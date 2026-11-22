import tempfile
import unittest
from pathlib import Path
import sys

TOOLS_DIR = Path(__file__).resolve().parent.parent / "tools"
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import ledger
import ollama_lean4_client


class TestOllamaClient(unittest.TestCase):
    def test_config_guardrails_and_model_selection(self):
        cfg = ollama_lean4_client.load_config()
        self.assertEqual(cfg.get("title"), "S4TuringPoissonOllamaGemmaConfig")
        self.assertEqual(cfg.get("service", {}).get("keep_alive"), 0)
        self.assertEqual(cfg.get("hardware_guardrails", {}).get("locked_num_ctx"), 4096)
        self.assertEqual(cfg.get("hardware_guardrails", {}).get("max_prompt_chars"), 4000)

        profiles = cfg.get("parameter_profiles", {})
        self.assertIn("prove", profiles)
        for name, prof in profiles.items():
            self.assertEqual(prof.get("num_ctx"), 4096, f"Profile {name} num_ctx must be 4096")

        chosen, _ = ollama_lean4_client.select_model(
            ["gemma2:9b", "gemma4:12B", "gemma-lean4:latest"], preferred=None
        )
        self.assertEqual(chosen, "gemma4:12B")
        chosen_ci, _ = ollama_lean4_client.select_model(["gemma4:12b"], preferred="gemma4:12B")
        self.assertEqual(chosen_ci, "gemma4:12b")

    def test_extract_lean_code_and_build_messages(self):
        self.assertEqual(
            ollama_lean4_client.extract_lean_code("text\n```lean4\ntheorem x : True := trivial\n```\nend"),
            "theorem x : True := trivial",
        )
        self.assertEqual(
            ollama_lean4_client.extract_lean_code("```lean\nexact rfl\n```"),
            "exact rfl",
        )
        premises = [
            {
                "name": "S4TuringPoisson.shiftSeq_zero",
                "file": "S4TuringPoisson/Dynamics/GeneralizedShift.lean",
                "signature": "theorem shiftSeq_zero {A : Type*} (s : ℤ → A) : shiftSeq 0 s = s",
            }
        ]
        msgs = ollama_lean4_client.build_messages(
            "tactic",
            "prove shiftSeq_zero",
            goal="⊢ shiftSeq 0 s = s",
            error="unsolved goals",
            premises=premises,
        )
        self.assertEqual(len(msgs), 2)
        self.assertEqual(msgs[0]["role"], "system")
        self.assertIn("⊢ shiftSeq 0 s = s", msgs[1]["content"])
        self.assertIn("S4TuringPoisson.shiftSeq_zero", msgs[1]["content"])

    def test_dry_run_query(self):
        msgs = ollama_lean4_client.build_messages("tactic", "prove", goal="⊢ True")
        res = ollama_lean4_client.query_ollama_chat(
            ollama_lean4_client.DEFAULT_OLLAMA_HOST,
            "gemma4:12B",
            "tactic",
            msgs,
            think=False,
            dry_run=True,
            record_usage=False,
        )
        self.assertEqual(res["status"], "mock")
        self.assertIn("trivial", res["lean_code"])


if __name__ == "__main__":
    unittest.main()
