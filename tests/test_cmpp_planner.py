#!/usr/bin/env python3
"""Unit tests for CMPP Milestone C0 (`tools/cmpp_planner.py`)."""

from fractions import Fraction
import math
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.cmpp_planner import (
    AxisRect,
    build_abstract_sliding_relocation_pipeline,
    build_r_flip_right_shift,
    build_random_bijective_shift_dom3,
    build_relocation_pipeline,
    cantor_base,
    cantor_disk_embed_exact,
    cantor_disk_embed_float,
    cantor_prefix_code,
    compute_block_affine_map,
    evaluate_pipeline_on_random_cantor_points,
    rect_gap,
    run_full_c0_suite,
    verify_lemma_g0,
    verify_r5_poisson_hamiltonian_normalization,
)


class TestCMPPPlanner(unittest.TestCase):
    """Comprehensive unit tests for C0.1--C0.4."""

    def test_c0_1_sign_pinning_and_cantor_prefix(self) -> None:
        """Verifies sign conventions of GeneralizedShift.eval vs cantorDiskEmbed and A_w."""
        self.assertEqual(cantor_base(2), 3)
        self.assertEqual(cantor_base(3), 5)
        self.assertEqual(cantor_base(6), 11)
        self.assertEqual(cantor_base(10), 19)
        self.assertEqual(cantor_prefix_code(3, [1, 0]), 3 * (2 * 1) + 2 * 0)

        # Check explicit F = +1, F = 0, F = -1 scaling directions on N = 3 (B = 5)
        rule = build_random_bijective_shift_dom3(3, seed=103)
        b = rule.base
        seen_f = set()
        for w in rule.all_triples():
            bmap = compute_block_affine_map(rule, w)
            f = bmap.f_shift
            seen_f.add(f)
            if f == 1:
                # F = +1 shifts sequence left: negHalf (x) gains a digit -> contracts by B^{-1};
                # nonnegHalf (y) loses a digit -> expands by B.
                self.assertEqual(bmap.lam_x, Fraction(1, b))
                self.assertEqual(bmap.lam_y, Fraction(b, 1))
                self.assertAlmostEqual(bmap.mu_stretch, math.log(b), places=14)
                self.assertAlmostEqual(bmap.target_rect.width, 1.0 / (4.0 * b * b), places=15)
                self.assertAlmostEqual(bmap.target_rect.height, 1.0 / (4.0 * b), places=15)
            elif f == -1:
                # F = -1 shifts sequence right: negHalf (x) loses a digit -> expands by B;
                # nonnegHalf (y) gains a digit -> contracts by B^{-1}.
                self.assertEqual(bmap.lam_x, Fraction(b, 1))
                self.assertEqual(bmap.lam_y, Fraction(1, b))
                self.assertAlmostEqual(bmap.mu_stretch, -math.log(b), places=14)
                self.assertAlmostEqual(bmap.target_rect.width, 0.25, places=15)
                self.assertAlmostEqual(bmap.target_rect.height, 1.0 / (4.0 * (b ** 3)), places=15)
            else:
                self.assertEqual(f, 0)
                self.assertEqual(bmap.lam_x, Fraction(1, 1))
                self.assertEqual(bmap.lam_y, Fraction(1, 1))
                self.assertAlmostEqual(bmap.mu_stretch, 0.0, places=15)
                self.assertAlmostEqual(bmap.target_rect.width, 1.0 / (4.0 * b), places=15)
                self.assertAlmostEqual(bmap.target_rect.height, 1.0 / (4.0 * b * b), places=15)

            # Check exact rational action on a test sequence in cyl(w)
            seq = {k: (abs(k) + 1) % 3 for k in range(-10, 11)}
            seq[-1], seq[0], seq[1] = w
            x0, y0 = cantor_disk_embed_exact(3, seq, depth=14)
            seq1 = rule.eval_seq(seq, window_radius=14)
            x1, y1 = cantor_disk_embed_exact(3, seq1, depth=14)
            self.assertEqual(bmap.apply_exact(x0, y0), (x1, y1))

        self.assertEqual(seen_f, {-1, 0, 1})

    def test_c0_2_lemma_g0_disjointness_all_sizes(self) -> None:
        """Verifies G0 disjointness and positive gaps for N=2,3,5,10 and R_flipRight_shift."""
        for n_val in (2, 3, 5, 10):
            rule = build_random_bijective_shift_dom3(n_val, seed=100 + n_val)
            g0 = verify_lemma_g0(rule, num_samples=150)
            self.assertTrue(g0.disjoint_sources)
            self.assertTrue(g0.disjoint_targets)
            self.assertTrue(g0.exact_rational_passed)
            self.assertLess(g0.max_affine_embed_error, 1e-12)
            self.assertAlmostEqual(g0.min_source_gap, g0.theoretical_source_gap, places=12)
            self.assertGreaterEqual(g0.min_target_gap, g0.theoretical_target_gap - 1e-14)

        r_flip = build_r_flip_right_shift()
        g0_flip = verify_lemma_g0(r_flip, num_samples=200)
        self.assertTrue(g0_flip.disjoint_sources)
        self.assertTrue(g0_flip.disjoint_targets)
        self.assertTrue(g0_flip.exact_rational_passed)
        self.assertLess(g0_flip.max_affine_embed_error, 1e-12)

    def test_c0_3_relocation_pipeline_zero_collisions_and_10k_points(self) -> None:
        """Verifies 0 collisions, max_support_norm < r_0 < 1, and < 1e-12 error on 10,000+ points."""
        total_points = 0
        for n_val, n_pts in ((2, 4000), (3, 4000), (5, 1500)):
            rule = build_random_bijective_shift_dom3(n_val, seed=100 + n_val)
            plan = build_relocation_pipeline(rule)
            self.assertEqual(plan.num_Collisions, 0)
            self.assertGreater(plan.min_tube_clearance, 0.0)
            self.assertGreater(plan.min_stretch_clearance, 0.04)
            self.assertLess(plan.max_trajectory_radius_in_wb, plan.workbench_r_in)
            self.assertLess(plan.max_support_norm, 0.75)
            self.assertLess(plan.max_support_norm, plan.r_0)
            self.assertLess(plan.r_0, 1.0)

            max_err, tested = evaluate_pipeline_on_random_cantor_points(
                rule, plan, num_points=n_pts, seed=500 + n_val
            )
            self.assertLess(max_err, 1e-12)
            total_points += tested

        # Test R_flipRight_shift (N = 6, B = 11, 216 blocks)
        r_flip = build_r_flip_right_shift()
        plan_flip = build_relocation_pipeline(r_flip)
        self.assertEqual(plan_flip.num_Collisions, 0)
        self.assertGreater(plan_flip.min_tube_clearance, 0.0)
        self.assertLess(plan_flip.max_support_norm, 0.75)
        err_flip, tested_flip = evaluate_pipeline_on_random_cantor_points(
            r_flip, plan_flip, num_points=1000, seed=999
        )
        self.assertLess(err_flip, 1e-12)
        total_points += tested_flip
        self.assertGreaterEqual(total_points, 10000)

    def test_c0_3_abstract_sliding_relocation_pipeline(self) -> None:
        """Verifies the general 1D-Sliding-Lemma Relocation Pipeline (Milestone A3)."""
        for n_val in (2, 3):
            rule = build_random_bijective_shift_dom3(n_val, seed=100 + n_val)
            bmaps = [compute_block_affine_map(rule, w) for w in rule.all_triples()]
            abs_plan = build_abstract_sliding_relocation_pipeline(
                source_rects=[m.source_rect for m in bmaps],
                target_rects=[m.target_rect for m in bmaps],
                f_shifts=[m.f_shift for m in bmaps],
                base=rule.base,
            )
            self.assertEqual(abs_plan.num_Collisions, 0)
            self.assertGreater(abs_plan.min_tube_clearance, 0.0)
            self.assertLess(abs_plan.max_support_norm, 0.75)
            err, _ = evaluate_pipeline_on_random_cantor_points(
                rule, abs_plan, num_points=500, seed=1700 + n_val
            )
            self.assertLess(err, 1e-12)

    def test_c0_4_r5_poisson_hamiltonian_normalization(self) -> None:
        """Verifies the 4D Jacobian-Poisson Hamiltonian vector field & time-1 flow identity."""
        r5 = verify_r5_poisson_hamiltonian_normalization()
        self.assertTrue(r5.annihilates_grad_rho_on_slope)
        self.assertTrue(r5.sign_is_plus_one)
        self.assertLess(r5.max_base_component_error, 1e-15)
        self.assertLess(r5.max_fiber_vector_field_error, 1e-12)
        self.assertGreater(r5.max_sign_flipped_error, 0.5)
        self.assertLess(r5.max_rk4_flow_time_one_error, 1e-12)


if __name__ == "__main__":
    unittest.main()
