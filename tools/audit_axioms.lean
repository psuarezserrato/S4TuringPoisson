import S4TuringPoisson
import Lean

open Lean Elab Command

namespace S4TuringPoisson.Audit

/--
Recursively eliminate unused (`decorative`) `have` and `let` bindings from an expression.
In Lean 4:
  - `have h : T := val; body` elaborates to `Expr.app (Expr.lam `h T body bi) val`.
  - `let h : T := val; body` elaborates to `Expr.letE `h T val body nonDep`.
If bound variable `#0` does not occur in `body` (`!body.hasLooseBVar 0`), `val` is a
decorative binding that does not contribute to the proof term and is stripped.
-/
partial def pruneDecorativeBindings (e : Expr) : Expr :=
  match e with
  | .app f a =>
    let f' := pruneDecorativeBindings f
    let a' := pruneDecorativeBindings a
    match f' with
    | .lam _ _ body _ =>
      if !body.hasLooseBVar 0 then
        pruneDecorativeBindings (body.lowerLooseBVars 1 1)
      else
        .app f' a'
    | _ => .app f' a'
  | .letE n t v b nonDep =>
    let b' := pruneDecorativeBindings b
    if !b'.hasLooseBVar 0 then
      pruneDecorativeBindings (b'.lowerLooseBVars 1 1)
    else
      .letE n (pruneDecorativeBindings t) (pruneDecorativeBindings v) b' nonDep
  | .lam n t b bi =>
    .lam n (pruneDecorativeBindings t) (pruneDecorativeBindings b) bi
  | .forallE n t b bi =>
    .forallE n (pruneDecorativeBindings t) (pruneDecorativeBindings b) bi
  | .mdata _ b =>
    pruneDecorativeBindings b
  | .proj s i b =>
    .proj s i (pruneDecorativeBindings b)
  | _ => e

/--
Extract constants referenced in the proof/value body of `ci` after stripping decorative
`have`/`let` bindings. For the root theorem we inspect only its proof value (not its statement
type) so that merely mentioning a constant in the type signature or a decorative `have` cannot
masquerade as genuine proof wiring.
-/
def getPrunedValueConstants (ci : ConstantInfo) (includeType : Bool := false) :
    Array Name := Id.run do
  let mut consts : Lean.NameSet := {}
  let addExpr (e : Expr) (s : Lean.NameSet) : Lean.NameSet :=
    let pruned := pruneDecorativeBindings e
    pruned.getUsedConstants.foldl (init := s) fun acc c => acc.insert c
  if includeType then
    consts := addExpr ci.type consts
  match ci with
  | .defnInfo v   => consts := addExpr v.value consts
  | .thmInfo v    => consts := addExpr v.value consts
  | .opaqueInfo v => consts := addExpr v.value consts
  | .inductInfo v =>
    for c in v.ctors do
      consts := consts.insert c
  | _ => pure ()
  return consts.toArray

/--
Compute the transitive closure of constants genuinely used in the proof term of `root`,
ignoring decorative `have`/`let` bindings at every step.
-/
def getProofTransitiveClosure (root : Name) (env : Environment) : Lean.NameSet := Id.run do
  let mut visited : Lean.NameSet := {}
  let some rootCi := env.find? root | return visited
  let mut queue : Array Name := getPrunedValueConstants rootCi (includeType := false)
  while !queue.isEmpty do
    let c := queue.back!
    queue := queue.pop
    if visited.contains c then
      continue
    visited := visited.insert c
    let some ci := env.find? c | continue
    let direct := getPrunedValueConstants ci (includeType := false)
    for d in direct do
      if !visited.contains d then
        queue := queue.push d
  return visited

/-- Resolve a candidate name in the environment (exact, `S4TuringPoisson.*`, `TuringRecursive.*`, or `Turing.*`). -/
def resolveDeclName (env : Environment) (raw : Name) : Option Name :=
  if env.contains raw then
    some raw
  else if env.contains (`S4TuringPoisson ++ raw) then
    some (`S4TuringPoisson ++ raw)
  else if env.contains (`S4TuringPoisson.Checks ++ raw) then
    some (`S4TuringPoisson.Checks ++ raw)
  else if env.contains (`TuringRecursive ++ raw) then
    some (`TuringRecursive ++ raw)
  else if env.contains (`Turing ++ raw) then
    some (`Turing ++ raw)
  else
    none

/-- Verify that every name in `required` is in the pruned proof closure of `root`. -/
def verifyWiring (env : Environment) (rootRaw : Name) (requiredRaw : List Name) :
    CommandElabM Unit := do
  let some root := resolveDeclName env rootRaw |
    throwError m!"[FAIL] #audit_wiring: root declaration '{rootRaw}' not found in environment"
  let some rootCi := env.find? root |
    throwError m!"[FAIL] #audit_wiring: root declaration '{root}' not found"

  let closure := getProofTransitiveClosure root env
  if closure.contains ``sorryAx then
    throwError m!"[FAIL] #audit_wiring: '{root}' depends on sorryAx"
  match rootCi with
  | .thmInfo v =>
    if v.value.getUsedConstants.contains ``sorryAx then
      throwError m!"[FAIL] #audit_wiring: '{root}' has direct sorryAx in proof term"
  | .defnInfo v =>
    if v.value.getUsedConstants.contains ``sorryAx then
      throwError m!"[FAIL] #audit_wiring: '{root}' has direct sorryAx in value term"
  | _ => pure ()

  let mut missing : List Name := []
  for reqRaw in requiredRaw do
    let req := (resolveDeclName env reqRaw).getD reqRaw
    if closure.contains req then
      logInfo m!"[PASS] #audit_wiring: '{root}' transitively uses '{req}'"
    else
      logError
        m!"[FAIL] #audit_wiring: '{root}' does NOT genuinely use '{req}' (missing or decorative)"
      missing := req :: missing

  if !missing.isEmpty then
    throwError
      m!"#audit_wiring FAILED for '{root}': missing {missing.length} required: {missing.reverse}"
  else
    logInfo
      m!"[OK] #audit_wiring PASSED for '{root}' ({requiredRaw.length} dependencies verified)"

/--
Syntax: `#audit_wiring root_theorem [req_lemma_1, req_lemma_2, ...]`
Verifies that all required lemmas occur in the pruned transitive closure of `root_theorem`.
Decorative `have` / `let` bindings are stripped before traversal and therefore fail the audit.
-/
syntax (name := auditWiringCmd) "#audit_wiring " ident " [" ident,* "]" : command

@[command_elab auditWiringCmd]
def elabAuditWiring : CommandElab := fun stx => do
  match stx with
  | `(#audit_wiring $rootId:ident [ $[$reqIds:ident],* ]) =>
    let env ← getEnv
    let rootName := rootId.getId
    let reqNames := reqIds.toList.map (·.getId)
    verifyWiring env rootName reqNames
  | _ => throwUnsupportedSyntax

/-- Check whether `a` is one of Lean's three standard foundational axioms. -/
def isAllowedAxiom (a : Name) : Bool :=
  a == ``propext || a == ``Classical.choice || a == ``Quot.sound

/-- Check whether `modName` is `S4TuringPoisson` or a submodule `S4TuringPoisson.*`. -/
def isS4TPModule (modName : Name) : Bool :=
  modName == `S4TuringPoisson || (`S4TuringPoisson).isPrefixOf modName

/-- Check whether `n` belongs to the `S4TuringPoisson.Audit` helper namespace. -/
def isAuditHelperName (n : Name) : Bool :=
  (`S4TuringPoisson.Audit).isPrefixOf n ||
    (n.toString.splitOn "S4TuringPoisson.Audit").length > 1 ||
    (n.toString.splitOn "auditWiringCmd").length > 1

/--
Check whether declaration `n` belongs to `S4TuringPoisson` (module or namespace) or the active file.
IMPORTANT (F-08 fix): Module membership is checked BEFORE `n.isInternal` so that unused `private`
declarations (`_private.S4TuringPoisson...`, for which `n.isInternal == true`) are audited too!
-/
def shouldAuditDecl (env : Environment) (n : Name) : Bool :=
  if isAuditHelperName n then
    false
  else
    match env.getModuleIdxFor? n with
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      if modName == `S4TuringPoisson.Audit || (`S4TuringPoisson.Audit).isPrefixOf modName then
        false
      else
        isS4TPModule modName
    | none =>
      if (`S4TuringPoisson).isPrefixOf n || (`_private).isPrefixOf n then
        true
      else
        !n.isInternal

/--
Audit all declarations in `S4TuringPoisson` modules (including unused `private` declarations)
using `Lean.collectAxioms`, reporting any axiom outside `{propext, Classical.choice, Quot.sound}`.
Also runs environment-driven `#audit_wiring` if `AUDIT_WIRING_ROOT` is set.
-/
elab "#audit_s4tp_axioms" : command => do
  let env ← getEnv
  let mut auditedCount : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]

  for (n, _) in env.constants.toList do
    if shouldAuditDecl env n then
      auditedCount := auditedCount + 1
      let axs ← liftCoreM (Lean.collectAxioms n)
      let bad := axs.filter (fun a => !isAllowedAxiom a)
      if !bad.isEmpty then
        violations := violations.push (n, bad)
        logError m!"[FAIL] Declaration '{n}' depends on disallowed axiom(s): {bad.toList}"

  logInfo m!"[Axiom Audit] Audited {auditedCount} declaration(s) in S4TuringPoisson / root."
  if !violations.isEmpty then
    throwError
      m!"Axiom audit FAILED: {violations.size} declaration(s) use non-standard axioms"
  else
    logInfo
      m!"[OK] All audited declarations use only \{propext, Classical.choice, Quot.sound}."

  -- Optional environment-driven wiring check (used by tools/collect_axioms.sh --wiring)
  let wiringRootOpt ← IO.getEnv "AUDIT_WIRING_ROOT"
  let wiringReqOpt ← IO.getEnv "AUDIT_WIRING_REQUIRED"
  if let some rootStr := wiringRootOpt then
    let cleanRoot := rootStr.trimAscii.toString
    if !cleanRoot.isEmpty then
      let reqStr := (wiringReqOpt.getD "").trimAscii.toString
      let reqNames :=
        (reqStr.splitOn ",").filterMap fun s =>
          let t := s.trimAscii.toString
          if t.isEmpty then none else some t.toName
      verifyWiring env cleanRoot.toName reqNames

/--
Module-scoped kernel axiom census command (`#phase_axiom_census`), ported from `SympTopAutoForm`.
Scans all constants (including `private` declarations before `isInternal`) in modules matching
`MODULE_PREFIX` (or `PHASE_MODULE`, default `S4TuringPoisson`).
-/
elab "#phase_axiom_census" : command => do
  let env ← getEnv
  let envVar ← IO.getEnv "MODULE_PREFIX"
  let envVar2 ← IO.getEnv "PHASE_MODULE"
  let rawPrefix := (envVar.orElse fun () => envVar2).getD "S4TuringPoisson"
  let prefixStr := rawPrefix.trimAscii.toString
  if prefixStr.isEmpty then
    throwError m!"Phase axiom census failed: module prefix cannot be empty"
  let targetPrefix := prefixStr.toName

  let mut clean : Nat := 0
  let mut dirty : Array Name := #[]
  let mut nonstandard : Array (Name × Name) := #[]

  for (n, _) in env.constants.toList do
    if isAuditHelperName n then
      continue
    let inScope :=
      match env.getModuleIdxFor? n with
      | some idx =>
        let modName := env.header.moduleNames[idx.toNat]!
        modName == targetPrefix || targetPrefix.isPrefixOf modName
      | none =>
        targetPrefix == `S4TuringPoisson && ((`S4TuringPoisson).isPrefixOf n || (`_private).isPrefixOf n || !n.isInternal)
    if !inScope then
      continue
    let axs ← liftCoreM (Lean.collectAxioms n)
    if axs.contains ``sorryAx then
      dirty := dirty.push n
    else
      clean := clean + 1
    for a in axs do
      unless a == ``sorryAx || isAllowedAxiom a do
        nonstandard := nonstandard.push (n, a)

  let total := clean + dirty.size
  logInfo m!"[Phase Axiom Census] scope={targetPrefix} total={total} clean={clean} sorryAx={dirty.size} nonstandard={nonstandard.size}"
  if total == 0 then
    throwError m!"Phase axiom census failed: 0 declarations found for prefix {targetPrefix}"
  if !nonstandard.isEmpty then
    throwError m!"Phase axiom census failed: {nonstandard.size} nonstandard axiom occurrences in {targetPrefix}"
  if !dirty.isEmpty then
    throwError m!"Phase axiom census failed: {dirty.size} declarations depend on sorryAx in {targetPrefix}"

#audit_s4tp_axioms

end S4TuringPoisson.Audit
