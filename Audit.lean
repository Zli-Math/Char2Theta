import Char2Theta
import Lean.Util.CollectAxioms

/-!
# 项目声明的公理依赖审计

本文件导入总入口，按所属的 `Char2Theta` 项目模块遍历声明，包括私有声明及生成在其他
命名空间中的辅助声明，检查其传递公理依赖。仅允许 Lean/mathlib 通常使用的 `propext`、`Classical.choice`、
`Quot.sound`；发现其他公理（包括 `sorryAx`）时直接报错。

运行 `lake env lean Audit.lean`，或运行 `scripts/check.sh` 同时构建和审计。
该检查针对已形式化声明；数学语义、原文覆盖范围与尚未形式化的内容仍需独立审查，
详见 `README.md` 与 `REVIEW.md`。
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in env.constants do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    if (`Char2Theta).isPrefixOf env.allImportedModuleNames[moduleIdx]! then
      count := count + 1
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
  logInfo m!"Audited {count} declarations from Char2Theta modules (including private and generated declarations): only propext, Classical.choice, Quot.sound allowed."
