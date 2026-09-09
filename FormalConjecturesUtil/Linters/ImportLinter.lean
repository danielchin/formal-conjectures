/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Tactic.Linter.Header

/-!
# The Import Linter

This file implements a linter that enforces import conventions in `FormalConjectures`:

1. Problem files must import `FormalConjecturesUtil`.
2. Direct imports of `Mathlib`, `Mathlib.*`, and the aggregate
   `FormalConjecturesForMathlib` are disallowed.
3. Specific `FormalConjecturesForMathlib.*` modules may be imported directly.
-/

public meta section

open Lean Elab Command Linter

register_option linter.style.imports : Bool := {
  defValue := false
  descr := "enable the import style linter"
}

namespace ImportLinter

/-- Checks an array of import identifiers against Formal Conjectures import rules. -/
def checkImports (importIds : Array Syntax) (isFormalConjecturesModule : Bool := true)
    (firstCmdStx : Syntax := .missing) : CommandElabM Unit := do
  for imp in importIds do
    let modName := imp.getId
    if modName == `Mathlib || modName.getRoot == `Mathlib then
      Linter.logLintIf linter.style.imports imp
        m!"Direct imports from 'Mathlib' (such as '{modName}') are disallowed in 'FormalConjectures'. \
           Use 'import FormalConjecturesUtil' instead."
    if modName == `FormalConjecturesForMathlib then
      Linter.logLintIf linter.style.imports imp
        m!"Direct imports from 'FormalConjecturesForMathlib' (such as '{modName}') are disallowed in 'FormalConjectures'. \
           Use 'import FormalConjecturesUtil' instead."

  if isFormalConjecturesModule then
    let hasUtil := importIds.any fun id ↦ id.getId == `FormalConjecturesUtil
    unless hasUtil do
      let targetStx := importIds[0]? |>.getD firstCmdStx
      Linter.logLintIf linter.style.imports targetStx
        "Files in 'FormalConjectures' must import 'FormalConjecturesUtil'."

/-- Files whose header has already been checked by this linter. -/
private initialize checkedFiles : IO.Ref (Std.HashSet String) ← IO.mkRef {}

/-- Enforce the required utility import and reject direct imports of Mathlib
or the shared-library aggregate. Specific shared modules are allowed.
-/
def importLinter : Linter where run := withSetOptionIn fun stx ↦ do
  if stx.getKind == ``Lean.Parser.Command.moduleDoc then return
  unless getLinterValue linter.style.imports (← getLinterOptions) do return
  if (← get).messages.hasErrors then return
  let fileName ← getFileName
  if fileName.endsWith "FormalConjectures/All.lean" || fileName.endsWith "All.lean" then return
  let mainModule ← getMainModule
  unless mainModule.getRoot == `FormalConjectures do return
  let checked ← checkedFiles.get
  if checked.contains fileName then return
  checkedFiles.modify (·.insert fileName)

  let fm ← getFileMap
  let (headerStx, _) ← Parser.parseHeader { inputString := fm.source, fileName := fileName, fileMap := fm }
  let importIds := Mathlib.Linter.getImportIds headerStx
  checkImports importIds (isFormalConjecturesModule := true) stx

initialize addLinter importLinter

/-- A command to test import validation on a simulated header string. -/
elab "#check_imports " headerStr:str : command => do
  let s := headerStr.getString
  let fm : FileMap := { source := s, positions := #[0] }
  let (headerStx, _) ← Parser.parseHeader { inputString := s, fileName := "test.lean", fileMap := fm }
  let importIds := Mathlib.Linter.getImportIds headerStx
  checkImports importIds (isFormalConjecturesModule := true) headerStr

end ImportLinter
