/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Translation.SourceScope
import Interop.Cryptol.Model.Reference.Types

/-! # Source-bundle validation and inspection -/

namespace Interop.Cryptol.Translation.SourceCLI

def errorJson (error : ImportError) : Lean.Json :=
  .mkObj [("status", .str "rejected"), ("location", Lean.toJson error.location),
    ("message", .str error.message)]

/-- Decode and validate a versioned source bundle, reporting the exact checking stage. -/
public def run (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  match args with
  | ["constraints", file] =>
      let text ← IO.FS.readFile file
      let result : Except ImportError Lean.Json := do
        let json ← (Lean.Json.parse text).mapError (⟨["json"], ·⟩)
        let cases ← json.getArr?.mapError (⟨["cases"], ·⟩)
        let checked ← cases.mapM fun entry => do
          let input ← (entry.getObjVal? "constraint").mapError (⟨["constraint"], ·⟩)
          let expression ← SourceBundle.decodeType input
          let result ← (do
            expression.checkKind 10000 [] .proposition
            expression.evaluate 10000 [] >>= Reference.TypeValue.proposition?).mapError
              (⟨["constraint"], ·⟩)
          pure (Lean.Json.mkObj [("constraint", input), ("result", Lean.toJson result)])
        return .arr checked
      match result with
      | .error error => out.putStrLn (errorJson error).compress; return 1
      | .ok result => out.putStrLn result.compress; return 0
  | ["inspect", file] =>
      let text ← IO.FS.readFile file
      let result : Except ImportError SourceBundle := do
        let json ← (Lean.Json.parse text).mapError (⟨["json"], ·⟩)
        let bundle ← SourceBundle.decode json
        let _ ← bundle.certifyScopes
        pure bundle
      match result with
      | .error error => out.putStrLn (errorJson error).compress; return 1
      | .ok bundle =>
          out.putStrLn (Lean.Json.mkObj [("status", .str "scoped"),
            ("roots", Lean.toJson (bundle.roots.map SourceRoot.text)),
            ("groups", Lean.toJson bundle.groups.length),
            ("declarations", Lean.toJson
              (bundle.groups.flatMap Reference.DeclGroup.declarations).length),
            ("modules", Lean.toJson bundle.modules.length)]).compress
          return 0
  | _ =>
      err.putStrLn "Usage: cryptol-interop source {inspect BUNDLE.json | constraints CASES.json}"
      return 1

end Interop.Cryptol.Translation.SourceCLI
