import Lean
import Geometry

def isUserDecl (n : Lean.Name) : Bool :=
  let s := n.toString
  let containsDenylist := [
    "_simp_",
    ".match_",
    "._aux_",
    ".extract",
    "._eq_",
    ".eq_",
    "._uniq"
  ]
  let endsWithDenylist := [
    ".inj",
    ".inj_iff",
    ".sizeOf_spec",
    ".rec",
    ".recOn",
    ".casesOn",
    ".brecOn",
    ".noConfusion",
    ".noConfusionType",
    ".proof_1",
    ".proof_2",
    ".proof_3"
  ]
  let kindDenylist := [
    "ParserDescr",
    "TrailingParserDescr",
    "Parser",
    "Macro",
    "Unexpander"
  ]
  !containsDenylist.any (fun sub => s.contains sub) &&
  !endsWithDenylist.any (fun suffix => s.endsWith suffix) &&
  !kindDenylist.any (fun k => s.contains k)

def getProofDeps (env : Lean.Environment) (info : Lean.ConstantInfo) : List String :=
  let expr := match info with
    | .thmInfo  t => some t.value
    | .defnInfo d => some d.value
    | _ => none
  match expr with
  | none => []
  | some e =>
    e.getUsedConstants.toList
      |>.map Lean.Name.toString
      |>.filter (fun (s : String) => s.startsWith "Geometry")

open Lean in
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Geometry }] {}

  let decls := env.constants.toList.filter (fun (n, _) =>
    n.toString.startsWith "Geometry" && isUserDecl n)

  let mut entries : Array String := #[]
  for (name, info) in decls do
    let kind := match info with
      | .axiomInfo  _ => "axiom"
      | .defnInfo   _ => "def"
      | .thmInfo    _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | _             => "other"
    let docstring ← findDocString? env name
    let doc := (docstring.getD "").replace "\"" "\\\"" |>.replace "\n" " "
    let typeStr := toString info.type |>.replace "\"" "\\\"" |>.replace "\n" " "
    let deps := getProofDeps env info
    let depsJson := "[" ++ (deps.map (fun d => s!"\"{d}\"") |> String.intercalate ",") ++ "]"
    entries := entries.push
      s!"\{\"name\":\"{name}\",\"kind\":\"{kind}\",\"doc\":\"{doc}\",\"type\":\"{typeStr}\",\"deps\":{depsJson}}"

  let json := "[\n" ++ (String.intercalate ",\n" entries.toList) ++ "\n]"
  IO.FS.writeFile "blueprint/decls.json" json
  IO.eprintln s!"Wrote {entries.size} declarations to blueprint/decls.json"
