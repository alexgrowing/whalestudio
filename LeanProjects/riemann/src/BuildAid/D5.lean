import Lean.LibrarySuggestions.Basic
import Lean.Elab.Command

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "UpperTheory"
