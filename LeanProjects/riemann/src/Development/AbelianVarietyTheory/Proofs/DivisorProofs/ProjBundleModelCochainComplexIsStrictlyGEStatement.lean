import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleModelCochainComplexIsStrictlyGE
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projBundleModelCochainComplex_isStrictlyGE : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), I.IsStrictlyGE 0 → (Jcx R q N I).IsStrictlyGE 0 := by
  first | (exact @GlobalTheory.EtC.Jcx_isStrictlyGE) | (exact GlobalTheory.EtC.Jcx_isStrictlyGE) | (intros; apply GlobalTheory.EtC.Jcx_isStrictlyGE  <;> assumption)
