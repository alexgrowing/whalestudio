import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionComparison
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictScalars_resolution_comparison : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S), ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)), (∀ (U : Scheme.{0}) (a : Sec F U), ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) ∧ ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n) := by
  first
  | exact @GlobalTheory.EtC.restrRes_comparison
  | exact GlobalTheory.EtC.restrRes_comparison
  | (intros; apply GlobalTheory.EtC.restrRes_comparison <;> assumption)
