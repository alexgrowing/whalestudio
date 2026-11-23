import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.hypercohomologyPullback_biprod_inl_inr_bijective : ∀ (R : Type) [CommRing R] (K L I : Cx R) (n : ℤ), Function.Bijective fun x : CohomologyClass (K ⊞ L) I n => (cpull (biprod.inl : K ⟶ K ⊞ L) I n x, cpull (biprod.inr : L ⟶ K ⊞ L) I n x) := by
  first | exact @GlobalTheory.EtC.cpull_biprod_bijective | exact GlobalTheory.EtC.cpull_biprod_bijective | (intros; apply GlobalTheory.EtC.cpull_biprod_bijective <;> assumption)
