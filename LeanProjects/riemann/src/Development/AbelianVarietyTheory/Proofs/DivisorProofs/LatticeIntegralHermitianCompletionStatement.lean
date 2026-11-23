import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntegralHermitianCompletion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_integral_hermitian_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → (∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)) → ∀ L : Submodule K.O B.A, GlobalTheory.UnitLemma.IsLat K.O K.E L → (∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) → ∃ g ∈ UL n w, pullLat w B ψ g = L := by
  first | exact @GlobalTheory.KapOrb.SelfDualPull.exists_unitary_pullLat_eq | exact GlobalTheory.KapOrb.SelfDualPull.exists_unitary_pullLat_eq | (intros; apply GlobalTheory.KapOrb.SelfDualPull.exists_unitary_pullLat_eq <;> assumption)
