import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardResidueFieldOfRingEquivAdicCompletion
import Mathlib
open ValuativeRel NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_residueField_of_ringEquiv_adicCompletion : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → Nat.card 𝓀[k] = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.LocalResidue.card_residue_of_ringEquiv | exact GlobalTheory.LocalResidue.card_residue_of_ringEquiv | (intros; apply GlobalTheory.LocalResidue.card_residue_of_ringEquiv <;> assumption)
