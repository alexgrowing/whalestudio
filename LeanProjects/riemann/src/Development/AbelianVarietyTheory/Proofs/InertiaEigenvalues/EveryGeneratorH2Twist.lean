import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCyclotomicCharacterLocalGaloisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiInjectiveQuotientH2Statement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2QuotientFiniteCardStatement

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.FunctorialityH2

theorem bijective_phi_quot_pow : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ, Function.Bijective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  intro p _ K O _ _ _ _ _ G _ _ hT hK hO i ε hε z hz k
  haveI : ContinuousMul G := ⟨by
    have h : (fun q : G × G => q.1 * q.2) = fun q => i.symm (i q.1 * i q.2) := by
      funext q; simp
    rw [h]
    exact i.symm.continuous.comp
      ((i.continuous.comp continuous_fst).mul (i.continuous.comp continuous_snd))⟩
  have hinj := GlobalTheory.T.phi_injective_quotient_H2 hO (GlobalTheory.T.continuous_cyclotomic_character_localGalois hO i hε) z hz k
  obtain ⟨_, hcard⟩ := GlobalTheory.T.finite_H2_twist_quotient_pow_and_card_le hT hK hO i hε k
  exact hinj.bijective_of_nat_card_le hcard

end GlobalTheory.FunctorialityH2
