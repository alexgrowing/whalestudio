import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.HLepolyTr

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def RestOIso : Prop :=
  ∀ (p n' : ℕ) (R₁ R₂ : RS p n') (φW : R₁.W ≃+* R₂.W),
    ∃ φO : R₁.O ≃+* R₂.O, (∀ x, φO (R₁.jO x) = R₂.jO (φW x)) ∧ φO R₁.w = R₂.w

theorem restRSIso_of (hW : WittIdent) (hO : RestOIso) : RestRSIso := by
  intro p n' R₁ R₂
  have s₁ := R₁.std.1
  have s₂ := R₂.std.1
  haveI : Fact (Nat.Prime p) := ⟨s₁.prime⟩
  haveI := s₁.frac_alt
  haveI := s₂.frac_alt
  haveI := s₁.frac_O
  haveI := s₂.frac_O
  obtain ⟨φ₁, h₁⟩ := hW p n' R₁.W R₁.Qq R₁.O R₁.Kf R₁.ι R₁.σ R₁.jO R₁.w s₁
  obtain ⟨φ₂, h₂⟩ := hW p n' R₂.W R₂.Qq R₂.O R₂.Kf R₂.ι R₂.σ R₂.jO R₂.w s₂
  obtain ⟨φO, hj, hw⟩ := hO p n' R₁ R₂ (φ₁.symm.trans φ₂)
  let φQ : R₁.Qq ≃+* R₂.Qq := IsFractionRing.ringEquivOfRingEquiv (φ₁.symm.trans φ₂)
  let φK : R₁.Kf ≃+* R₂.Kf := IsFractionRing.ringEquivOfRingEquiv φO
  have hWQ : ∀ x, φQ (algebraMap R₁.W R₁.Qq x) = algebraMap R₂.W R₂.Qq ((φ₁.symm.trans φ₂) x) :=
    fun x => IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have hOK : ∀ x, φK (algebraMap R₁.O R₁.Kf x) = algebraMap R₂.O R₂.Kf (φO x) :=
    fun x => IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have hσ : ∀ x, φQ (R₁.σ x) = R₂.σ (φQ x) := by
    have key : (φQ : R₁.Qq →+* R₂.Qq).comp (R₁.σ : R₁.Qq →+* R₁.Qq) =
        (R₂.σ : R₂.Qq →+* R₂.Qq).comp (φQ : R₁.Qq →+* R₂.Qq) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors R₁.W)
      ext u
      obtain ⟨v, rfl⟩ := φ₁.surjective u
      simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      rw [h₁ v, hWQ, hWQ]
      simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
      rw [h₂ v]
    exact fun x => RingHom.congr_fun key x
  have hι : ∀ x, φK (R₁.ι x) = R₂.ι (φQ x) := by
    have key : (φK : R₁.Kf →+* R₂.Kf).comp R₁.ι = R₂.ι.comp (φQ : R₁.Qq →+* R₂.Qq) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors R₁.W)
      ext u
      simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      rw [s₁.ι_comp, hOK, hj, hWQ, s₂.ι_comp]
    exact fun x => RingHom.congr_fun key x
  exact ⟨⟨φ₁.symm.trans φ₂, φQ, φO, φK, hWQ, hOK, hι, hσ, hj, hw⟩⟩

theorem lpRingIndep_of'' (hW : WittIdent) (hO : RestOIso) : LPRingIndep := lpRingIndep_of' (restRSIso_of hW hO)

end Formalism.MainNotions.flipOneThree.Pf

end
