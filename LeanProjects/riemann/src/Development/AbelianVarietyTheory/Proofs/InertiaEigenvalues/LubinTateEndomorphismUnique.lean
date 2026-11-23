import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK

namespace GlobalTheory.PZ

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem resCard_eq_card_residueField :
    resCard K = Nat.card (IsLocalRing.ResidueField ↥(OL K)) :=
  (GlobalTheory.AinfK.main l K).1.symm

theorem one_lt_resCard [Finite (IsLocalRing.ResidueField ↥(OL K))] : 1 < resCard K := by
  rw [resCard_eq_card_residueField]
  exact Finite.one_lt_card

theorem isLubinTateSeries_ltSeries [Finite (IsLocalRing.ResidueField ↥(OL K))] (π : ↥(OL K)) :
    IsLubinTateSeries π (ltSeries K π) := by
  have hq := one_lt_resCard K
  refine ⟨?_, ?_, fun n => ?_⟩
  · simp [ltSeries, show resCard K ≠ 0 by omega]
  · simp [ltSeries, PowerSeries.coeff_X_pow, show 1 ≠ resCard K by omega]
  · rw [← resCard_eq_card_residueField, ltSeries, add_sub_cancel_right, PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _

theorem subst_ltSeries (π : ↥(OL K)) {φ : PowerSeries ↥(OL K)} (h : PowerSeries.constantCoeff φ = 0) :
    PowerSeries.subst φ (ltSeries K π) = PowerSeries.C π * φ + φ ^ resCard K := by
  have hs : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' h
  rw [ltSeries, PowerSeries.subst_add hs, PowerSeries.subst_pow hs, PowerSeries.subst_mul hs,
    PowerSeries.subst_X hs, PowerSeries.subst_C]
  rfl

theorem isLTEndo_iff_eq_lubinTateHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l)
    [Finite (IsLocalRing.ResidueField ↥(OL K))] (π : ↥(OL K)) (hπ : Irreducible π),
    ∃ hf : IsLubinTateSeries π (ltSeries K π),
      ∀ (a : ↥(OL K)) (φ : PowerSeries ↥(OL K)),
        IsLTEndo K π a φ ↔ φ = (lubinTateHom hπ hf hf a).toPowerSeries := by
  intro l _ K _ π hπ
  refine ⟨isLubinTateSeries_ltSeries K π, fun a φ => ⟨?_, ?_⟩⟩
  · rintro ⟨h0, h1, h2⟩
    exact eq_lubinTateHom_toPowerSeries hπ _ _ a h0 h1 (by rw [subst_ltSeries K π h0, h2])
  · rintro rfl
    have h0 := (lubinTateHom hπ (isLubinTateSeries_ltSeries K π) (isLubinTateSeries_ltSeries K π) a).constantCoeff_eq_zero
    refine ⟨h0, coeff_one_lubinTateHom hπ _ _ a, ?_⟩
    rw [← subst_ltSeries K π h0]
    exact subst_lubinTateHom hπ _ _ a

end GlobalTheory.PZ

end
