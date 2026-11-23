import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LayersOfExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfConstantCoeffZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial

noncomputable section

namespace GlobalTheory.NL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL PowerSeries

section Generic

variable {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] O]
    [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] {v : AddValuation L (WithTop ℚ)}
    {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR}
    [Algebra Qp L] [TopologicalSpace L] {n : ℕ}

def levOne (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
  (W.lev i ζ).comp (Pi.constAlgHom O (ZMod n) O⟦X⟧)

omit [CharZero L] [Algebra ℚ L] in

theorem lev_eq_levOne (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) (f : LetA O n) :
    W.lev i ζ f = levOne W i ζ (f i) := by
  have h := W.lev_letter i ζ (f - Pi.constAlgHom O (ZMod n) O⟦X⟧ (f i)) (sub_self (f i))
  rw [map_sub, sub_eq_zero] at h
  exact h

theorem levOne_X (W : LocWach PD L O v n) (i : ZMod n) {ζ : L} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    levOne W i ζ X = C ζ * exp L - 1 := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π i ζ h
  have hE : E = exp L := Ser.ode_unique 1 (by rw [map_one, one_mul]; exact h1)
    (by rw [map_one, one_mul]; exact derivative_exp L) (by rw [h0, constantCoeff_exp])
  rw [← hE, ← h2, add_sub_cancel_left]
  rfl

theorem levLaws_of_evLaw [IsDomain O] (hl0 : (l : O) ≠ 0) (hlu : ¬ IsUnit (l : O)) (W : LocWach PD L O v n)
    (hp : PD.p = l) (c : W.Gam → ℤ_[l]) (hc : ∀ g, algebraMap ℤ_[l] O (c g) = (W.χΓ g : O))
    (hv : ∀ (c : ℤ_[l]) (j a : ℕ), (j : WithTop ℚ) ≤ v (algebraMap ℤ_[l] L c - (a : L)) →
      (l : ℤ_[l]) ^ j ∣ c - a) (H : Ser.EvLaw l (O := O) v inferInstance) : LevLaws W := by
  have hc' : ∀ g, algebraMap O L (W.χΓ g : O) = algebraMap ℤ_[l] L (c g) :=
    fun g => by rw [← hc, ← IsScalarTower.algebraMap_apply]
  have hpr : PD.p.Prime := hp ▸ (Fact.out : l.Prime)
  have hφX : W.φ₀ X = (1 + X) ^ l - 1 := by rw [W.φ₀_X, W.q₀_def, hp]
  have hφ : W.φ₀ = GlobalTheory.Fon.phi0 l O :=
    GlobalTheory.Cyc.algHom_ext_of_constantCoeff_zero _ _ (by rw [hφX, GlobalTheory.Fon.cyclotomicFrobeniusPowerSeries_X]) (by rw [hφX]; simp)
  have hγ : ∀ g, W.γ₀ g = GlobalTheory.Fon.gam O (c g) := fun g =>
    GlobalTheory.Cyc.algHom_ext_of_constantCoeff_zero _ _
      (GlobalTheory.Cyc.eq_of_commute_pow l hl0 hlu W.φ₀ _ _ hφX (W.γ₀_comm g _) (by rw [hφ]; exact GlobalTheory.Fon.cyclotomicFrobenius_comm_gammaAction _ _ _)
        (W.γ₀_X g).1 (GlobalTheory.Fon.constantCoeff_gam_X _ _)
        (by rw [(W.γ₀_X g).2, GlobalTheory.Fon.coeff_one_gam_X, hc])) (W.γ₀_X g).1
  constructor
  · rintro g i ζ _ j a h hj rfl f
    rw [hc'] at hj ⊢
    rw [lev_eq_levOne, lev_eq_levOne]
    change levOne W i ζ (W.γ₀ g (f i)) = _
    rw [hγ]
    exact Ser.ev_gam H (hp ▸ h.pow_eq_one) _ (hv _ j a hj) (levOne_X W i ⟨j, h⟩)
      (levOne_X W i (root_pow hpr ⟨j, h⟩ a)) (f i)
  · rintro i ζ ⟨j, h⟩ f
    rw [lev_eq_levOne, lev_eq_levOne]
    change levOne W i ζ (W.φ₀ (f (i - 1))) = _
    have := Ser.ev_gam H (hp ▸ h.pow_eq_one) (l : ℤ_[l]) (a := l) (by simp) (levOne_X W i ⟨j, h⟩)
      (levOne_X W (i - 1) (root_pow hpr ⟨j, h⟩ l)) (f (i - 1))
    rw [GlobalTheory.Fon.gam_l, map_natCast] at this
    rw [hφ, hp]
    exact this

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem levLaws : LevLaws (H.W K s LL h) := by
  obtain ⟨_, -, h0, hu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨c, hc⟩ := Ser.exists_padic_char (GamL H h)
  refine levLaws_of_evLaw h0 hu _ (P.PD_p K) (fun g => (c g : ℤ_[l])) hc (Ser.dvd_of_le_v P) ?_
  convert Ser.evLaw_integers P LL using 1
  exact Algebra.algebra_ext _ _ fun r => PowerSeries.algebraMap_apply

theorem ioLaws_tie : IoLaws (F.E K s LL h).tie :=
  ⟨GlobalTheory.HWL.Back.ioE_φ (O := ↥(OL LL)) Subtype.val_injective _,
    GlobalTheory.HWL.Back.ioE_γ (O := ↥(OL LL)) Subtype.val_injective _⟩

theorem one_crys : IsCrys (P.PD K) (H.W K s LL h).one.ρ :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  GlobalTheory.TrivCrys.isCrys_lat_of_trivial _ (H.W K s LL h).one_triv

theorem laws_of_cmp (C : LocCmpT l P AI H F) : Laws H F h :=
  ⟨⟨(C.C K s LL h).tie.lev_Γ, (C.C K s LL h).tie.lev_φ⟩, ioLaws_tie H F h, one_crys H h⟩

end Concrete

theorem laws : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL), Laws H F h :=
  fun H F _ _ _ h => ⟨levLaws H h, ioLaws_tie H F h, one_crys H h⟩

end GlobalTheory.NL
