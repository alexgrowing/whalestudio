import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAlgebraMapInjectiveOfCharZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgEquivXAddC

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.SenLines

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

theorem isUnit_q_of_associated {m : ℕ} (h : Associated W.π₀₁ (X ^ m)) :
    IsUnit (algebraMap (LetA O n) W.EE (W.π₀ + ((PD.p : ℕ) : LetA O n))) := by
  obtain ⟨w, hw⟩ := h.symm
  have e : (W.π₀ : LetA O n) = letπ ^ m * fun _ => (w : O⟦X⟧) := funext fun _ => hw.symm
  have hu : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [e, map_mul, map_pow]
    exact (W.EE_π.pow _).mul (IsUnit.map _ (Pi.isUnit_iff.2 fun _ => w.isUnit))
  haveI := W.EE_complete
  have hJ := IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
    (Ideal.mem_span_singleton_self _)
  obtain ⟨u, hu⟩ := hu
  have h1 := (Ideal.mem_jacobson_bot.1 hJ (↑u⁻¹ : W.EE)).mul u.isUnit
  rw [map_add, map_natCast, ← hu]
  convert h1 using 1
  rw [add_mul, mul_assoc, Units.inv_mul]; ring

variable [Fact l.Prime] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (hp : PD.p = l)
  (χ : W.Gam →* ℤ_[l]ˣ) (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O))
include hp hχ

theorem exists_subst_invariants (ξ : O⟦X⟧) (hξ : Associated ξ (X ^ W.DelF.card))
    (h0 : constantCoeff ξ = 0) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ) :
    ∃ j : O⟦X⟧ →ₐ[O] O⟦X⟧, j X = ξ ∧ Function.Injective j ∧
      ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a := by
  classical
  have hγ := γ₀_eq W hp χ hχ
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  let Δ : Subgroup ℤ_[l]ˣ := (CommGroup.torsion W.Gam).map χ
  have hΔ : (Δ : Set ℤ_[l]ˣ) = ↑(W.DelF.image χ) := by
    ext x
    simp only [Δ, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, CommGroup.mem_torsion,
      Finset.coe_image, Finset.mem_coe, mem_DelF_iff]
  have hfa : ∀ p : ℤ_[l]ˣ → Prop, (∀ δ ∈ Δ, p δ) ↔ ∀ δ ∈ W.DelF, p (χ δ) := by
    intro p
    simp only [← SetLike.mem_coe, hΔ, Finset.coe_image, Set.forall_mem_image]
  haveI : Finite Δ := by
    change Finite (Δ : Set ℤ_[l]ˣ)
    rw [hΔ]; infer_instance
  have hcard : Nat.card Δ = W.DelF.card := by
    change Nat.card (Δ : Set ℤ_[l]ˣ) = _
    rw [hΔ, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hχi]
  have hs : HasSubst ξ := HasSubst.of_constantCoeff_zero' h0
  have hX : (substAlgHom hs : O⟦X⟧ →ₐ[O] O⟦X⟧) X = ξ := by rw [coe_substAlgHom, subst_X hs]
  obtain ⟨h2, h3⟩ := injective_and_range_eq_invariants Δ (substAlgHom hs : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (by rw [hX, hcard]; exact hξ)
    ((hfa _).2 fun δ hδ => by rw [← hγ, hX]; exact hinv δ hδ)
  refine ⟨_, hX, h2, fun a => ?_⟩
  rw [h3, hfa]; simp only [hγ]

theorem exists_qFrame_of_card [IsNoetherianRing O] (hl : l ≠ 2) (hc : W.DelF.card = l - 1)
    (σ : O⟦X⟧ ≃ₐ[O] O⟦X⟧) (hσ : σ X = X + C (l : O)) (g : W.Gam)
    (hg : (l : ℤ_[l]) ∣ (χ g : ℤ_[l]) - 1) : ∃ J, QFrame W g J := by
  have h2l := (Fact.out : l.Prime).two_le
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨p2, p3, w, hw⟩ := π₀₁_spec W hp χ hχ hl hc
  have hq := (φ₀_eq W hp).2
  have hγ := γ₀_eq W hp χ hχ
  have hX0 : (X : O⟦X⟧) ∣ W.π₀₁ := (dvd_pow_self _ (by omega)).trans p2.symm.dvd
  have h0 := X_dvd_iff.1 hX0
  obtain ⟨j, hj, hji, hjr⟩ := exists_subst_invariants W hp χ hχ _ p2 h0 p3
  let J : O⟦X⟧ →ₐ[O] O⟦X⟧ := j.comp σ
  have hJ : ∀ c, J c = j (σ c) := fun _ => rfl
  have hσ' : σ X = X + (l : O⟦X⟧) := by rw [hσ, map_natCast]
  have hJX : J X = W.π₀₁ + (l : O⟦X⟧) := by rw [hJ, hσ', map_add, hj, map_natCast]
  have hσl : σ (X - (l : O⟦X⟧)) = X := by rw [map_sub, hσ', map_natCast]; ring
  have hr : ∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a := fun a => by
    rw [← hjr]
    exact ⟨fun ⟨b, hb⟩ => ⟨σ b, hb⟩, fun ⟨b, hb⟩ => ⟨σ.symm b, by rw [hJ, σ.apply_symm_apply, hb]⟩⟩
  have hk : ∀ c, constantCoeff (J c) = 0 → X - (l : O⟦X⟧) ∣ c := fun c h => by
    rw [hJ, constantCoeff_algHom j (hj ▸ hX0)] at h
    rw [← map_dvd_iff σ, hσl, X_dvd_iff, h]
  have hc0 : constantCoeff (J X) = (l : O) := by rw [hJX, map_add, h0, map_natCast, zero_add]
  have hwu : IsUnit w := by
    have h1 := congrArg constantCoeff hw
    rw [← hJX, hc0, map_mul, show constantCoeff (lvl l O 0) = (l : O) by simp [lvl]] at h1
    rw [isUnit_iff_constantCoeff, ← mul_left_cancel₀ hl0 ((mul_one _).trans h1)]
    exact isUnit_one
  have hass : Associated (J X) (lvl l O 0) := by
    rw [hJX, hw]; exact associated_mul_unit_left _ _ hwu
  have hne : J X ≠ 0 := fun h => hl0 (by rw [← hc0, h, map_zero])
  obtain ⟨y, hy⟩ : J X * X ∣ W.γ₀ g (J X) - J X := by
    have h1 := dvd_act_sub (O := O) 1 (χ g) 1 (by rwa [pow_one]) (J X)
    have h2 := mul_lvl (l := l) (O := O) 0
    rw [pow_zero, pow_one, add_sub_cancel_left, zero_add] at h2
    rw [act_one, ← hγ, ← h2, mul_comm] at h1
    exact (mul_dvd_mul_right hass.dvd _).trans h1
  have hinv := (hr (J X)).1 ⟨X, rfl⟩
  obtain ⟨y', hy'⟩ := (hr (X * y)).2 fun δ hδ => by
    apply mul_left_cancel₀ hne
    have h1 := congrArg (W.γ₀ δ) hy
    rw [mul_assoc, map_mul, map_sub, hinv δ hδ, hγ δ, hγ g, act_comm, ← hγ δ, hinv δ hδ,
      ← hγ g, hy, mul_assoc] at h1
    exact h1.symm
  obtain ⟨z, hz⟩ := hk y' (by rw [hy']; simp)
  have hs : IsUnit (1 + y') := by
    rw [← MulEquiv.isUnit_map σ, hz, map_add, map_mul, hσl, isUnit_iff_constantCoeff]
    simp
  refine ⟨J, hji.comp σ.injective, hr, by rw [hp, hJX], by rw [hp]; exact hk,
    ⟨hs.unit, ?_, ?_⟩, hq ▸ hass, isUnit_q_of_associated W p2⟩
  · rw [hs.unit_spec, map_add, map_one, hy']
    linear_combination hy
  · rw [hp, hs.unit_spec, add_sub_cancel_left]
    exact ⟨z, hz⟩

end Generic

theorem exists_qFrame : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (g : W.Gam), CaseA K LL → ((W.χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) = 1 + (l : ↥(OL LL)) → IsUnit (W.DelF.card : ↥(OL LL)) ∧ ∃ J, QFrame W g J := by
  intro l _ P K LL n W g ⟨hK, hl, h⟩ hg
  have p1 : Module.finrank ↥(K0 K) ↥K.1 = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hK x.2⟩, rfl⟩⟩
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W hl h.2.2.1
  rw [p1, mul_one] at hc
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL W
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨σ, hσ⟩ := GlobalTheory.NB.LT.exists_algEquiv_X_add_C (IsLocalRing.maximalIdeal ↥(OL LL))
    (l : ↥(OL LL)) hu
  refine ⟨?_, exists_qFrame_of_card W (P.PD_p K) χ hχ hl hc σ hσ g ?_⟩
  · have h1 := IsLocalRing.isUnit_or_isUnit_one_sub_self (l : ↥(OL LL))
    rw [hc, Nat.cast_sub (Fact.out : l.Prime).one_le, Nat.cast_one, ← IsUnit.neg_iff, neg_sub]
    exact h1.resolve_left hu
  · have h1 : (χ g : ℤ_[l]) = 1 + l := GlobalTheory.algebraMap_padicInt_OL_injective LL (by
      rw [hχ, hg, map_add, map_one, map_natCast])
    rw [h1, add_sub_cancel_left]

end GlobalTheory.SenLines
