import Mathlib

namespace GlobalTheory.FormalCalc

open MvPowerSeries Finsupp

section Chain

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem subst_zero' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    subst a (0 : MvPowerSeries σ R) = 0 := by
  rw [← substAlgHom_apply ha, map_zero]

theorem subst_one' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    subst a (1 : MvPowerSeries σ R) = 1 := by
  rw [← substAlgHom_apply ha, map_one]

theorem subst_neg' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (-f) = -subst a f := by
  rw [← substAlgHom_apply ha, map_neg, substAlgHom_apply]

theorem subst_sum' {κ : Type*} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (s : Finset κ)
    (f : κ → MvPowerSeries σ R) : subst a (∑ k ∈ s, f k) = ∑ k ∈ s, subst a (f k) := by
  rw [← substAlgHom_apply ha, map_sum]
  simp only [substAlgHom_apply]

theorem subst_C' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (r : R) :
    subst a (C r : MvPowerSeries σ R) = C (algebraMap R S r) := by
  rw [← substAlgHom_apply ha, show (C r : MvPowerSeries σ R) = algebraMap R _ r from rfl,
    AlgHom.commutes, MvPowerSeries.algebraMap_apply]

open MvPowerSeries.WithPiTopology in

theorem continuous_pderiv [TopologicalSpace R] [DiscreteTopology R] (i : σ) :
    Continuous (pderiv R i : MvPowerSeries σ R → MvPowerSeries σ R) := by
  refine continuous_iff_continuousAt.mpr fun f => ?_
  rw [ContinuousAt, tendsto_iff_coeff_tendsto]
  intro d
  simp only [coeff_pderiv]
  exact ((continuous_coeff R (d + single i 1)).mul continuous_const).continuousAt

theorem pderiv_comm (i j : σ) (f : MvPowerSeries σ R) :
    pderiv R i (pderiv R j f) = pderiv R j (pderiv R i f) := by
  classical
  by_cases h : i = j
  · rw [h]
  ext d
  simp only [coeff_pderiv, Finsupp.add_apply, single_eq_of_ne h, single_eq_of_ne (Ne.symm h),
    add_zero]
  rw [add_right_comm]
  ring

open MvPowerSeries.WithPiTopology in

theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (f : MvPowerSeries σ R) (j : τ) :
    pderiv S j (subst a f) = ∑ i, subst a (pderiv R i f) * pderiv S j (a i) := by
  classical
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  have hc := continuous_subst (R := R) ha
  refine congr_fun (DenseRange.equalizer (denseRange_toMvPowerSeries (σ := σ) (R := R))
    (g := fun f => pderiv S j (subst a f))
    (h := fun f => ∑ i, subst a (pderiv R i f) * pderiv S j (a i))
    ((continuous_pderiv j).comp hc)
    (continuous_finset_sum _ fun i _ => (hc.comp (continuous_pderiv i)).mul continuous_const)
    ?_) f
  funext p
  simp only [Function.comp_apply]
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp [MvPolynomial.coe_C, pderiv_C, subst_C' ha, subst_zero' ha]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, subst_add ha, map_add, hp, hq, add_mul,
      Finset.sum_add_distrib]
  | mul_X p n hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, Derivation.leibniz, hp,
      smul_eq_mul, subst_add ha, subst_X ha, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single n]
      · simp [subst_one' ha]
      · intro b _ hb
        simp [pderiv_X_of_ne (Ne.symm hb), subst_zero' ha]
      · simp
    · exact Finset.sum_congr rfl fun i _ => by ring

theorem pderiv_powerSeries_subst {a : MvPowerSeries τ S} (ha : PowerSeries.HasSubst a)
    (f : PowerSeries R) (j : τ) :
    pderiv S j (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative R f) * pderiv S j a := by
  have h := pderiv_subst (σ := Unit) (a := fun _ => a) ha.const f j
  simpa [PowerSeries.subst, PowerSeries.derivative] using h

theorem constantCoeff_subst_of_zero {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = algebraMap R S (constantCoeff f) := by
  have h : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by simp
  have h' : constantCoeff (subst a (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero ha ha0 (by simp)
  conv_lhs => rw [h, subst_add ha, map_add, h', subst_C' ha]
  simp

theorem pderiv_map {T : Type*} [CommRing T] (φ : R →+* T) (i : σ) (f : MvPowerSeries σ R) :
    pderiv T i (map φ f) = map φ (pderiv R i f) := by
  ext d
  simp [coeff_pderiv]

end Chain

section Poincare

variable {σ ι A : Type*} [CommRing A]

theorem natCast_mul_coeff_of_pderiv_eq {f a : MvPowerSeries σ A} {s : σ}
    (h : pderiv A s f = a) {α : σ →₀ ℕ} (hα : α s ≠ 0) :
    (α s : A) * coeff α f = coeff (α - single s 1) a := by
  have hle : single s 1 ≤ α := single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hα)
  rw [← h, coeff_pderiv, tsub_add_cancel_of_le hle, coe_tsub, Pi.sub_apply, single_eq_same,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hα), Nat.cast_one, sub_add_cancel, mul_comm]

theorem ext_of_pderiv_of_coeff [IsAddTorsionFree A] (e : ι → σ) {f g : MvPowerSeries σ A}
    (hD : ∀ i, pderiv A (e i) f = pderiv A (e i) g)
    (h0 : ∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = coeff α g) : f = g := by
  ext α
  by_cases h : ∀ i, α (e i) = 0
  · exact h0 α h
  push Not at h
  obtain ⟨i, hi⟩ := h
  have h1 := natCast_mul_coeff_of_pderiv_eq (hD i) hi
  have h2 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv A (e i) g = _) hi
  rw [← h2, ← nsmul_eq_mul, ← nsmul_eq_mul] at h1
  exact (smul_right_inj hi).mp h1

variable [Algebra ℚ A]

theorem existsUnique_primitive_param {e : ι → σ} (he : Function.Injective e)
    (a : ι → MvPowerSeries σ A) (ha : ∀ i j, pderiv A (e i) (a j) = pderiv A (e j) (a i)) :
    ∃! f : MvPowerSeries σ A, (∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = 0) ∧
      ∀ i, pderiv A (e i) f = a i := by
  classical
  haveI : IsAddTorsionFree A := .of_module_rat A
  have key : ∀ (α : σ →₀ ℕ) (i j : ι), α (e i) ≠ 0 → α (e j) ≠ 0 →
      (α (e j) : A) * coeff (α - single (e i) 1) (a i) =
        (α (e i) : A) * coeff (α - single (e j) 1) (a j) := by
    intro α i j hi hj
    by_cases hij : i = j
    · rw [hij]
    have hne : e i ≠ e j := fun h => hij (he h)
    have e1 : (α - single (e i) 1 : σ →₀ ℕ) (e j) = α (e j) := by
      simp [single_eq_of_ne (Ne.symm hne)]
    have e2 : (α - single (e j) 1 : σ →₀ ℕ) (e i) = α (e i) := by
      simp [single_eq_of_ne hne]
    have h1 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv A (e j) (a i) = _) (e1 ▸ hj)
    have h2 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv A (e i) (a j) = _) (e2 ▸ hi)
    rw [e1] at h1
    rw [e2] at h2
    rw [h1, h2, ha, tsub_right_comm]
  let f : MvPowerSeries σ A := fun α =>
    if h : ∃ i, α (e i) ≠ 0 then
      ((α (e h.choose) : ℚ)⁻¹) • coeff (α - single (e h.choose) 1) (a h.choose) else 0
  have hf : ∀ α, coeff α f = if h : ∃ i, α (e i) ≠ 0 then
      ((α (e h.choose) : ℚ)⁻¹) • coeff (α - single (e h.choose) 1) (a h.choose) else 0 :=
    fun _ => rfl
  have hf0 : ∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = 0 := by
    intro α h
    rw [hf, dif_neg]
    push Not
    exact h
  have hf1 : ∀ i, pderiv A (e i) f = a i := by
    intro i
    ext n
    have hi : (n + single (e i) 1 : σ →₀ ℕ) (e i) ≠ 0 := by simp
    have hex : ∃ j, (n + single (e i) 1 : σ →₀ ℕ) (e j) ≠ 0 := ⟨i, hi⟩
    have hk := key _ hex.choose i hex.choose_spec hi
    have hq : (((n + single (e i) 1 : σ →₀ ℕ) (e hex.choose) : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hex.choose_spec
    rw [add_tsub_cancel_right] at hk
    rw [coeff_pderiv, hf, dif_pos hex, smul_mul_assoc, mul_comm]
    have : ((n (e i) : A) + 1) = (((n + single (e i) 1 : σ →₀ ℕ) (e i) : ℕ) : A) := by simp
    rw [this, hk, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hq,
      one_smul]
  refine ⟨f, ⟨hf0, hf1⟩, fun g hg => ?_⟩
  exact ext_of_pderiv_of_coeff e (fun i => by rw [hg.2, hf1]) fun α h => by rw [hg.1 α h, hf0 α h]

end Poincare

end GlobalTheory.FormalCalc
