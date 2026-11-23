import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionHolomorphic
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm

noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.Model GlobalTheory.Sieg.Hol PowerSeries

namespace GlobalTheory.Sieg.Gal

local notation "𝕢" => Function.Periodic.qParam

variable {σ : ℂ ≃+* ℂ} {h : ℝ} {f f' g g' : ℍ → ℂ}

theorem q_ne (h : ℝ) (τ : ℍ) : 𝕢 h τ ≠ 0 := Function.Periodic.qParam_ne_zero _

theorem of_pow_mul {φ : PowerSeries ℂ} (n : ℕ) (hf : HasQExpansion h (fun τ => 𝕢 h τ ^ n * f τ) (X ^ n * φ)) :
    HasQExpansion h f φ := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    apply ih
    apply HasQExpansion.of_qParam_mul
    rw [← mul_assoc, ← pow_succ']
    exact hf.congr fun τ => by ring

theorem exists_inv (hh : 0 < h) {φ : PowerSeries ℂ} (hf : HasQExpansion h f φ) (h0 : coeff 0 φ ≠ 0)
    (hz : ∀ τ, f τ ≠ 0) : ∃ ψ, HasQExpansion h (fun τ => (f τ)⁻¹) ψ ∧ φ * ψ = 1 := by
  obtain ⟨F, hF, hF0, hfF⟩ := hf.exists_analytic hh
  have hne : ∀ z ∈ Metric.ball (0 : ℂ) 1, F z ≠ 0 := by
    intro z hz1
    rcases eq_or_ne z 0 with rfl | hz0
    · rwa [hF0]
    · have hq : ‖z‖ < 1 := by simpa using hz1
      have h1 := Function.Periodic.im_invQParam_pos_of_norm_lt_one hh hq hz0
      have := hz ⟨_, h1⟩
      rw [hfF] at this
      simpa only [Function.Periodic.qParam_right_inv hh.ne' hz0] using this
  have hd : DifferentiableOn ℂ (fun z => (F z)⁻¹) (Metric.ball 0 1) := hF.differentiableOn.inv hne
  have key : HasQExpansion h (fun τ => (f τ)⁻¹)
      (PowerSeries.mk fun n => ((n.factorial : ℂ))⁻¹ * iteratedDeriv n (fun z => (F z)⁻¹) 0) := by
    intro τ
    have := Complex.hasSum_taylorSeries_on_ball hd (z := 𝕢 h τ)
      (by simpa using Function.Periodic.norm_qParam_lt_one hh τ.im_pos)
    simp only [hfF]
    convert! this using 1
    funext n
    simp only [coeff_mk, sub_zero, smul_eq_mul]; ring
  refine ⟨_, key, ?_⟩
  refine HasQExpansion.unique hh (hf.mul key) ?_
  have := HasQExpansion.const h 1
  rw [map_one] at this
  exact this.congr fun τ => mul_inv_cancel₀ (hz τ)

def Cj (σ : ℂ ≃+* ℂ) (h : ℝ) (f f' : ℍ → ℂ) : Prop :=
  ∃ φ, HasQExpansion h f φ ∧ HasQExpansion h f' (PowerSeries.map (σ : ℂ →+* ℂ) φ)

theorem Cj.congr (hf : Cj σ h f f') (e : ∀ τ, g τ = f τ) (e' : ∀ τ, g' τ = f' τ) : Cj σ h g g' := by
  obtain ⟨φ, a, b⟩ := hf
  exact ⟨φ, a.congr e, b.congr e'⟩

theorem Cj.mul (hf : Cj σ h f f') (hg : Cj σ h g g') : Cj σ h (fun τ => f τ * g τ) fun τ => f' τ * g' τ := by
  obtain ⟨φ, a, b⟩ := hf
  obtain ⟨ψ, c, d⟩ := hg
  exact ⟨_, a.mul c, by rw [map_mul]; exact b.mul d⟩

theorem Cj.sub (hf : Cj σ h f f') (hg : Cj σ h g g') : Cj σ h (fun τ => f τ - g τ) fun τ => f' τ - g' τ := by
  obtain ⟨φ, a, b⟩ := hf
  obtain ⟨ψ, c, d⟩ := hg
  exact ⟨_, a.sub c, by rw [map_sub]; exact b.sub d⟩

theorem Cj.const (w : ℂ) : Cj σ h (fun _ => w) fun _ => σ w :=
  ⟨_, HasQExpansion.const h w, by rw [map_C]; exact HasQExpansion.const h _⟩

theorem Cj.qpow (n : ℕ) : Cj σ h (fun τ => 𝕢 h τ ^ n) fun τ => 𝕢 h τ ^ n :=
  ⟨_, (HasQExpansion.qParam h).pow n, by rw [map_pow, map_X]; exact (HasQExpansion.qParam h).pow n⟩

def Rel (σ : ℂ ≃+* ℂ) (h : ℝ) (f f' : ℍ → ℂ) : Prop :=
  ∃ k : ℕ, Cj σ h (fun τ => 𝕢 h τ ^ k * f τ) fun τ => 𝕢 h τ ^ k * f' τ

theorem Cj.rel (hf : Cj σ h f f') : Rel σ h f f' := ⟨0, hf.congr (by simp) (by simp)⟩

theorem Rel.congr (hf : Rel σ h f f') (e : ∀ τ, g τ = f τ) (e' : ∀ τ, g' τ = f' τ) : Rel σ h g g' := by
  obtain ⟨k, a⟩ := hf
  exact ⟨k, a.congr (fun τ => by rw [e]) fun τ => by rw [e']⟩

theorem Rel.mul (hf : Rel σ h f f') (hg : Rel σ h g g') : Rel σ h (fun τ => f τ * g τ) fun τ => f' τ * g' τ := by
  obtain ⟨k, a⟩ := hf
  obtain ⟨l, b⟩ := hg
  exact ⟨k + l, (a.mul b).congr (fun τ => by ring) fun τ => by ring⟩

theorem Rel.sub (hf : Rel σ h f f') (hg : Rel σ h g g') : Rel σ h (fun τ => f τ - g τ) fun τ => f' τ - g' τ := by
  obtain ⟨k, a⟩ := hf
  obtain ⟨l, b⟩ := hg
  exact ⟨k + l, (((Cj.qpow l).mul a).sub ((Cj.qpow k).mul b)).congr (fun τ => by ring) fun τ => by ring⟩

theorem Rel.const (w : ℂ) : Rel σ h (fun _ => w) fun _ => σ w := (Cj.const w).rel

theorem Rel.one : Rel σ h (fun _ => 1) fun _ => 1 := (Rel.const 1).congr (fun _ => rfl) fun _ => (map_one σ).symm

theorem Rel.pow (hf : Rel σ h f f') (n : ℕ) : Rel σ h (fun τ => f τ ^ n) fun τ => f' τ ^ n := by
  induction n with
  | zero => simpa using Rel.one
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem Rel.inv (hh : 0 < h) (hf : Rel σ h f f') (hz : ∀ τ, f τ ≠ 0) (hz' : ∀ τ, f' τ ≠ 0) :
    Rel σ h (fun τ => (f τ)⁻¹) fun τ => (f' τ)⁻¹ := by
  obtain ⟨k, φ, a, b⟩ := hf
  have hφ : φ ≠ 0 := by
    rintro rfl
    have := a UpperHalfPlane.I
    simp only [map_zero, zero_mul] at this
    exact mul_ne_zero (pow_ne_zero k (q_ne h _)) (hz _) (this.unique hasSum_zero)
  obtain ⟨n, u, hu, rfl⟩ : ∃ (n : ℕ) (u : PowerSeries ℂ), coeff 0 u ≠ 0 ∧ φ = X ^ n * u := by
    refine ⟨φ.order.toNat, divXPowOrder φ, ?_, X_pow_order_mul_divXPowOrder.symm⟩
    rw [coeff_zero_eq_constantCoeff_apply, Ne, constantCoeff_divXPowOrder_eq_zero_iff]
    exact hφ
  rw [map_mul, map_pow, map_X] at b
  have a1 : HasQExpansion h (fun τ => (𝕢 h τ ^ n)⁻¹ * (𝕢 h τ ^ k * f τ)) u :=
    of_pow_mul n (a.congr fun τ => mul_inv_cancel_left₀ (pow_ne_zero _ (q_ne h τ)) _)
  have b1 : HasQExpansion h (fun τ => (𝕢 h τ ^ n)⁻¹ * (𝕢 h τ ^ k * f' τ)) (PowerSeries.map (σ : ℂ →+* ℂ) u) :=
    of_pow_mul n (b.congr fun τ => mul_inv_cancel_left₀ (pow_ne_zero _ (q_ne h τ)) _)
  obtain ⟨ψ, a2, e⟩ := exists_inv hh a1 hu fun τ =>
    mul_ne_zero (inv_ne_zero (pow_ne_zero _ (q_ne h τ))) (mul_ne_zero (pow_ne_zero _ (q_ne h τ)) (hz τ))
  obtain ⟨ψ', b2, e'⟩ := exists_inv hh b1 (by simpa using hu) fun τ =>
    mul_ne_zero (inv_ne_zero (pow_ne_zero _ (q_ne h τ))) (mul_ne_zero (pow_ne_zero _ (q_ne h τ)) (hz' τ))
  have e2 : ψ' = PowerSeries.map (σ : ℂ →+* ℂ) ψ := by
    have e3 := congrArg (PowerSeries.map (σ : ℂ →+* ℂ)) e
    rw [map_mul, map_one] at e3
    calc ψ' = ψ' * (PowerSeries.map (σ : ℂ →+* ℂ) u * PowerSeries.map (σ : ℂ →+* ℂ) ψ) := by rw [e3, mul_one]
      _ = (PowerSeries.map (σ : ℂ →+* ℂ) u * ψ') * PowerSeries.map (σ : ℂ →+* ℂ) ψ := by ring
      _ = _ := by rw [e', one_mul]
  subst e2
  refine ⟨n, ((Cj.qpow k).mul ⟨ψ, a2, b2⟩).congr (fun τ => ?_) fun τ => ?_⟩
  · have := q_ne h τ; have := hz τ; field_simp
  · have := q_ne h τ; have := hz' τ; field_simp

theorem Rel.zpow (hh : 0 < h) (hf : Rel σ h f f') (hz : ∀ τ, f τ ≠ 0) (hz' : ∀ τ, f' τ ≠ 0) (j : ℤ) :
    Rel σ h (fun τ => f τ ^ j) fun τ => f' τ ^ j := by
  obtain ⟨n, rfl | rfl⟩ := j.eq_nat_or_neg
  · simpa using hf.pow n
  · simpa using (hf.pow n).inv hh (fun τ => pow_ne_zero _ (hz τ)) fun τ => pow_ne_zero _ (hz' τ)

theorem Rel.qzpow (hh : 0 < h) (j : ℤ) : Rel σ h (fun τ => 𝕢 h τ ^ j) fun τ => 𝕢 h τ ^ j :=
  Rel.zpow hh (by simpa using (Cj.qpow (σ := σ) (h := h) 1).rel) (q_ne h) (q_ne h) j

theorem finite_fiber {e : ℕ → ℕ} (he : ∀ m, m ≤ e m) (n : ℕ) {s : Finset ℕ} (hs : ∑ m ∈ s, e m = n) :
    s ∈ (Finset.range (n + 1)).powerset := by
  rw [Finset.mem_powerset]
  intro m hm
  have := Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) hm
  have := he m
  rw [Finset.mem_range]; omega

theorem hasQ_tprod (hh : 0 < h) {e : ℕ → ℕ} (he : ∀ m, m ≤ e m) (w : ℂ) :
    HasQExpansion h (fun τ => ∏' m, (1 + 𝕢 h τ ^ e m * w))
      (PowerSeries.mk fun n => ∑ s ∈ (Finset.range (n + 1)).powerset with ∑ m ∈ s, e m = n, w ^ s.card) := by
  intro τ
  set Q := 𝕢 h τ with hQ
  have hq : ‖Q‖ < 1 := Function.Periodic.norm_qParam_lt_one hh τ.im_pos
  have hs : Summable fun m => ‖Q ^ e m * w‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right ‖w‖)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (norm_nonneg _) hq.le (he m)) (norm_nonneg _)
  have h1 := summable_finsetProd_of_summable_norm hs
  have h2 := h1.hasSum
  rw [← tprod_one_add h1] at h2
  have h3 := HasSum.tsum_fiberwise h2 (fun s => ∑ m ∈ s, e m)
  convert! h3 using 1
  funext n
  have e1 : (fun s : Finset ℕ => ∑ m ∈ s, e m) ⁻¹' {n} =
      (((Finset.range (n + 1)).powerset.filter fun s => ∑ m ∈ s, e m = n : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun hs => ⟨finite_fiber he n hs, hs⟩, fun hs => hs.2⟩
  rw [e1, Finset.tsum_subtype' _ (fun s : Finset ℕ => ∏ i ∈ s, Q ^ e i * w), coeff_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, (Finset.mem_filter.mp hs).2, Finset.prod_const, mul_comm]

theorem cj_tprod (hh : 0 < h) {e : ℕ → ℕ} (he : ∀ m, m ≤ e m) (w : ℂ) :
    Cj σ h (fun τ => ∏' m, (1 + 𝕢 h τ ^ e m * w)) fun τ => ∏' m, (1 + 𝕢 h τ ^ e m * σ w) := by
  refine ⟨_, hasQ_tprod hh he w, ?_⟩
  convert hasQ_tprod hh he (σ w) using 1
  ext n
  simp [map_sum]

theorem geomProd_shift {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : geomProd q u = (1 - q * u) * geomProd q (q * u) := by
  have e : (fun m : ℕ => 1 - q ^ (m + 1 + 1) * u) = fun m : ℕ => 1 - q ^ (m + 1) * (q * u) := by
    funext m; ring
  have hs : Summable fun m : ℕ => ‖-(q ^ (m + 1) * (q * u))‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_succ]
    exact ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _).mul_right _
  have h : Multipliable fun m : ℕ => (fun m : ℕ => 1 - q ^ (m + 1) * u) (m + 1) := by
    show Multipliable fun m : ℕ => 1 - q ^ (m + 1 + 1) * u
    rw [e]; simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs
  have := tprod_eq_zero_mul' (f := fun m : ℕ => 1 - q ^ (m + 1) * u) h
  simp only [e, zero_add, pow_one] at this
  exact this

theorem rel_geomProd (hh : 0 < h) {M : ℕ} (hM : 0 < M) (w : ℂ) (j : ℤ) :
    Rel σ h (fun τ => geomProd (𝕢 h τ ^ M) (𝕢 h τ ^ j * w)) fun τ => geomProd (𝕢 h τ ^ M) (𝕢 h τ ^ j * σ w) := by
  have key : ∀ (K : ℕ) (j : ℤ), 0 ≤ j + K →
      Rel σ h (fun τ => geomProd (𝕢 h τ ^ M) (𝕢 h τ ^ j * w)) fun τ => geomProd (𝕢 h τ ^ M) (𝕢 h τ ^ j * σ w) := by
    intro K
    induction K with
    | zero =>
      intro j hj
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ j by simpa using hj)
      have := (cj_tprod (σ := σ) hh (e := fun m => M * (m + 1) + n) (fun m => by nlinarith) (-w)).rel
      refine this.congr (fun τ => ?_) fun τ => ?_
      · unfold geomProd; congr 1; funext m; rw [zpow_natCast]; ring
      · unfold geomProd; congr 1; funext m; rw [zpow_natCast, map_neg]; ring
    | succ K ih =>
      intro j hj
      have h1 := ih (j + M) (by push_cast at hj; omega)
      have h2 := (Rel.one.sub ((Rel.qzpow (σ := σ) hh (j + M)).mul (Rel.const w))).mul h1
      have hq : ∀ τ : ℍ, ‖𝕢 h τ ^ M‖ < 1 := fun τ => by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) (Function.Periodic.norm_qParam_lt_one hh τ.im_pos) hM.ne'
      have e : ∀ (τ : ℍ) (v : ℂ), 𝕢 h τ ^ M * (𝕢 h τ ^ j * v) = 𝕢 h τ ^ (j + M) * v := fun τ v => by
        rw [zpow_add₀ (q_ne h τ), zpow_natCast]; ring
      refine h2.congr (fun τ => ?_) fun τ => ?_
      · rw [geomProd_shift (hq τ), e]
      · rw [geomProd_shift (hq τ), e]
  exact key j.natAbs j (by omega)

theorem ee_eq_q {M : ℕ} (hM : 0 < M) (τ : ℍ) : ee τ = 𝕢 (M : ℝ) τ ^ M := by
  have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold ee Function.Periodic.qParam
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp

theorem ee_pt_eq {M : ℕ} (hM : 0 < M) (a b : ℕ) (τ : ℍ) :
    ee (pt ![(a : ℚ) / M, (b : ℚ) / M] τ) = 𝕢 (M : ℝ) τ ^ a * ee ((b : ℂ) / M) := by
  have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold ee Function.Periodic.qParam pt
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast; field_simp

theorem rel_sg {c M a b b' : ℕ} (hM : 0 < M) (hσ : σ (ee ((b : ℂ) / M)) = ee ((b' : ℂ) / M))
    (h1 : admitted c ![(a : ℚ) / M, (b : ℚ) / M]) (h2 : admitted c ![(a : ℚ) / M, (b' : ℚ) / M]) :
    Rel σ M (sg c ![(a : ℚ) / M, (b : ℚ) / M]) (sg c ![(a : ℚ) / M, (b' : ℚ) / M]) := by
  have hh : (0 : ℝ) < M := by exact_mod_cast hM
  set x : Fin 2 → ℚ := ![(a : ℚ) / M, (b : ℚ) / M] with hx
  set x' : Fin 2 → ℚ := ![(a : ℚ) / M, (b' : ℚ) / M] with hx'
  set z := ee ((b : ℂ) / M) with hz
  have e : ∀ τ, ee (pt x τ) = 𝕢 (M : ℝ) τ ^ a * z := ee_pt_eq hM a b
  have e' : ∀ τ, ee (pt x' τ) = 𝕢 (M : ℝ) τ ^ a * σ z := fun τ => by rw [hσ]; exact ee_pt_eq hM a b' τ
  have ht : Rel σ M (fun τ => ee (pt x τ)) fun τ => ee (pt x' τ) :=
    (((Cj.qpow a).mul (Cj.const z)).rel).congr e e'
  have hq : Rel σ M (fun τ : ℍ => ee τ) fun τ => ee τ := (Cj.qpow M).rel.congr (ee_eq_q hM) (ee_eq_q hM)
  have hG : ∀ i : ℤ, Rel σ M (fun τ : ℍ => geomProd (ee τ) (ee (pt x τ) ^ i))
      fun τ => geomProd (ee τ) (ee (pt x' τ) ^ i) := fun i =>
    (rel_geomProd hh hM (z ^ i) (a * i)).congr
      (fun τ => by rw [e, ee_eq_q hM, mul_zpow, zpow_mul, zpow_natCast])
      (fun τ => by rw [e', ee_eq_q hM, mul_zpow, zpow_mul, zpow_natCast, map_zpow₀])
  have hA := hG 1
  have hB := hG (-1)
  have hC := hG c
  have hD := hG (-c)
  simp only [zpow_one, zpow_neg, zpow_natCast] at hA hB hC hD
  have hneg : Rel σ M (fun τ => -ee (pt x τ)) fun τ => -ee (pt x' τ) :=
    ((Rel.const 0).sub ht).congr (fun τ => by simp) fun τ => by simp
  have hfront := (((hq.pow ((c ^ 2 - 1) / 12)).mul (hneg.zpow hh (fun τ => neg_ne_zero.2 (ee_ne_zero _))
    (fun τ => neg_ne_zero.2 (ee_ne_zero _)) (((c : ℤ) - (c : ℤ) ^ 2) / 2))).mul ((Rel.one.sub ht).pow (c ^ 2))).mul
    ((Rel.one.sub (ht.pow c)).inv hh (fun τ => (multipliable_and_sg_ne_zero h1 τ).2.1)
      fun τ => (multipliable_and_sg_ne_zero h2 τ).2.1)
  have hback := ((hA.pow (c ^ 2)).mul (hB.pow (c ^ 2))).mul
    ((hC.mul hD).inv hh (fun τ => (tprod_cthFac h1 τ).1) fun τ => (tprod_cthFac h2 τ).1)
  refine (hfront.mul hback).congr (fun τ => ?_) fun τ => ?_
  · unfold sg cth; rw [(tprod_cthFac h1 τ).2, div_eq_mul_inv, div_eq_mul_inv]
  · unfold sg cth; rw [(tprod_cthFac h2 τ).2, div_eq_mul_inv, div_eq_mul_inv]

end GlobalTheory.Sieg.Gal

namespace GlobalTheory.Sieg

open Gal

theorem sg_coeff_galois : ∀ (c M a b d : ℕ) (σ : ℂ ≃+* ℂ), 0 < M → a < M → σ (ee (1 / (M : ℂ))) = ee ((d : ℂ) / M) → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → ∃ (κ : ℚ) (A : ℕ → ℂ), HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-(κ : ℂ) * (τ : ℂ))) A ∧ HasQ M (fun τ => sg c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] τ * ee (-(κ : ℂ) * (τ : ℂ))) (fun n => σ (A n)) := by
  intro c M a b d σ hM _ hσ h1 h2
  have hσ' : σ (ee ((b : ℂ) / M)) = ee (((d * b : ℕ) : ℂ) / M) := by
    rw [show (b : ℂ) / M = b * (1 / M) by ring, ee_nat_mul, map_pow, hσ, ← ee_nat_mul]
    congr 1; push_cast; ring
  obtain ⟨k, φ, p, p'⟩ := rel_sg hM hσ' h1 h2
  have e : ∀ τ : ℍ, ee (-((-(k : ℚ) / M : ℚ) : ℂ) * (τ : ℂ)) = Function.Periodic.qParam (M : ℝ) τ ^ k := fun τ => by
    unfold ee Function.Periodic.qParam
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  refine ⟨-(k : ℚ) / M, fun n => coeff n φ, ?_, ?_⟩
  · rw [hasQ_iff]; intro τ
    have := p τ
    simp only [e, mul_comm (sg _ _ _)]
    simpa only [Function.Periodic.qParam, Complex.ofReal_natCast] using this
  · rw [hasQ_iff]; intro τ
    have := p' τ
    simp only [e, mul_comm (sg _ _ _)]
    simpa only [Function.Periodic.qParam, Complex.ofReal_natCast, coeff_map, RingHom.coe_coe] using this

theorem sg_coeff_galois_int : ∀ (c M a b d : ℕ) (σ : ℂ ≃+* ℂ), 0 < M → a < M → σ (ee (1 / (M : ℂ))) = ee ((d : ℂ) / M) → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → ℂ), HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A ∧ HasQ M (fun τ => sg c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => σ (A n)) := by
  intro c M a b d σ hM _ hσ h1 h2
  have hσ' : σ (ee ((b : ℂ) / M)) = ee (((d * b : ℕ) : ℂ) / M) := by
    rw [show (b : ℂ) / M = b * (1 / M) by ring, ee_nat_mul, map_pow, hσ, ← ee_nat_mul]
    congr 1; push_cast; ring
  obtain ⟨k, φ, p, p'⟩ := rel_sg hM hσ' h1 h2
  have e : ∀ τ : ℍ, ee (-(((-(k : ℤ) : ℤ) : ℂ) / M) * (τ : ℂ)) = Function.Periodic.qParam (M : ℝ) τ ^ k := fun τ => by
    unfold ee Function.Periodic.qParam
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  refine ⟨-(k : ℤ), fun n => coeff n φ, ?_, ?_⟩
  · rw [hasQ_iff]; intro τ
    have := p τ
    simp only [e, mul_comm (sg _ _ _)]
    simpa only [Function.Periodic.qParam, Complex.ofReal_natCast] using this
  · rw [hasQ_iff]; intro τ
    have := p' τ
    simp only [e, mul_comm (sg _ _ _)]
    simpa only [Function.Periodic.qParam, Complex.ofReal_natCast, coeff_map, RingHom.coe_coe] using this

end GlobalTheory.Sieg
