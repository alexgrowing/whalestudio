import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.FrobChainSeries

open Finset

section General

variable {A R : Type*} [CommRing A] [CommRing R]

theorem dvd_of_limit (w L : A) (b : ℕ → A) (hL : ∀ n, L - ∑ i ∈ range n, w ^ i * b i ∈ Ideal.span {w ^ n})
    (M : ℕ) : w ^ M ∣ L - ∑ j ∈ range M, b j * w ^ j := by
  have h := Ideal.mem_span_singleton.1 (hL M)
  rwa [Finset.sum_congr rfl (fun i _ => mul_comm (w ^ i) (b i))] at h

theorem chain_dvd (φ : A →+* A) (hφ : Function.Bijective φ) (ι : R →+* A) (hι : ∀ c, φ (ι c) = ι c)
    (ω y : ℕ → A) (c : ℕ → R) (hω : ∀ n, φ (ω (n + 1)) = ω n) (hy : ∀ n, φ (y (n + 1)) = y n)
    (h0 : ∀ M, ω 0 ^ M ∣ y 0 - ∑ j ∈ range M, ι (c j) * ω 0 ^ j) :
    ∀ n M, ω n ^ M ∣ y n - ∑ j ∈ range M, ι (c j) * ω n ^ j := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    intro M
    obtain ⟨z, hz⟩ := ih M
    obtain ⟨z', rfl⟩ := hφ.2 z
    refine ⟨z', hφ.1 ?_⟩
    simp only [map_sub, map_sum, map_mul, map_pow, hι, hω, hy]
    exact hz

end General

section OC

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.LTTilt

variable {l : ℕ} [Fact l.Prime]

theorem one_le_norm_of_isUnit {c : OC l} (h : IsUnit c) : 1 ≤ ‖(c : ℂ_[l])‖ := by
  obtain ⟨d, hd⟩ := h.exists_right_inv
  have e : ‖(c : ℂ_[l])‖ * ‖(d : ℂ_[l])‖ = 1 := by
    rw [← norm_mul]
    have : (c : ℂ_[l]) * (d : ℂ_[l]) = 1 := congrArg Subtype.val hd
    rw [this, norm_one]
  have hd1 := norm_OC_le_one d
  nlinarith [norm_nonneg (c : ℂ_[l]), norm_nonneg (d : ℂ_[l])]

theorem eq_of_norm_le {x u : ℂ_[l]} {a : ℝ} (ha : a < 1)
    (h : ∀ M : ℕ, ‖x - u‖ ≤ 2 * a ^ M) : x = u := by
  have ha0 : 0 ≤ a := by
    have h1 := h 1
    rw [pow_one] at h1
    linarith [norm_nonneg (x - u)]
  have hlim : Filter.Tendsto (fun M : ℕ => 2 * a ^ M) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha).const_mul 2
  have := ge_of_tendsto' hlim h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem eval_eq {A R : Type*} [CommRing A] [CommRing R] (θ : A →+* OC l) (ι : R →+* A) (a : R →+* OC l)
    (hθι : ∀ c, θ (ι c) = a c) (w y : A) (c : ℕ → R) (u : OC l) (hw : ‖(θ w : ℂ_[l])‖ < 1)
    (hS : HasSum (fun i => ((a (c i) * θ w ^ i : OC l) : ℂ_[l])) (u : ℂ_[l]))
    (hd : ∀ M, w ^ M ∣ y - ∑ j ∈ range M, ι (c j) * w ^ j) : θ y = u := by
  refine Subtype.ext (eq_of_norm_le hw fun M => ?_)
  obtain ⟨z, hz⟩ := hd M
  have h1 : θ y - ∑ j ∈ range M, a (c j) * θ w ^ j = θ w ^ M * θ z := by
    have := congrArg θ hz
    simpa only [map_sub, map_sum, map_mul, map_pow, hθι] using this
  have h2 : ‖(θ y : ℂ_[l]) - ((∑ j ∈ range M, a (c j) * θ w ^ j : OC l) : ℂ_[l])‖ ≤ ‖(θ w : ℂ_[l])‖ ^ M := by
    have e : (θ y : ℂ_[l]) - ((∑ j ∈ range M, a (c j) * θ w ^ j : OC l) : ℂ_[l]) =
        (((θ w ^ M * θ z : OC l)) : ℂ_[l]) := by rw [← h1]; push_cast; rfl
    rw [e]
    push_cast
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (norm_OC_le_one _)
  have h3 := norm_tail_le (fun i => a (c i)) (θ w) (u : ℂ_[l]) hS M
  have h4 := norm_sub_le_norm_sub_add_norm_sub (θ y : ℂ_[l])
    ((∑ j ∈ range M, a (c j) * θ w ^ j : OC l) : ℂ_[l]) (u : ℂ_[l])
  rw [norm_sub_rev (((∑ j ∈ range M, a (c j) * θ w ^ j : OC l) : ℂ_[l]))] at h4
  linarith

end OC

end GlobalTheory.FrobChainSeries

open GlobalTheory.FrobChainSeries in

theorem GlobalTheory.FrobChainSeries.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ω : ℕ → AK K) (G : PowerSeries ↥(OL K)) (u : ℕ → OC l),
    (∀ n, frobq K (ω (n + 1)) = ω n) → (∀ n, ‖((thetaK K (ω n) : OC l) : ℂ_[l])‖ < 1) →
    (∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i G) * thetaK K (ω n) ^ i : OC l) : ℂ_[l])) (u n : ℂ_[l])) →
    ∃ y : ℕ → AK K, (∀ n, frobq K (y (n + 1)) = y n) ∧ (∀ n, thetaK K (y n) = u n) ∧
      ∀ M : ℕ, ω 0 ^ M ∣ y 0 - ∑ j ∈ Finset.range M, inO K (PowerSeries.coeff j G) * ω 0 ^ j := by
  intro l _ K ω G u hω hθ hS
  have hnu : ¬ IsUnit (red K (ω 0)) := fun h =>
    absurd (hθ 0) (not_lt.2 (one_le_norm_of_isUnit (((isUnit_iff_red _).2 h).map (thetaK K))))
  haveI := complete_single hnu
  obtain ⟨L, hL⟩ := GlobalTheory.Per.AinfComplete.summ_of_precomplete (ω 0) (fun i => inO K (PowerSeries.coeff i G))
  let r := Function.surjInv (frobq_bijective K).2
  have hy : ∀ n, frobq K (r^[n + 1] L) = r^[n] L := fun n => by
    rw [Function.iterate_succ_apply']
    exact Function.surjInv_eq (frobq_bijective K).2 _
  have hd := chain_dvd (frobq K).toRingHom (frobq_bijective K) (inO K) (frobq_inO K) ω (fun n => r^[n] L)
    (fun j => PowerSeries.coeff j G) hω hy (dvd_of_limit (ω 0) L _ hL)
  exact ⟨fun n => r^[n] L, hy, fun n => eval_eq (thetaK K) (inO K) (intToOC K) (thetaK_inO (K := K)) (ω n) _ _ (u n)
    (hθ n) (hS n) (hd n), hd 0⟩
