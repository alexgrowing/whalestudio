import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

noncomputable section

namespace GlobalTheory.FockSeq

open MvPolynomial GlobalTheory.FockAlg

variable {σ : Type}

abbrev L2 (σ : Type) : Type := lp (fun _ : σ →₀ ℕ => ℂ) 2

def mfact (α : σ →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial

theorem mfact_pos (α : σ →₀ ℕ) : 0 < mfact α := by
  unfold mfact Finsupp.prod
  exact Finset.prod_pos fun l _ => Nat.factorial_pos (α l)

theorem mfact_cast (α : σ →₀ ℕ) : ((mfact α : ℕ) : ℂ) = α.prod fun _ k => (k.factorial : ℂ) := by
  unfold mfact Finsupp.prod
  push_cast
  rfl

def wt (α : σ →₀ ℕ) : ℂ := (Real.sqrt (mfact α) : ℝ)

theorem wt_ne_zero (α : σ →₀ ℕ) : wt α ≠ 0 := by
  have h : 0 < Real.sqrt (mfact α : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 (mfact_pos α))
  unfold wt
  exact_mod_cast h.ne'

theorem star_wt_mul (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) * wt α = (mfact α : ℕ) := by
  have h : Real.sqrt (mfact α : ℝ) * Real.sqrt (mfact α : ℝ) = (mfact α : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  unfold wt
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, h, Complex.ofReal_natCast]

variable [DecidableEq σ]

def emb (σ : Type) [DecidableEq σ] : MvPolynomial σ ℂ →ₗ[ℂ] L2 σ :=
  (basisMonomials σ ℂ).constr ℂ fun α => lp.single 2 α (wt α)

theorem emb_monomial (α : σ →₀ ℕ) (c : ℂ) : emb σ (monomial α c) = lp.single 2 α (c * wt α) := by
  have h : monomial α c = c • basisMonomials σ ℂ α := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, emb, Module.Basis.constr_basis, ← smul_eq_mul, lp.single_smul]

theorem emb_apply (f : MvPolynomial σ ℂ) (α : σ →₀ ℕ) : emb σ f α = coeff α f * wt α := by
  induction f using MvPolynomial.induction_on' with
  | monomial β c =>
    rw [emb_monomial, lp.single_apply, coeff_monomial]
    by_cases h : β = α
    · subst h
      simp
    · simp [h]
  | add f g hf hg =>
    rw [map_add, lp.coeFn_add, Pi.add_apply, hf, hg, coeff_add, add_mul]

theorem emb_injective : Function.Injective (emb σ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  ext α
  have h : emb σ f α = 0 := by rw [hf]; rfl
  rw [emb_apply] at h
  rw [coeff_zero]
  exact (mul_eq_zero.1 h).resolve_right (wt_ne_zero α)

theorem dense_range_emb : Dense (Set.range (emb σ)) := by
  intro x
  have hx := lp.hasSum_single (E := fun _ : σ →₀ ℕ => ℂ) (p := 2) ENNReal.ofNat_ne_top x
  rw [HasSum] at hx
  refine mem_closure_of_tendsto hx (Filter.Eventually.of_forall fun s => ?_)
  refine ⟨∑ α ∈ s, monomial α (x α / wt α), ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [emb_monomial, div_mul_cancel₀ _ (wt_ne_zero α)]

theorem isFockIsometry_embedding : IsFockIP (emb σ) := by
  intro α β
  rw [emb_monomial, emb_monomial, lp.inner_single_left, lp.single_apply, one_mul, one_mul]
  by_cases h : α = β
  · subst h
    rw [Pi.single_eq_same, if_pos rfl, RCLike.inner_apply, mul_comm, star_wt_mul, mfact_cast]
  · rw [Pi.single_eq_of_ne h, if_neg h, inner_zero_right]

omit [DecidableEq σ] in

def diag (c : (σ →₀ ℕ) → ℂ) (hc : ∀ α, ‖c α‖ = 1) : L2 σ →L[ℂ] L2 σ :=
  lp.mapCLM 2 (fun α => c α • ContinuousLinearMap.id ℂ ℂ) zero_le_one fun α => by
    simp [norm_smul, hc]

omit [DecidableEq σ] in

@[simp] theorem diag_apply (c : (σ →₀ ℕ) → ℂ) (hc : ∀ α, ‖c α‖ = 1) (x : L2 σ) (α : σ →₀ ℕ) :
    diag c hc x α = c α * x α := rfl

omit [DecidableEq σ] in

theorem norm_diag (c : (σ →₀ ℕ) → ℂ) (hc : ∀ α, ‖c α‖ = 1) (x : L2 σ) : ‖diag c hc x‖ = ‖x‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  congr 1
  refine tsum_congr fun α => ?_
  rw [diag_apply, norm_mul, hc, one_mul]

theorem diag_emb_monomial (c : (σ →₀ ℕ) → ℂ) (hc : ∀ α, ‖c α‖ = 1) (α : σ →₀ ℕ) (a : ℂ) :
    diag c hc (emb σ (monomial α a)) = c α • emb σ (monomial α a) := by
  ext β
  rw [diag_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, emb_monomial, lp.single_apply]
  by_cases h : β = α
  · subst h
    rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

theorem continuous_of_dense {G H : Type*} [TopologicalSpace G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (π : G → H →L[ℂ] H) (hπ : ∀ g x, ‖π g x‖ = ‖x‖) {S : Set H} (hS : Dense S)
    (h : ∀ x ∈ S, Continuous fun g => π g x) (x : H) : Continuous fun g => π g x := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hyS, hxy⟩ := Metric.mem_closure_iff.1 (hS x) (ε / 3) (by positivity)
  have hy := (h y hyS).continuousAt (x := g₀)
  rw [ContinuousAt, Metric.tendsto_nhds] at hy
  have hd : ∀ g, dist (π g x) (π g y) = dist x y := fun g => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, hπ]
  filter_upwards [hy (ε / 3) (by positivity)] with g hg
  have h₁ := hd g
  have h₂ := hd g₀
  rw [dist_comm] at h₂
  calc dist (π g x) (π g₀ x)
      ≤ dist (π g x) (π g y) + dist (π g y) (π g₀ y) + dist (π g₀ y) (π g₀ x) :=
        dist_triangle4 _ _ _ _
    _ < ε := by rw [h₁, h₂]; linarith

example : ‖emb σ 1‖ = 1 := by
  rw [← C_1, C_apply, emb_monomial, lp.norm_single (by simp)]
  simp [wt, mfact]

end GlobalTheory.FockSeq
