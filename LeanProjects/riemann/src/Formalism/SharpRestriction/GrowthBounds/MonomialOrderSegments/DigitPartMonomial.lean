import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Monomial

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

def lsup {σ τ : Type} (φ : (σ →₀ ℕ) → MvPolynomial τ K) : MvPolynomial σ K →ₗ[K] MvPolynomial τ K :=
  (basisMonomials σ K).constr K φ

theorem lsup_monomial {σ τ : Type} (φ : (σ →₀ ℕ) → MvPolynomial τ K) (α : σ →₀ ℕ) (c : K) :
    lsup φ (monomial α c) = c • φ α := by
  have h : monomial α c = c • (basisMonomials σ K) α := by simp [smul_monomial]
  rw [h, map_smul, lsup, Module.Basis.constr_basis]

theorem lsup_apply {σ τ : Type} (φ : (σ →₀ ℕ) → MvPolynomial τ K) (F : MvPolynomial σ K) :
    lsup φ F = ∑ α ∈ F.support, F.coeff α • φ α := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun α _ => lsup_monomial φ α _

theorem dg_eq_lsup {σ : Type} (f : (σ →₀ ℕ) → K) : dg f = lsup fun α => monomial α (f α) := rfl

theorem dg_apply {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg f F = ∑ α ∈ F.support, monomial α (f α * F.coeff α) := by
  rw [dg_eq_lsup, lsup_apply]
  exact Finset.sum_congr rfl fun α _ => by rw [smul_monomial, smul_eq_mul, mul_comm]

def ddivL {σ : Type} (M : σ →₀ ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  lsup fun α => if M ≤ α then monomial (α - M) (α.prod fun x k => (k.choose (M x) : K)) else 0

theorem ddiv_eq {σ : Type} (M : σ →₀ ℕ) (F : MvPolynomial σ K) : ddiv M F = ddivL M F := by
  rw [ddivL, lsup_apply, ddiv]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [smul_monomial, smul_eq_mul]
  · rw [smul_zero]

theorem ddiv_monomial {σ : Type} (M α : σ →₀ ℕ) (c : K) :
    ddiv M (monomial α c) =
      if M ≤ α then monomial (α - M) (c * α.prod fun x k => (k.choose (M x) : K)) else 0 := by
  rw [ddiv_eq, ddivL, lsup_monomial]
  split_ifs
  · rw [smul_monomial, smul_eq_mul]
  · rw [smul_zero]

theorem ddiv_add {σ : Type} (M : σ →₀ ℕ) (F G : MvPolynomial σ K) :
    ddiv M (F + G) = ddiv M F + ddiv M G := by simp only [ddiv_eq, map_add]

theorem ddiv_smul {σ : Type} (M : σ →₀ ℕ) (a : K) (F : MvPolynomial σ K) :
    ddiv M (a • F) = a • ddiv M F := by simp only [ddiv_eq, map_smul]

theorem ddiv_sum {σ ι : Type} (M : σ →₀ ℕ) (s : Finset ι) (f : ι → MvPolynomial σ K) :
    ddiv M (∑ i ∈ s, f i) = ∑ i ∈ s, ddiv M (f i) := by simp only [ddiv_eq, map_sum]

theorem coeff_ddiv {σ : Type} (M β : σ →₀ ℕ) (F : MvPolynomial σ K) :
    (ddiv M F).coeff β = F.coeff (β + M) * (β + M).prod fun x k => (k.choose (M x) : K) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [ddiv_monomial, coeff_monomial]
    by_cases h : M ≤ α
    · rw [if_pos h, coeff_monomial]
      by_cases h2 : α - M = β
      · have : α = β + M := by rw [← h2, tsub_add_cancel_of_le h]
        rw [if_pos h2, if_pos this, this]
      · have : ¬ α = β + M := by
          intro h3; apply h2; rw [h3, add_tsub_cancel_right]
        rw [if_neg h2, if_neg this, zero_mul]
    · have : ¬ α = β + M := by
        intro h3; apply h; rw [h3]; exact le_add_self
      rw [if_neg h, if_neg this, coeff_zero, zero_mul]
  | add p q hp hq => rw [ddiv_add, coeff_add, coeff_add, hp, hq, add_mul]

namespace TwistData

variable (D : TwistData K)

def digitPartL (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) :
    MvPolynomial (D.OL × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun α => if D.InClass p ρ α then monomial (D.liftE p α) 1 else 0

theorem digitPart_eq (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ F = D.digitPartL p ρ F := by
  rw [digitPartL, lsup_apply, digitPart]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [smul_monomial, smul_eq_mul, mul_one]
  · rw [smul_zero]

theorem digitPart_monomial (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (α : D.EA) (c : K) :
    D.digitPart p ρ (monomial α c) = if D.InClass p ρ α then monomial (D.liftE p α) c else 0 := by
  rw [digitPart_eq, digitPartL, lsup_monomial]
  split_ifs
  · rw [smul_monomial, smul_eq_mul, mul_one]
  · rw [smul_zero]

theorem digitPart_add (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (F G : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (F + G) = D.digitPart p ρ F + D.digitPart p ρ G := by
  simp only [digitPart_eq, map_add]

theorem digitPart_smul (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (a : K) (F : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (a • F) = a • D.digitPart p ρ F := by
  simp only [digitPart_eq, map_smul]

theorem digitPart_sum {ι : Type} (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (s : Finset ι)
    (f : ι → MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (∑ i ∈ s, f i) = ∑ i ∈ s, D.digitPart p ρ (f i) := by
  simp only [digitPart_eq, map_sum]

theorem gaAct_eq (G : MvPolynomial (D.OL × Fin D.r) K) : D.gaAct G = dg D.ga G := by
  rw [dg_apply, gaAct]

end TwistData

end Formalism.MainNotions.PlaneGram
