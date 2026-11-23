import Mathlib

open Matrix Complex ComplexConjugate

namespace ReciprocityTheory.L2DbarEstimates

noncomputable def sqNorm {p : ℕ} (g : Fin p → ℂ) : ℝ := ∑ i, Complex.normSq (g i)

noncomputable def projPerp {p : ℕ} (g : Fin p → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  1 - ((sqNorm g : ℝ) : ℂ)⁻¹ • vecMulVec g (star g)

def SkodaMatrixStatement : Prop :=
  ∀ (p n : ℕ) (g : Fin p → ℂ) (J V : Matrix (Fin p) (Fin n) ℂ), g ≠ 0 →
    Complex.normSq (trace (projPerp g * J * Vᵀ)) ≤
      ((p : ℝ) - 1) * ∑ i, sqNorm ((projPerp g * J) *ᵥ V i)

def SkodaPointwiseStatement : Prop :=
  ∀ (p n : ℕ) (g : Fin p → ℂ) (J V : Matrix (Fin p) (Fin n) ℂ), g ≠ 0 →
    sqNorm g * Complex.normSq (∑ i, ∑ k,
        (starRingEnd ℂ ((projPerp g * J) i k) / ((sqNorm g : ℝ) : ℂ)) * starRingEnd ℂ (V i k)) ≤
      ((p : ℝ) - 1) * ∑ i, sqNorm ((projPerp g * J) *ᵥ V i) / sqNorm g

def ProjPerpNormStatement : Prop :=
  ∀ (p : ℕ) (g w : Fin p → ℂ), g ≠ 0 →
    sqNorm (projPerp g *ᵥ w) = sqNorm w - Complex.normSq (star g ⬝ᵥ w) / sqNorm g

variable {p : ℕ}

theorem sqNorm_pos {g : Fin p → ℂ} (hg : g ≠ 0) : 0 < sqNorm g := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
  unfold sqNorm
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
    (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (g j)) (Finset.mem_univ i))

theorem star_dotProduct_self (g : Fin p → ℂ) : star g ⬝ᵥ g = ((sqNorm g : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, sqNorm, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

theorem projPerp_apply (g : Fin p → ℂ) (i l : Fin p) :
    projPerp g i l = (if i = l then 1 else 0) - ((sqNorm g : ℝ) : ℂ)⁻¹ * (g i * conj (g l)) := by
  simp [projPerp, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, Complex.star_def]

theorem projPerp_mulVec (g w : Fin p → ℂ) :
    projPerp g *ᵥ w = w - (((sqNorm g : ℝ) : ℂ)⁻¹ * (star g ⬝ᵥ w)) • g := by
  ext i
  rw [mulVec, dotProduct]
  simp only [projPerp_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct, Pi.star_apply]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.star_def]
  ring

theorem star_dotProduct_projPerp_mulVec {g : Fin p → ℂ} (hg : g ≠ 0) (w : Fin p → ℂ) :
    star g ⬝ᵥ (projPerp g *ᵥ w) = 0 := by
  have hs : ((sqNorm g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sqNorm_pos hg).ne'
  rw [projPerp_mulVec, dotProduct_sub, dotProduct_smul, star_dotProduct_self, smul_eq_mul]
  field_simp
  ring

theorem projPerp_mulVec_idem {g : Fin p → ℂ} (hg : g ≠ 0) (w : Fin p → ℂ) :
    projPerp g *ᵥ (projPerp g *ᵥ w) = projPerp g *ᵥ w := by
  rw [projPerp_mulVec g (projPerp g *ᵥ w), star_dotProduct_projPerp_mulVec hg, mul_zero,
    zero_smul, sub_zero]

theorem conj_projPerp (g : Fin p → ℂ) (i l : Fin p) :
    conj (projPerp g i l) = projPerp g l i := by
  rw [projPerp_apply, projPerp_apply]
  simp only [map_sub, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj,
    apply_ite (starRingEnd ℂ), map_one, map_zero]
  by_cases h : i = l
  · subst h
    simp only [if_pos rfl]
    ring
  · rw [if_neg h, if_neg (Ne.symm h)]
    ring

private theorem sqNorm_projPerp_mulVec {g : Fin p → ℂ} (hg : g ≠ 0) (w : Fin p → ℂ) :
    sqNorm (projPerp g *ᵥ w) = sqNorm w - Complex.normSq (star g ⬝ᵥ w) / sqNorm g := by
  have key : ((sqNorm (projPerp g *ᵥ w) : ℝ) : ℂ) =
      ((sqNorm w : ℝ) : ℂ) - ((Complex.normSq (star g ⬝ᵥ w) : ℝ) : ℂ) / ((sqNorm g : ℝ) : ℂ) := by
    rw [← star_dotProduct_self (projPerp g *ᵥ w), ← star_dotProduct_self w]
    have hst : star (projPerp g *ᵥ w) =
        star w - star (((sqNorm g : ℝ) : ℂ)⁻¹ * (star g ⬝ᵥ w)) • star g := by
      rw [projPerp_mulVec, star_sub, star_smul]
    rw [hst, sub_dotProduct, smul_dotProduct, star_dotProduct_projPerp_mulVec hg, smul_zero,
      sub_zero, projPerp_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      Matrix.star_dotProduct w g, Complex.star_def, mul_assoc, Complex.mul_conj]
    ring
  exact_mod_cast key

theorem sum_normSq_projPerp {g : Fin p → ℂ} (hg : g ≠ 0) :
    ∑ i, ∑ l, Complex.normSq (projPerp g i l) = (p : ℝ) - 1 := by
  rw [Finset.sum_comm]
  have hcol : ∀ l, ∑ i, Complex.normSq (projPerp g i l) = 1 - Complex.normSq (g l) / sqNorm g := by
    intro l
    have h1 : sqNorm (Pi.single l (1 : ℂ)) = 1 := by
      unfold sqNorm
      rw [Finset.sum_eq_single l (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simp
    have := sqNorm_projPerp_mulVec hg (Pi.single l (1 : ℂ))
    have h2 : star g ⬝ᵥ Pi.single l (1 : ℂ) = star (g l) := by
      simp [dotProduct, Pi.single_apply]
    rw [Matrix.mulVec_single_one, h2, h1, Complex.star_def, Complex.normSq_conj] at this
    exact this
  rw [Finset.sum_congr rfl (fun l _ => hcol l), Finset.sum_sub_distrib, ← Finset.sum_div]
  change _ - sqNorm g / sqNorm g = _
  rw [div_self (sqNorm_pos hg).ne']
  simp

theorem normSq_sum_mul_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    Complex.normSq (∑ q ∈ s, a q * b q) ≤
      (∑ q ∈ s, Complex.normSq (a q)) * ∑ q ∈ s, Complex.normSq (b q) := by
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ q ∈ s, a q * b q‖ ^ 2 ≤ (∑ q ∈ s, ‖a q‖ * ‖b q‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => norm_mul _ _))
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s _ _

theorem trace_mul_transpose {n : ℕ} (A V : Matrix (Fin p) (Fin n) ℂ) :
    trace (A * Vᵀ) = ∑ i, ∑ k, A i k * V i k := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]

theorem skodaMatrix : SkodaMatrixStatement := by
  intro p n g J V hg
  have hPu : ∀ i, projPerp g *ᵥ ((projPerp g * J) *ᵥ V i) = (projPerp g * J) *ᵥ V i := by
    intro i
    rw [← Matrix.mulVec_mulVec]
    exact projPerp_mulVec_idem hg _
  have htr : trace (projPerp g * J * Vᵀ) =
      ∑ x : Fin p × Fin p, projPerp g x.1 x.2 * ((projPerp g * J) *ᵥ V x.1) x.2 := by
    rw [trace_mul_transpose, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (congrFun (hPu i) i).symm
  rw [htr]
  refine (normSq_sum_mul_le _ _ _).trans ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_normSq_projPerp hg]
  exact le_rfl

theorem skodaPointwise : SkodaPointwiseStatement := by
  intro p n g J V hg
  have hs := sqNorm_pos hg
  have hM := skodaMatrix p n g J V hg
  have hsum : (∑ i, ∑ k, (starRingEnd ℂ ((projPerp g * J) i k) / ((sqNorm g : ℝ) : ℂ)) *
      starRingEnd ℂ (V i k)) =
      starRingEnd ℂ (trace (projPerp g * J * Vᵀ)) / ((sqNorm g : ℝ) : ℂ) := by
    rw [trace_mul_transpose, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    ring
  rw [hsum, Complex.normSq_div, Complex.normSq_conj, Complex.normSq_ofReal]
  calc sqNorm g * (Complex.normSq (trace (projPerp g * J * Vᵀ)) / (sqNorm g * sqNorm g))
      = Complex.normSq (trace (projPerp g * J * Vᵀ)) / sqNorm g := by
        rw [mul_div_assoc', mul_div_mul_left _ _ hs.ne']
    _ ≤ ((p : ℝ) - 1) * (∑ i, sqNorm ((projPerp g * J) *ᵥ V i)) / sqNorm g :=
        div_le_div_of_nonneg_right hM hs.le
    _ = _ := by rw [mul_div_assoc, Finset.sum_div]

theorem projPerp_sqNorm : ProjPerpNormStatement := by
  intro p g w hg
  exact sqNorm_projPerp_mulVec hg w

end ReciprocityTheory.L2DbarEstimates
