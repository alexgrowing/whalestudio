import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.HermFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

section Two

variable {m l m' l' : Type*}

variable [Fintype m] [Fintype l] [Fintype m'] [Fintype l']

theorem form_fromBlocks_diag (A₁ : Matrix m m ℂ) (A₂ : Matrix l l ℂ) (u u' : m → ℂ)
    (w w' : l → ℂ) : form (fromBlocks A₁ 0 0 A₂) (Sum.elim u w) (Sum.elim u' w') =
      form A₁ u u' + form A₂ w w' := by
  simp [form_eq_sum, Fintype.sum_sum_type]

theorem posSemidef_fromBlocks_diag {A₁ : Matrix m m ℂ} {A₂ : Matrix l l ℂ} (h₁ : A₁.PosSemidef)
    (h₂ : A₂.PosSemidef) : (fromBlocks A₁ 0 0 A₂).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (IsHermitian.fromBlocks h₁.isHermitian (by simp) h₂.isHermitian) fun x => ?_
  have h : star x ⬝ᵥ (fromBlocks A₁ 0 0 A₂ *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A₁ *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (A₂ *ᵥ (x ∘ Sum.inr)) := by
    simp [dotProduct, mulVec, Fintype.sum_sum_type]
  rw [h]
  exact add_nonneg (h₁.dotProduct_mulVec_nonneg _) (h₂.dotProduct_mulVec_nonneg _)

theorem posDef_fromBlocks_diag {A₁ : Matrix m m ℂ} {A₂ : Matrix l l ℂ} (h₁ : A₁.PosDef)
    (h₂ : A₂.PosDef) : (fromBlocks A₁ 0 0 A₂).PosDef := by
  refine posDef_iff.2 ⟨IsHermitian.fromBlocks h₁.isHermitian (by simp) h₂.isHermitian,
    fun v hv => ?_⟩
  rw [← Sum.elim_comp_inl_inr v] at hv ⊢
  rw [form_fromBlocks_diag, form_self h₁.posSemidef, form_self h₂.posSemidef, ← ofReal_add,
    zero_lt_real]
  by_cases h : v ∘ Sum.inl = 0
  · have h' : v ∘ Sum.inr ≠ 0 := fun h' => hv (by rw [h, h']; simp)
    have := gnorm_pos h₂ h'
    positivity
  · have := gnorm_pos h₁ h
    positivity

variable [DecidableEq m] [DecidableEq l] {H₁ : E → Matrix m m ℂ} {H₂ : E → Matrix l l ℂ} {z : E}

end Two

section Family

variable {o : Type*} [DecidableEq o] {m m' : o → Type*}

theorem mdel_blockDiagonal' (A : ∀ i, E → Matrix (m i) (m' i) ℂ) (z ξ : E) :
    mdel (fun x => blockDiagonal' fun i => A i x) z ξ = blockDiagonal' fun i => mdel (A i) z ξ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h; simp
  · simp [blockDiagonal'_apply_ne _ _ _ h]

theorem mdbar_blockDiagonal' (A : ∀ i, E → Matrix (m i) (m' i) ℂ) (z ξ : E) :
    mdbar (fun x => blockDiagonal' fun i => A i x) z ξ =
      blockDiagonal' fun i => mdbar (A i) z ξ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h; simp
  · simp [blockDiagonal'_apply_ne _ _ _ h]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem mContDiffAt_blockDiagonal' {k : WithTop ℕ∞} {A : ∀ i, E → Matrix (m i) (m' i) ℂ} {z : E}
    (hA : ∀ i, MContDiffAt k (A i) z) :
    MContDiffAt k (fun x => blockDiagonal' fun i => A i x) z := by
  rintro ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h; simpa using hA i a b
  · simpa [blockDiagonal'_apply_ne _ _ _ h] using contDiffAt_const

variable [Fintype o] [∀ i, Fintype (m i)] [∀ i, Fintype (m' i)]

omit [∀ i, Fintype (m' i)] in

theorem blockDiagonal'_mulVec_apply (T : ∀ i, Matrix (m' i) (m i) ℂ) (v : (Σ i, m i) → ℂ) (i : o)
    (a : m' i) : (blockDiagonal' T *ᵥ v) ⟨i, a⟩ = (T i *ᵥ fun b => v ⟨i, b⟩) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [blockDiagonal'_apply_ne _ _ _ hj.symm]
  · simp

theorem form_blockDiagonal' (A : ∀ i, Matrix (m i) (m i) ℂ) (v w : (Σ i, m i) → ℂ) :
    form (blockDiagonal' A) v w = ∑ i, form (A i) (fun a => v ⟨i, a⟩) fun a => w ⟨i, a⟩ := by
  simp only [form, dotProduct, Fintype.sum_sigma, blockDiagonal'_mulVec_apply]
  rfl

theorem posSemidef_blockDiagonal' {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosSemidef) :
    (blockDiagonal' A).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_blockDiagonal'_iff.2 fun i => (h i).isHermitian) fun x => ?_
  simp only [dotProduct, Fintype.sum_sigma, blockDiagonal'_mulVec_apply]
  exact Finset.sum_nonneg fun i _ => (h i).dotProduct_mulVec_nonneg fun a => x ⟨i, a⟩

theorem gnorm_blockDiagonal'_sq {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosSemidef)
    (v : (Σ i, m i) → ℂ) :
    gnorm (blockDiagonal' A) v ^ 2 = ∑ i, gnorm (A i) (fun a => v ⟨i, a⟩) ^ 2 := by
  simp only [gnorm_sq (posSemidef_blockDiagonal' h), gnorm_sq (h _), form_blockDiagonal', re_sum]

theorem posDef_blockDiagonal' {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosDef) :
    (blockDiagonal' A).PosDef := by
  refine posDef_iff.2 ⟨isHermitian_blockDiagonal'_iff.2 fun i => (h i).isHermitian,
    fun v hv => ?_⟩
  rw [form_self (posSemidef_blockDiagonal' fun i => (h i).posSemidef),
    gnorm_blockDiagonal'_sq fun i => (h i).posSemidef, zero_lt_real]
  obtain ⟨⟨i, a⟩, ha⟩ := Function.ne_iff.1 hv
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _,
    pow_pos (gnorm_pos (h i) (Function.ne_iff.2 ⟨a, ha⟩)) 2⟩

variable [∀ i, DecidableEq (m i)] {H : ∀ i, E → Matrix (m i) (m i) ℂ} {z : E}

theorem isUnit_det_blockDiagonal' {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, IsUnit (A i).det) :
    IsUnit (blockDiagonal' A).det := by
  refine isUnit_det_of_right_inverse (B := blockDiagonal' fun i => (A i)⁻¹) ?_
  rw [← blockDiagonal'_mul, ← blockDiagonal'_one]
  congr 1
  funext i
  exact mul_nonsing_inv _ (h i)

theorem conn_blockDiagonal' (h : ∀ i, IsUnit (H i z).det) (ξ : E) :
    conn (fun x => blockDiagonal' fun i => H i x) z ξ = blockDiagonal' fun i => conn (H i) z ξ := by
  refine (eq_conn_of_compatible (H := fun x => blockDiagonal' fun i => H i x)
    (isUnit_det_blockDiagonal' h) ?_).symm
  rw [mdel_blockDiagonal', blockDiagonal'_transpose, ← blockDiagonal'_mul]
  congr 1
  funext i
  exact conn_transpose_mul (h i) ξ

theorem curv_blockDiagonal' {k : WithTop ℕ∞} (d : ∀ i, MContDiffAt k (H i) z)
    (h : ∀ i, IsUnit (H i z).det) (ξ η : E) :
    curv (fun x => blockDiagonal' fun i => H i x) z ξ η =
      blockDiagonal' fun i => curv (H i) z ξ η := by
  have he : (fun x => conn (fun x => blockDiagonal' fun i => H i x) x ξ) =ᶠ[𝓝 z]
      fun x => blockDiagonal' fun i => conn (H i) x ξ :=
    (eventually_all.2 fun i => (d i).eventually_isUnit (h i)).mono
      fun x hx => conn_blockDiagonal' hx ξ
  rw [curv, mdbar_congr he, mdbar_blockDiagonal' fun i x => conn (H i) x ξ, ← blockDiagonal'_neg]
  rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem isHermFrame_blockDiagonal' {U : Set E} (hU : IsOpen U) (h : ∀ i, IsHermFrame U (H i)) :
    IsHermFrame U fun x => blockDiagonal' fun i => H i x :=
  .of_mContDiffAt hU (fun _ hz => mContDiffAt_blockDiagonal' fun i => (h i).mContDiffAt hz)
    (fun z hz => isHermitian_blockDiagonal'_iff.2 fun i => (h i).herm z hz)
    fun z hz => isUnit_det_blockDiagonal' fun i => (h i).isUnit z hz

end Family

end GlobalTheory.HermFrame
