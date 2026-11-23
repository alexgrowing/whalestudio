import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem dotProduct_blockDiagonal_mulVec {R ι W : Type} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (f : W → Matrix ι ι R) (y : ι × W → R) :
    y ⬝ᵥ (blockDiagonal f *ᵥ y) = ∑ w, (fun i => y (i, w)) ⬝ᵥ (f w *ᵥ fun i => y (i, w)) := by
  simp only [dotProduct, mulVec]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Fintype.sum_prod_type_right, Finset.sum_eq_single w]
  · simp [blockDiagonal_apply]
  · intro v _ hv
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [blockDiagonal_apply, hv.symm]
  · simp

theorem dotProduct_block_ofReal {ι : Type} [Fintype ι] (a b : ℝ) (C P : Matrix ι ι ℝ)
    (y : ι → ℝ) :
    (fun i => (y i : ℂ)) ⬝ᵥ
        ((Matrix.of fun i j => (a : ℂ) * ((C i j : ℝ) : ℂ) +
          Complex.I * (b : ℂ) * ((P i j : ℝ) : ℂ)) *ᵥ fun i => (y i : ℂ)) =
      (a : ℂ) * ((y ⬝ᵥ (C *ᵥ y) : ℝ) : ℂ) + Complex.I * (b : ℂ) * ((y ⬝ᵥ (P *ᵥ y) : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec, Matrix.of_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def ZB {F : Type} [Field F] {ι : Type} {W : Type} (B : Matrix ι ι F) (ρ : W → (F →+* ℝ))
    (P : W → Matrix ι ι ℝ) (τ : W → ℂ) (w : W) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) + Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ)

theorem ZM_eq_blockDiagonal {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) : ZM B ρ P τ = blockDiagonal (ZB B ρ P τ) := rfl

theorem ZM_map_im {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) :
    (ZM B ρ P τ).map Complex.im = blockDiagonal fun w => (τ w).im • P w := by
  rw [ZM_eq_blockDiagonal]
  ext ⟨i, v⟩ ⟨j, u⟩
  by_cases h : v = u
  · subst h
    simp [ZB, blockDiagonal_apply]
  · simp [ZB, blockDiagonal_apply, h]

theorem ZM_symm_posDef_gauss (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) :
    QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) →
      (ZM B ρ P τ).IsSymm ∧ ((ZM B ρ P τ).map Complex.im).PosDef ∧
        ∀ x : ι × InfinitePlace F → ℝ,
          Complex.exp ((Real.pi : ℂ) * Complex.I *
            ((fun i => (x i : ℂ)) ⬝ᵥ (ZM B ρ P τ *ᵥ fun i => (x i : ℂ)))) =
              gauss B ρ P τ (cur x) := by
  rintro ⟨-, -, hB, -, -, hP, -⟩ τ hτ
  have hPs : ∀ w i j, P w j i = P w i j := fun w i j => by
    simpa using (hP w).isHermitian.apply i j
  refine ⟨?_, ?_, fun x => ?_⟩
  · rw [Matrix.IsSymm, ZM_eq_blockDiagonal, blockDiagonal_transpose]
    congr 1
    funext w
    ext i j
    simp only [transpose_apply, ZB, Matrix.of_apply]
    rw [hB.apply i j, hPs w i j]
  · rw [ZM_map_im]
    have hq : ∀ w (y : ι → ℝ), y ≠ 0 → 0 < y ⬝ᵥ (P w *ᵥ y) := fun w y hy => by
      simpa using (hP w).dotProduct_mulVec_pos hy
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · ext ⟨i, v⟩ ⟨j, u⟩
      by_cases h : v = u
      · subst h
        simp [blockDiagonal_apply, hPs v i j]
      · have h' : ¬ u = v := fun e => h e.symm
        simp [blockDiagonal_apply, h, h']
    · obtain ⟨⟨i, w⟩, hiw⟩ := Function.ne_iff.1 hx
      have hstar : star x = x := by
        funext p
        simp
      rw [hstar, dotProduct_blockDiagonal_mulVec]
      have hterm : ∀ v, (fun i => x (i, v)) ⬝ᵥ (((τ v).im • P v) *ᵥ fun i => x (i, v)) =
          (τ v).im * ((fun i => x (i, v)) ⬝ᵥ (P v *ᵥ fun i => x (i, v))) := fun v => by
        simp [smul_mulVec, dotProduct_smul]
      simp only [hterm]
      refine Finset.sum_pos' (fun v _ => ?_) ⟨w, Finset.mem_univ w, ?_⟩
      · by_cases hy : (fun i => x (i, v)) = 0
        · simp [hy]
        · exact (mul_pos (hτ v) (hq v _ hy)).le
      · refine mul_pos (hτ w) (hq w _ fun h0 => hiw ?_)
        simpa using congrFun h0 i
  · unfold gauss
    congr 1
    rw [ZM_eq_blockDiagonal, dotProduct_blockDiagonal_mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h := dotProduct_block_ofReal (τ w).re (τ w).im (B.map (ρ w)) (P w) (cur x w)
    simp only [Matrix.map_apply] at h
    have h2 : (fun i => ((x (i, w) : ℝ) : ℂ)) = fun i => ((cur x w i : ℝ) : ℂ) := rfl
    have h3 : ZB B ρ P τ w = Matrix.of fun i j => ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) +
        Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ) := rfl
    rw [h2, h3, h]
    linear_combination ((Real.pi : ℂ) * ((τ w).im : ℂ) * ((cur x w ⬝ᵥ (P w *ᵥ cur x w) : ℝ) : ℂ)) *
      Complex.I_mul_I

end GlobalTheory.CompanionTheory.SW.ThW
