import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockModelPosFrameBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChTwoInvOfIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChTwoBlockDiagonalSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChTwoImaginaryPartSymmetricZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFderiv

open Matrix Filter Topology GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.BlockChTwoSum

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem chTwo_congr_curv {n : Type} [Fintype n] [DecidableEq n] {H K : E → Matrix n n ℂ} {z : E}
    (h : ∀ ξ η, curv H z ξ η = curv K z ξ η) (ξ₁ η₁ ξ₂ η₂ : E) :
    chTwo H z ξ₁ η₁ ξ₂ η₂ = chTwo K z ξ₁ η₁ ξ₂ η₂ := by
  simp only [chTwo, h]

theorem chTwo_submatrix_equiv {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (K : E → Matrix n n ℂ) (e : m ≃ n) (z ξ₁ η₁ ξ₂ η₂ : E) :
    chTwo (fun x => (K x).submatrix e e) z ξ₁ η₁ ξ₂ η₂ = chTwo K z ξ₁ η₁ ξ₂ η₂ := by
  simp only [chTwo, curv_submatrix_equiv, submatrix_apply]
  congr 1
  exact Fintype.sum_equiv e _ _ fun a => Fintype.sum_equiv e _ _ fun b => rfl

theorem posDef_mul_mul_conjTranspose {m n : Type} [Fintype m] [Fintype n] {M : Matrix n n ℂ} (hM : M.PosDef)
    {P : Matrix m n ℂ} (hP : LinearIndependent ℂ P) : (P * M * Pᴴ).PosDef :=
  hM.mul_mul_conjTranspose_same (vecMul_injective_iff.2 hP)

theorem sum_chTwo_blocks {ι : Type} [Fintype ι] {μ : ι → ℕ} {g : ℕ} {W : Set E} {w : E}
    (Q : ∀ τ, E → Matrix (Fin (μ τ)) (Fin g) ℂ) {M : E → Matrix (Fin g) (Fin g) ℂ} (hW : IsOpen W) (hw : w ∈ W)
    (hQ : ∀ τ i l, DifferentiableOn ℂ (fun z => Q τ z i l) W) (hM : MContDiffAt 2 M w) (hp : (M w).PosDef)
    (hc : Fintype.card (Σ τ, Fin (μ τ)) = g) (hl : LinearIndependent ℂ (fun p : Σ τ, Fin (μ τ) => Q p.1 w p.2))
    (ho : ∀ z ∈ W, ∀ τ τ', τ ≠ τ' → Q τ z * M z * (Q τ' z)ᴴ = 0) :
    (∀ τ, MContDiffAt 2 (fun z => Q τ z * M z * (Q τ z)ᴴ) w ∧ IsUnit (Q τ w * M w * (Q τ w)ᴴ).det) ∧
      ∀ ξ₁ η₁ ξ₂ η₂ : E,
        ∑ τ, chTwo (fun z => Q τ z * M z * (Q τ z)ᴴ) w ξ₁ η₁ ξ₂ η₂ = chTwo M w ξ₁ η₁ ξ₂ η₂ := by
  classical
  have hQ2 : ∀ τ, MContDiffAt 2 (Q τ) w := fun τ i l => HoloNormed.contDiffAt_two_real hW (hQ τ i l) hw
  have h1 : ∀ τ, MContDiffAt 2 (fun z => Q τ z * M z * (Q τ z)ᴴ) w := fun τ =>
    ((hQ2 τ).mul hM).mul (hQ2 τ).conjTranspose
  have h2 : ∀ τ, IsUnit (Q τ w * M w * (Q τ w)ᴴ).det := fun τ =>
    (isUnit_iff_isUnit_det _).1
      (posDef_mul_mul_conjTranspose hp (hl.comp (Sigma.mk τ) sigma_mk_injective)).isUnit
  refine ⟨fun τ => ⟨h1 τ, h2 τ⟩, fun ξ₁ η₁ ξ₂ η₂ => ?_⟩
  let e : Fin g ≃ (Σ τ, Fin (μ τ)) := (Fintype.equivFinOfCardEq hc).symm
  let A : E → Matrix (Fin g) (Fin g) ℂ := fun z => of fun l a => Q (e a).1 z (e a).2 l
  have hA2 : MContDiffAt 2 A w := fun l a => hQ2 _ _ _
  have hAu : IsUnit (A w).det := by
    rw [← det_transpose, ← isUnit_iff_isUnit_det, ← linearIndependent_rows_iff_isUnit]
    exact hl.comp e e.injective
  have hA0 : ∀ᶠ x in 𝓝 w, ∀ η, mdbar A x η = 0 := by
    filter_upwards [hW.mem_nhds hw] with x hx η
    ext l a
    exact DFunLike.congr_fun (dbar_eq_zero ((hQ (e a).1 (e a).2 l).differentiableAt (hW.mem_nhds hx))) η
  have he : (fun x => (blockDiagonal' fun τ => Q τ x * M x * (Q τ x)ᴴ).submatrix e e) =ᶠ[𝓝 w]
      fun x => (A x)ᵀ * M x * (A x)ᴴᵀ := by
    filter_upwards [hW.mem_nhds hw] with x hx
    ext a b
    have e1 : ((A x)ᵀ * M x * (A x)ᴴᵀ) a b = (Q (e a).1 x * M x * (Q (e b).1 x)ᴴ) (e a).2 (e b).2 := rfl
    rw [e1, submatrix_apply]
    generalize e a = p
    generalize e b = q
    obtain ⟨τ, i⟩ := p
    obtain ⟨τ', j⟩ := q
    by_cases h : τ = τ'
    · subst h; rw [blockDiagonal'_apply_eq]
    · rw [blockDiagonal'_apply_ne _ _ _ h, ho x hx τ τ' h]; rfl
  rw [← GlobalTheory.T.chTwo_block_diagonal_sum h1 h2, ← chTwo_submatrix_equiv _ e, chTwo_congr_curv (curv_congr he),
    HodgeChTwo.chTwo_changeFrame hM ((isUnit_iff_isUnit_det _).1 hp.isUnit) hA2 hAu hA0]

theorem sum_chTwo_blocks_eq_zero : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι] {μ : ι → ℕ} {g : ℕ} {W : Set E} {w : E} (Q : ∀ τ, E → Matrix (Fin (μ τ)) (Fin g) ℂ) (Z : E → Matrix (Fin g) (Fin g) ℂ) (κ : ι → ℝ) (H : ∀ τ, E → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ), IsOpen W → w ∈ W → (∀ τ i l, DifferentiableOn ℂ (fun z => Q τ z i l) W) → (∀ i k, DifferentiableOn ℂ (fun z => Z z i k) W) → (∀ z ∈ W, (Z z).IsSymm) → (∀ z ∈ W, ((Z z).map fun c => ((c.im : ℝ) : ℂ)).PosDef) → Fintype.card (Σ τ, Fin (μ τ)) = g → LinearIndependent ℂ (fun p : Σ τ, Fin (μ τ) => Q p.1 w p.2) → (∀ τ, 0 < κ τ) → (∀ z ∈ W, (∀ τ, H τ z = ((κ τ : ℝ) : ℂ) • (Q τ z * ((Z z).map fun c => ((c.im : ℝ) : ℂ))⁻¹ * (Q τ z)ᴴ)) ∧ ∀ τ τ', τ ≠ τ' → Q τ z * ((Z z).map fun c => ((c.im : ℝ) : ℂ))⁻¹ * (Q τ' z)ᴴ = 0) → (∀ τ, MContDiffAt 2 (H τ) w ∧ IsUnit (H τ w).det) ∧ ∀ ξ₁ η₁ ξ₂ η₂ : E, ∑ τ, chTwo (H τ) w ξ₁ η₁ ξ₂ η₂ = 0 := by
  intro E _ _ _ _ ι _ μ g W w Q Z κ H hW hw hQ hZ hs hp hc hl hκ hH
  have hY : MContDiffAt 2 (fun z => (Z z).map fun c => ((c.im : ℝ) : ℂ)) w := fun i k =>
    (Complex.ofRealCLM.comp Complex.imCLM).contDiff.contDiffAt.comp w
      (HoloNormed.contDiffAt_two_real hW (hZ i k) hw)
  have hYu := (isUnit_iff_isUnit_det _).1 (hp w hw).isUnit
  obtain ⟨h1, h2⟩ := sum_chTwo_blocks Q hW hw hQ (hY.inv hYu) (hp w hw).inv hc hl fun z hz => (hH z hz).2
  have he : ∀ τ, H τ =ᶠ[𝓝 w] fun z => ((κ τ : ℝ) : ℂ) •
      (Q τ z * ((Z z).map fun c => ((c.im : ℝ) : ℂ))⁻¹ * (Q τ z)ᴴ) := fun τ =>
    mem_of_superset (hW.mem_nhds hw) fun z hz => (hH z hz).1 τ
  refine ⟨fun τ => ⟨fun a b => ?_, ?_⟩, fun ξ₁ η₁ ξ₂ η₂ => ?_⟩
  · exact (MContDiffAt.smul contDiffAt_const (h1 τ).1 a b).congr_of_eventuallyEq
      ((he τ).mono fun x hx => congrFun (congrFun hx a) b)
  · rw [(hH w hw).1 τ, det_smul]
    exact (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (hκ τ).ne')).isUnit.mul (h1 τ).2
  · rw [Finset.sum_congr rfl fun τ _ => chTwo_congr_curv (fun ξ η => (curv_congr (he τ) ξ η).trans
      (CurvInterp.Block.curv_const_smul (hκ τ).ne' (h1 τ).1 (h1 τ).2 ξ η)) ξ₁ η₁ ξ₂ η₂, h2,
      HodgeChTwo.chTwo_inv_of_isSymm hY hYu
        (mem_of_superset (hW.mem_nhds hw) fun z hz => (hs z hz).map _)]
    exact GlobalTheory.T.chTwo_imaginary_part_symmetric_zero hW hw hZ hs hYu ξ₁ η₁ ξ₂ η₂

end GlobalTheory.BlockChTwoSum
