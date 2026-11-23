import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory.FlatVert

theorem differentiableAt_finset_prod_of {ι F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Finset ι) {f : ι → F → ℝ} {x : F} (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    DifferentiableAt ℝ (fun y => ∏ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem differentiableAt_det_of {n : Type} [Fintype n] [DecidableEq n] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {M : F → Matrix n n ℝ} {x : F}
    (h : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) :
    DifferentiableAt ℝ (fun y => (M y).det) x := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  exact (differentiableAt_finset_prod_of Finset.univ (f := fun i y => M y (σ i) i)
    fun i _ => h _ _).const_mul _

theorem differentiableAt_inv_of {n : Type} [Fintype n] [DecidableEq n] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {M : F → Matrix n n ℝ} {x : F}
    (h : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) (h0 : (M x).det ≠ 0) (i j : n) :
    DifferentiableAt ℝ (fun y => (M y)⁻¹ i j) x := by
  have hadj : DifferentiableAt ℝ (fun y => (M y).adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    refine differentiableAt_det_of fun k l => ?_
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact differentiableAt_const _
    · exact h _ _
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((differentiableAt_det_of h).inv h0).mul hadj

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

noncomputable def flatLin (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] Fl g where
  toFun := flatOf τ
  map_add' z w := by
    have him : (fun i => ((z + w) i).im) = (fun i => (z i).im) + fun i => (w i).im := by
      ext; simp
    have hre : (fun i => ((z + w) i).re) = (fun i => (z i).re) + fun i => (w i).re := by
      ext; simp
    simp only [flatOf, him, hre, Matrix.add_vecMul]
    funext k
    rcases k with i | i <;> simp <;> ring
  map_smul' c z := by
    have him : (fun i => ((c • z) i).im) = c • fun i => (z i).im := by
      ext; simp
    have hre : (fun i => ((c • z) i).re) = c • fun i => (z i).re := by
      ext; simp
    simp only [flatOf, him, hre, Matrix.smul_vecMul, RingHom.id_apply]
    funext k
    rcases k with i | i <;> simp <;> ring

theorem flatLin_apply (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    flatLin τ z = flatOf τ z := rfl

theorem differentiableAt_flat {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) {b : E} (hb : b ∈ B) (z : Fin g → ℂ) :
    DifferentiableAt ℝ (flat τ) (b, z) := by
  have hent : ∀ i j, DifferentiableAt ℝ (fun P : Pt E g => τ P.1 i j) (b, z) := fun i j => by
    have h1 : DifferentiableAt ℝ (fun b => τ b i j) b :=
      ((hτ.2.1 i j).differentiableAt (hτ.1.mem_nhds hb)).restrictScalars ℝ
    have h2 : DifferentiableAt ℝ (fun P : Pt E g => P.1) (b, z) := differentiableAt_fst
    exact h1.comp (b, z) h2
  have him : ∀ i j, DifferentiableAt ℝ (fun P : Pt E g => ((τ P.1).map Complex.im) i j) (b, z) :=
    fun i j => by
      simp only [Matrix.map_apply]
      exact Complex.imCLM.differentiableAt.comp _ (hent i j)
  have hre : ∀ i j, DifferentiableAt ℝ (fun P : Pt E g => ((τ P.1).map Complex.re) i j) (b, z) :=
    fun i j => by
      simp only [Matrix.map_apply]
      exact Complex.reCLM.differentiableAt.comp _ (hent i j)
  have hdet : ((τ b).map Complex.im).det ≠ 0 := ((hτ.2.2 b hb).2.det_pos).ne'
  have hinv := differentiableAt_inv_of (M := fun P : Pt E g => (τ P.1).map Complex.im) him hdet
  have hzi : ∀ j, DifferentiableAt ℝ (fun P : Pt E g => (P.2 j).im) (b, z) := fun j => by fun_prop
  have hzr : ∀ j, DifferentiableAt ℝ (fun P : Pt E g => (P.2 j).re) (b, z) := fun j => by fun_prop
  have hp : ∀ i, DifferentiableAt ℝ (fun P : Pt E g =>
      ((fun j => (P.2 j).im) ᵥ* ((τ P.1).map Complex.im)⁻¹) i) (b, z) := fun i => by
    simp only [Matrix.vecMul, dotProduct]
    exact DifferentiableAt.fun_sum fun j _ => (hzi j).mul (hinv j i)
  rw [differentiableAt_pi]
  rintro (i | i)
  · exact hp i
  · simp only [flat, flatOf, Sum.elim_inr, Pi.sub_apply]
    refine (hzr i).sub ?_
    simp only [Matrix.vecMul, dotProduct] at hp ⊢
    exact DifferentiableAt.fun_sum fun k _ => (hp k).mul (hre k i)

theorem dflat_vert : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ b ∈ B, ∀ z v : Fin g → ℂ,
    dflat τ (b, z) ((0 : E), v) = flatOf (τ b) v := by
  intro g E _ _ B τ hτ b hb z v
  have hd := differentiableAt_flat hτ hb z
  have hc : HasFDerivAt (fun w : Fin g → ℂ => ((b, w) : Pt E g))
      ((0 : (Fin g → ℂ) →L[ℝ] E).prod (ContinuousLinearMap.id ℝ _)) z :=
    (hasFDerivAt_const b z).prodMk (hasFDerivAt_id z)
  have h2 : HasFDerivAt (flatOf (τ b))
      ((fderiv ℝ (flat τ) (b, z)).comp
        ((0 : (Fin g → ℂ) →L[ℝ] E).prod (ContinuousLinearMap.id ℝ _))) z :=
    hd.hasFDerivAt.comp z hc
  have h3 : HasFDerivAt (flatOf (τ b)) (LinearMap.toContinuousLinearMap (flatLin (τ b))) z :=
    (LinearMap.toContinuousLinearMap (flatLin (τ b))).hasFDerivAt
  have e := congrArg (fun L : (Fin g → ℂ) →L[ℝ] Fl g => L v) (h2.unique h3)
  simpa [dflat, flatLin_apply] using e

end GlobalTheory.FlatVert
