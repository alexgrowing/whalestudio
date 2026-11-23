import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.FlatFibre

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem det_differentiableAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    {M : F → Matrix (Fin n) (Fin n) ℝ} {x : F}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) :
    DifferentiableAt ℝ (fun y => (M y).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine DifferentiableAt.const_mul ?_ _
  have h' : ∀ i, DifferentiableAt ℝ (fun y => M y (σ i) i) x := fun i => hM _ _
  first
  | fun_prop
  | exact DifferentiableAt.finset_prod (fun i _ => h' i)

theorem inv_entry_differentiableAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    {M : F → Matrix (Fin n) (Fin n) ℝ} {x : F}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) (hdet : (M x).det ≠ 0) (i j : Fin n) :
    DifferentiableAt ℝ (fun y => (M y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  refine DifferentiableAt.mul ((det_differentiableAt hM).inv hdet) ?_
  refine det_differentiableAt fun k l => ?_
  by_cases hk : k = j
  · subst hk
    simp only [Matrix.updateRow_self]
    exact differentiableAt_const _
  · simp only [Matrix.updateRow_ne hk]
    exact hM k l

theorem flat_differentiableAt {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) {P : Pt E g} (hP : P ∈ cov B g) :
    DifferentiableAt ℝ (flat τ) P := by
  have hτe : ∀ i j, DifferentiableAt ℝ (fun Q : Pt E g => τ Q.1 i j) P := fun i j =>
    (((hτ.2.1 i j).differentiableAt (hτ.1.mem_nhds hP.1)).restrictScalars ℝ).comp P
      differentiableAt_fst
  have hre : ∀ i j, DifferentiableAt ℝ (fun Q : Pt E g => (τ Q.1).map Complex.re i j) P :=
    fun i j => Complex.reCLM.differentiableAt.comp P (hτe i j)
  have him : ∀ i j, DifferentiableAt ℝ (fun Q : Pt E g => (τ Q.1).map Complex.im i j) P :=
    fun i j => Complex.imCLM.differentiableAt.comp P (hτe i j)
  have hdet : ((τ P.1).map Complex.im).det ≠ 0 := (hτ.2.2 P.1 hP.1).2.det_pos.ne'
  have hinv := inv_entry_differentiableAt him hdet
  have hzre : ∀ i, DifferentiableAt ℝ (fun Q : Pt E g => (Q.2 i).re) P := fun i =>
    Complex.reCLM.differentiableAt.comp P
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g => ℂ) i).differentiableAt.comp P
        differentiableAt_snd)
  have hzim : ∀ i, DifferentiableAt ℝ (fun Q : Pt E g => (Q.2 i).im) P := fun i =>
    Complex.imCLM.differentiableAt.comp P
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g => ℂ) i).differentiableAt.comp P
        differentiableAt_snd)
  have hp : ∀ i, DifferentiableAt ℝ
      (fun Q : Pt E g => ((fun k => (Q.2 k).im) ᵥ* ((τ Q.1).map Complex.im)⁻¹) i) P := by
    intro i
    simp only [Matrix.vecMul, dotProduct]
    exact DifferentiableAt.fun_sum fun k _ => (hzim k).mul (hinv k i)
  rw [differentiableAt_pi]
  rintro (i | i)
  · exact hp i
  · show DifferentiableAt ℝ (fun Q : Pt E g => (Q.2 i).re -
      (((fun k => (Q.2 k).im) ᵥ* ((τ Q.1).map Complex.im)⁻¹) ᵥ* (τ Q.1).map Complex.re) i) P
    refine (hzre i).sub ?_
    simp only [Matrix.vecMul, dotProduct] at hp ⊢
    exact DifferentiableAt.fun_sum fun k _ => (hp k).mul (hre k i)

def flatOfLin (T : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] Fl g where
  toFun := flatOf T
  map_add' x y := by
    funext k
    rcases k with i | i <;>
      simp [flatOf, Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul] <;> ring
  map_smul' c x := by
    funext k
    rcases k with i | i
    · simp [flatOf, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    · simp [flatOf, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
      simp only [mul_sub, Finset.mul_sum]

theorem dflat_vert {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) {P : Pt E g} (hP : P ∈ cov B g) (v : Fin g → ℂ) :
    dflat τ P (0, v) = flatOf (τ P.1) v := by
  have hd := flat_differentiableAt hτ hP
  let L : (Fin g → ℂ) →L[ℝ] Fl g := LinearMap.toContinuousLinearMap (flatOfLin (τ P.1))
  have h1 : HasFDerivAt (fun z => flat τ (P.1, z)) L P.2 := by
    have : (fun z => flat τ (P.1, z)) = L := by funext z; rfl
    rw [this]
    exact L.hasFDerivAt
  have hin : HasFDerivAt (fun z : Fin g → ℂ => (P.1, z))
      ((0 : (Fin g → ℂ) →L[ℝ] E).prod (ContinuousLinearMap.id ℝ (Fin g → ℂ))) P.2 :=
    (hasFDerivAt_const P.1 P.2).prodMk (hasFDerivAt_id P.2)
  have hd' : DifferentiableAt ℝ (flat τ) (P.1, P.2) := hd
  have h2 := hd'.hasFDerivAt.comp P.2 hin
  have h3 := congrArg (fun T => T v) (h1.unique h2)
  simpa [dflat, L, flatOfLin] using h3.symm

theorem riem_flatOf (T : Matrix (Fin g) (Fin g) ℂ) (hT : T.IsSymm) (v w : Fin g → ℂ) :
    riem (flatOf T v) (flatOf T w) = -(herm T v w).im := by
  set Yi := (T.map Complex.im)⁻¹ with hYi
  set X := T.map Complex.re with hX
  have sYi : Yiᵀ = Yi := (hT.map Complex.im).inv
  have sX : Xᵀ = X := hT.map Complex.re
  set a : Fin g → ℝ := fun i => (v i).im
  set b : Fin g → ℝ := fun i => (v i).re
  set a' : Fin g → ℝ := fun i => (w i).im
  set b' : Fin g → ℝ := fun i => (w i).re
  have hr : ∀ (p q p' q' : Fin g → ℝ),
      riem (Sum.elim p q) (Sum.elim p' q') = q ⬝ᵥ p' - p ⬝ᵥ q' := by
    intro p q p' q'
    simp [riem, dotProduct, Finset.sum_sub_distrib]
  have hu_re : ∀ i, ((v ᵥ* Yi.map (fun t : ℝ => (t : ℂ))) i).re = (b ᵥ* Yi) i := by
    intro i
    simp [Matrix.vecMul, dotProduct, Complex.re_sum, b]
  have hu_im : ∀ i, ((v ᵥ* Yi.map (fun t : ℝ => (t : ℂ))) i).im = (a ᵥ* Yi) i := by
    intro i
    simp [Matrix.vecMul, dotProduct, Complex.im_sum, a]
  have hh : (herm T v w).im = (a ᵥ* Yi) ⬝ᵥ b' - (b ᵥ* Yi) ⬝ᵥ a' := by
    simp only [herm, ← hYi]
    simp only [dotProduct, Complex.im_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, hu_re, hu_im, a', b']
    ring
  have e1 : (b ᵥ* Yi) ⬝ᵥ a' = b ⬝ᵥ (a' ᵥ* Yi) := by
    rw [← dotProduct_mulVec, ← Matrix.vecMul_transpose, sYi]
  have e2 : ((a ᵥ* Yi) ᵥ* X) ⬝ᵥ (a' ᵥ* Yi) = (a ᵥ* Yi) ⬝ᵥ ((a' ᵥ* Yi) ᵥ* X) := by
    rw [← dotProduct_mulVec, ← Matrix.vecMul_transpose, sX]
  show riem (Sum.elim (a ᵥ* Yi) (b - (a ᵥ* Yi) ᵥ* X))
    (Sum.elim (a' ᵥ* Yi) (b' - (a' ᵥ* Yi) ᵥ* X)) = _
  rw [hr, hh, sub_dotProduct, dotProduct_sub, e1, e2, dotProduct_comm b (a' ᵥ* Yi)]
  ring

theorem herm_self_re_pos (T : Matrix (Fin g) (Fin g) ℂ) (hT : (T.map Complex.im).PosDef)
    {v : Fin g → ℂ} (hv : v ≠ 0) : 0 < (herm T v v).re := by
  set Yi := (T.map Complex.im)⁻¹ with hYi
  have hpd : Yi.PosDef := hT.inv
  set a : Fin g → ℝ := fun i => (v i).im
  set b : Fin g → ℝ := fun i => (v i).re
  have hu_re : ∀ i, ((v ᵥ* Yi.map (fun t : ℝ => (t : ℂ))) i).re = (b ᵥ* Yi) i := by
    intro i
    simp [Matrix.vecMul, dotProduct, Complex.re_sum, b]
  have hu_im : ∀ i, ((v ᵥ* Yi.map (fun t : ℝ => (t : ℂ))) i).im = (a ᵥ* Yi) i := by
    intro i
    simp [Matrix.vecMul, dotProduct, Complex.im_sum, a]
  have hh : (herm T v v).re = b ⬝ᵥ (Yi *ᵥ b) + a ⬝ᵥ (Yi *ᵥ a) := by
    rw [dotProduct_mulVec, dotProduct_mulVec, dotProduct_comm (b ᵥ* Yi),
      dotProduct_comm (a ᵥ* Yi)]
    simp only [herm, ← hYi]
    simp only [dotProduct, Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, hu_re, hu_im, a, b]
    ring
  have hnn : ∀ x : Fin g → ℝ, 0 ≤ x ⬝ᵥ (Yi *ᵥ x) := fun x => by
    simpa using hpd.posSemidef.dotProduct_mulVec_nonneg x
  rw [hh]
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      apply hv
      funext i
      apply Complex.ext
      · simpa [b] using congrFun hb i
      · simpa [a] using congrFun ha i
    have := hpd.dotProduct_mulVec_pos hb
    simp only [star_trivial] at this
    linarith [hnn a]
  · have := hpd.dotProduct_mulVec_pos ha
    simp only [star_trivial] at this
    linarith [hnn b]

theorem flat_fibre {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} :
    IsPeriodMap B τ →
      (∀ P ∈ cov B g, ∀ v w : Fin g → ℂ, om0 τ P ![(0, v), (0, w)] = -(herm (τ P.1) v w).im) ∧
      (∀ P ∈ cov B g, ∀ v : Fin g → ℂ, v ≠ 0 → 0 < om0 τ P ![(0, v), (0, Complex.I • v)]) := by
  intro hτ
  have key : ∀ P ∈ cov B g, ∀ v w : Fin g → ℂ,
      om0 τ P ![(0, v), (0, w)] = -(herm (τ P.1) v w).im := by
    intro P hP v w
    have h0 : om0 τ P ![(0, v), (0, w)] = riem (dflat τ P (0, v)) (dflat τ P (0, w)) := rfl
    rw [h0, dflat_vert hτ hP, dflat_vert hτ hP]
    exact riem_flatOf _ (hτ.2.2 P.1 hP.1).1 v w
  refine ⟨key, fun P hP v hv => ?_⟩
  rw [key P hP]
  have : herm (τ P.1) v (Complex.I • v) = -Complex.I * herm (τ P.1) v v := by
    simp only [herm, star_smul, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_I]
  rw [this]
  have hpos := herm_self_re_pos (τ P.1) (hτ.2.2 P.1 hP.1).2 hv
  simpa [Complex.mul_im] using hpos

end GlobalTheory.FlatFibre
