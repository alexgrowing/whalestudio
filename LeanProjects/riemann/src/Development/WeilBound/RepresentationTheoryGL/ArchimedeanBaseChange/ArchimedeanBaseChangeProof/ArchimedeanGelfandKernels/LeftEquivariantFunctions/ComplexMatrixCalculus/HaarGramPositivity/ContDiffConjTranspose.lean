import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.ContDiffOnMatrixIff

noncomputable section

open Matrix
open scoped ContDiff Kronecker

namespace PositivityTheory.RgBcC.Cxe

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option linter.unusedSectionVars false

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem contDiffOn_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    {f g : E → Matrix ι ι ℂ} (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) : ContDiffOn ℝ ∞ (fun x => f x * g x) s := by
  rw [contDiffOn_matrix_iff] at hf hg ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hf i k).mul (hg k j)

theorem contDiffOn_kron {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    {f : E → Matrix ι ι ℂ} {g : E → Matrix κ κ ℂ} (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) :
    ContDiffOn ℝ ∞ (fun x => f x ⊗ₖ g x) s := by
  rw [contDiffOn_matrix_iff] at hf hg ⊢
  rintro ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.kroneckerMap_apply]
  exact (hf i k).mul (hg j l)

theorem contDiffOn_transpose {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    {f : E → Matrix ι ι ℂ} (hf : ContDiffOn ℝ ∞ f s) : ContDiffOn ℝ ∞ (fun x => (f x)ᵀ) s := by
  rw [contDiffOn_matrix_iff] at hf ⊢
  intro i j
  exact hf j i

theorem contDiff_conjTranspose : ContDiff ℝ ∞ (fun x : Matrix ι ι ℂ => xᴴ) := by
  rw [contDiff_matrix_iff]
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact Complex.conjCLE.contDiff.comp (contDiff_entry j i)

def cTL : Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => xᴴ, map_add' := fun x y => Matrix.conjTranspose_add x y,
      map_smul' := fun r x => by ext i j; simp [Matrix.conjTranspose_apply] }

@[simp] theorem cTL_apply (x : Matrix ι ι ℂ) : cTL x = xᴴ := rfl

def mulLL (S : Matrix κ κ ℂ) : Matrix κ κ ℂ →L[ℝ] Matrix κ κ ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => S * M, map_add' := fun M N => Matrix.mul_add S M N,
      map_smul' := fun r M => by ext i j; simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm] }

def mulRL (S : Matrix κ κ ℂ) : Matrix κ κ ℂ →L[ℝ] Matrix κ κ ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M * S, map_add' := fun M N => Matrix.add_mul M N S,
      map_smul' := fun r M => by ext i j; simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

@[simp] theorem mulLL_apply (S M : Matrix κ κ ℂ) : mulLL S M = S * M := rfl
@[simp] theorem mulRL_apply (S M : Matrix κ κ ℂ) : mulRL S M = M * S := rfl

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := isOpen_det_ne

theorem mem_GLs {x : Mat n} : x ∈ GLs n ↔ IsUnit x.det := by
  simp [GLs, isUnit_iff_ne_zero]

theorem contDiff_Mt : ContDiff ℝ ∞ (fun y : Mat n => Mt y) := by
  rw [contDiff_matrix_iff]
  intro p q
  simp only [Mt, cf, LinearMap.coe_mk, AddHom.coe_mk]
  refine Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp ?_)
  simp only [Matrix.trace]
  refine ContDiff.sum fun i _ => ?_
  have h : ContDiff ℝ ∞ (fun y : Mat n => y * hbM q * yᴴ * hbM p) := by
    have h1 : ContDiffOn ℝ ∞ (fun y : Mat n => y * hbM q * yᴴ * hbM p) Set.univ :=
      contDiffOn_mul (contDiffOn_mul (contDiffOn_mul contDiffOn_id contDiffOn_const) contDiff_conjTranspose.contDiffOn)
        contDiffOn_const
    exact contDiffOn_univ.mp h1
  exact (contDiff_matrix_iff _).mp h i i

theorem rm_inv (hR : RmLaws) (lam : Fin n → ℤ) {x : Mat n} (hx : IsUnit x.det) : Rm lam x⁻¹ = (Rm lam x)⁻¹ := by
  have hx' : IsUnit (x⁻¹).det := Matrix.isUnit_nonsing_inv_det x hx
  have h : Rm lam x⁻¹ * Rm lam x = 1 := by
    rw [← (hR n lam).2.1 _ _ hx' hx, Matrix.nonsing_inv_mul x hx, (hR n lam).1]
  exact (Matrix.inv_eq_left_inv h).symm

theorem rm_det (hR : RmLaws) (lam : Fin n → ℤ) {x : Mat n} (hx : IsUnit x.det) : (Rm lam x).det ≠ 0 := by
  have hx' : IsUnit (x⁻¹).det := Matrix.isUnit_nonsing_inv_det x hx
  have h : Rm lam x * Rm lam x⁻¹ = 1 := by
    rw [← (hR n lam).2.1 _ _ hx hx', Matrix.mul_nonsing_inv x hx, (hR n lam).1]
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem isUnit_det_cT {x : Mat n} (hx : IsUnit x.det) : IsUnit xᴴ.det := by
  rw [Matrix.det_conjTranspose]; exact hx.star

theorem rhoW_contDiffOn (hR : RmLaws) (lam : Fin n → ℤ) : ContDiffOn ℝ ∞ (rhoW lam) (GLs n) := by
  have hRm := (hR n lam).2.2
  have h1 : ContDiffOn ℝ ∞ (fun x : Mat n => (Rm lam x)⁻¹) (GLs n) :=
    contDiffOn_inv.comp hRm fun x hx => rm_det hR lam (mem_GLs.mp hx)
  have h2 : ContDiffOn ℝ ∞ (fun x : Mat n => Rm lam xᴴ) (GLs n) :=
    hRm.comp contDiff_conjTranspose.contDiffOn fun x hx => mem_GLs.mpr (isUnit_det_cT (mem_GLs.mp hx))
  exact contDiffOn_kron (contDiffOn_transpose h1) (contDiffOn_transpose h2)

theorem frame_zero_contDiffOn (hR : RmLaws) (hD : GamDer) (lam : Fin n → ℤ) : ContDiffOn ℝ ∞ (fr0 lam) (GLs n) := by
  have hg : ContDiff ℝ ∞ (gamM (n := n)) := (hD n).1.restrict_scalars ℝ
  have hinv : ContDiffOn ℝ ∞ (fun x : Mat n => (Mt x⁻¹)ᵀ) (GLs n) :=
    contDiffOn_transpose (contDiff_Mt.comp_contDiffOn contDiffOn_inv)
  exact contDiffOn_kron (hg.comp_contDiffOn hinv) (rhoW_contDiffOn hR lam)

theorem fr0Laws_of (hR : RmLaws) (hG : GamMul) (hM : MtLaws) (hD : GamDer) : MatrixFrechetDerivativeAtZeroLaws := by
  intro n lam
  refine ⟨?_, ?_, frame_zero_contDiffOn hR hD lam⟩
  · simp only [fr0, rhoW, inv_one, (hM n).1, Matrix.transpose_one, (hG n).1, (hR n lam).1, Matrix.conjTranspose_one,
      Matrix.one_kronecker_one]
  · intro x y hx hy
    have hxy := (hR n lam).2.1 x y hx hy
    have hyx := (hR n lam).2.1 yᴴ xᴴ (isUnit_det_cT hy) (isUnit_det_cT hx)
    simp only [fr0, rhoW]
    rw [Matrix.mul_inv_rev, (hM n).2.1, Matrix.transpose_mul, (hG n).2, Matrix.conjTranspose_mul, hxy, hyx,
      Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

theorem swap_kron (lam : Fin n → ℤ) (A B : Matrix (Jd n lam) (Jd n lam) ℂ) :
    swapJ lam * (A ⊗ₖ B) = (B ⊗ₖ A) * swapJ lam := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, swapJ, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

theorem swap_swap (lam : Fin n → ℤ) : swapJ lam * swapJ lam = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, swapJ, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, ite_and, Matrix.one_apply,
    Prod.mk.injEq]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  by_cases h1 : i = k <;> by_cases h2 : j = l <;> simp [h1, h2, eq_comm]

theorem swap_cT (lam : Fin n → ℤ) : (swapJ lam)ᴴ = swapJ lam := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.conjTranspose_apply, swapJ]
  by_cases h : k = j ∧ l = i
  · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩]; simp
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2.symm, h'.1.symm⟩]; simp

theorem trace_kron_swap (lam : Fin n → ℤ) (A B : Matrix (Jd n lam) (Jd n lam) ℂ) :
    ((A ⊗ₖ B) * swapJ lam).trace = (A * B).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, swapJ, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem swap_rhoW (hR : RmLaws) (lam : Fin n → ℤ) {x : Mat n} (hx : IsUnit x.det) :
    swapJ lam * rhoW lam (xᴴ)⁻¹ = rhoW lam x * swapJ lam := by
  have hxc := isUnit_det_cT hx
  have e1 : ((xᴴ)⁻¹)ᴴ = x⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]
  have e2 : (Rm lam (xᴴ)⁻¹)⁻¹ = Rm lam xᴴ := by rw [rm_inv hR lam hxc, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (rm_det hR lam hxc))]
  simp only [rhoW]
  rw [e1, e2, rm_inv hR lam hx, swap_kron]

theorem swapLaws_of (hR : RmLaws) : SwapLaws := by
  intro n lam
  refine ⟨swap_swap lam, ?_, fun x hx => swap_rhoW hR lam hx, ?_, trace_kron_swap lam⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, swap_cT, swap_swap]
  · intro X hXh0
    have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
    have hd : DifferentiableAt ℝ (rhoW lam) 1 :=
      ((rhoW_contDiffOn hR lam).contDiffAt (isOpen_GLs.mem_nhds h1)).differentiableAt (by simp)
    set D := fderiv ℝ (rhoW lam) 1
    have hD : HasFDerivAt (rhoW lam) D 1 := hd.hasFDerivAt
    have hθ : HasFDerivAt (fun x : Mat n => (xᴴ)⁻¹) ((-ContinuousLinearMap.id ℝ (Mat n)).comp cTL) 1 := by
      have h' : HasFDerivAt (fun x : Mat n => x⁻¹) (-ContinuousLinearMap.id ℝ (Mat n)) (cTL (1 : Mat n)) := by
        rw [cTL_apply, Matrix.conjTranspose_one]; exact hasFDerivAt_inv_one
      exact h'.comp (1 : Mat n) (cTL.hasFDerivAt (x := (1 : Mat n)))
    have hF : HasFDerivAt (fun x : Mat n => swapJ lam * rhoW lam (xᴴ)⁻¹)
        ((mulLL (swapJ lam)).comp (D.comp ((-ContinuousLinearMap.id ℝ (Mat n)).comp cTL))) 1 := by
      have hc : HasFDerivAt (fun x : Mat n => rhoW lam (xᴴ)⁻¹) (D.comp ((-ContinuousLinearMap.id ℝ (Mat n)).comp cTL)) 1 := by
        have e : (((1 : Mat n))ᴴ)⁻¹ = 1 := by simp
        have hD' : HasFDerivAt (rhoW lam) D (((1 : Mat n))ᴴ)⁻¹ := by rw [e]; exact hD
        exact hD'.comp (1 : Mat n) hθ
      exact (mulLL (swapJ lam)).hasFDerivAt.comp (1 : Mat n) hc
    have hG : HasFDerivAt (fun x : Mat n => rhoW lam x * swapJ lam) ((mulRL (swapJ lam)).comp D) 1 :=
      (mulRL (swapJ lam)).hasFDerivAt.comp (1 : Mat n) hD
    have hev : (fun x : Mat n => swapJ lam * rhoW lam (xᴴ)⁻¹) =ᶠ[nhds 1] fun x => rhoW lam x * swapJ lam := by
      filter_upwards [isOpen_GLs.mem_nhds h1] with x hx
      exact swap_rhoW hR lam (mem_GLs.mp hx)
    have huniq := hF.unique (hG.congr_of_eventuallyEq hev)
    have hX := congrArg (fun T : Mat n →L[ℝ] Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ => T X) huniq
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, cTL_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, mulLL_apply, mulRL_apply, map_neg] at hX
    rw [hXh0.eq] at hX
    rw [← hX, neg_neg]

end PositivityTheory.RgBcC.Cxe
