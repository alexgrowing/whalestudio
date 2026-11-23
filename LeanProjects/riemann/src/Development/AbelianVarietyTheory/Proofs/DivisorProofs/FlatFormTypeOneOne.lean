import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.FlatTypeOneOne

theorem herm_I_smul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    herm τ (Complex.I • v) (Complex.I • w) = herm τ v w := by
  simp only [herm, Matrix.smul_vecMul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← mul_assoc]; simp [Complex.conj_I]

theorem herm_im {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    (herm τ v w).im = ((fun i => (v i).im) ᵥ* (τ.map Complex.im)⁻¹) ⬝ᵥ (fun i => (w i).re) -
      ((fun i => (v i).re) ᵥ* (τ.map Complex.im)⁻¹) ⬝ᵥ (fun i => (w i).im) := by
  simp only [herm, dotProduct, Matrix.vecMul, Finset.sum_mul, Complex.im_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem per_re {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (u : Fl g) :
    (fun i => (per τ u i).re) =
      (fun i => u (Sum.inl i)) ᵥ* τ.map Complex.re + fun i => u (Sum.inr i) := by
  funext j; simp [per, Matrix.vecMul, dotProduct, Complex.re_sum]

theorem per_im {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (u : Fl g) :
    (fun i => (per τ u i).im) = (fun i => u (Sum.inl i)) ᵥ* τ.map Complex.im := by
  funext j; simp [per, Matrix.vecMul, dotProduct, Complex.im_sum]

theorem per_flatOf {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : GlobalTheory.IsSiegel τ)
    (z : Fin g → ℂ) : per τ (flatOf τ z) = z := by
  have hu : IsUnit (τ.map Complex.im).det := hτ.2.det_pos.ne'.isUnit
  have hY : (τ.map Complex.im)⁻¹ * τ.map Complex.im = 1 := Matrix.nonsing_inv_mul _ hu
  have hr := per_re τ (flatOf τ z)
  have hi := per_im τ (flatOf τ z)
  simp only [flatOf, Sum.elim_inl, Sum.elim_inr, add_sub_cancel, Matrix.vecMul_vecMul, hY,
    Matrix.vecMul_one] at hr hi ⊢
  funext j
  exact Complex.ext (congrFun hr j) (congrFun hi j)

theorem riem_eq_herm {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : GlobalTheory.IsSiegel τ) (x y : Fl g) :
    riem x y = -(herm τ (per τ x) (per τ y)).im := by
  have hu : IsUnit (τ.map Complex.im).det := hτ.2.det_pos.ne'.isUnit
  have hYi : τ.map Complex.im * (τ.map Complex.im)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hiY : (τ.map Complex.im)⁻¹ * τ.map Complex.im = 1 := Matrix.nonsing_inv_mul _ hu
  have hYs : (τ.map Complex.im)ᵀ = τ.map Complex.im := by
    rw [← Matrix.transpose_map, hτ.1.eq]
  have hXs : (τ.map Complex.re)ᵀ = τ.map Complex.re := by
    rw [← Matrix.transpose_map, hτ.1.eq]
  have T2 : ∀ u p' : Fin g → ℝ,
      (u ᵥ* (τ.map Complex.im)⁻¹) ⬝ᵥ (p' ᵥ* τ.map Complex.im) = u ⬝ᵥ p' := by
    intro u p'
    rw [← Matrix.mulVec_transpose (τ.map Complex.im) p', Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, hYs, hiY, Matrix.vecMul_one]
  have TX : ∀ p p' : Fin g → ℝ,
      p ⬝ᵥ (p' ᵥ* τ.map Complex.re) = (p ᵥ* τ.map Complex.re) ⬝ᵥ p' := by
    intro p p'
    rw [← Matrix.mulVec_transpose (τ.map Complex.re) p', Matrix.dotProduct_mulVec, hXs]
  rw [herm_im, per_re, per_re, per_im, per_im, T2, Matrix.vecMul_vecMul, hYi, Matrix.vecMul_one,
    dotProduct_add, add_dotProduct, TX]
  simp only [riem, dotProduct, Finset.sum_sub_distrib]
  ring

section Family

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem per_dflat_I {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ)
    {P : Pt E g} (hP : P ∈ cov B g) (t : Pt E g) :
    per (τ P.1) (dflat τ P (Complex.I • t)) = Complex.I • per (τ P.1) (dflat τ P t) := by
  by_cases hd : DifferentiableAt ℝ (flat τ) P
  swap
  · funext j
    simp [dflat, fderiv_zero_of_not_differentiableAt hd, per, Matrix.vecMul, dotProduct]
  have hF : HasFDerivAt (flat τ) (dflat τ P) P := hd.hasFDerivAt
  have hb : P.1 ∈ B := hP.1
  have hFk : ∀ k, HasFDerivAt (fun Q => (flat τ Q k : ℂ))
      (Complex.ofRealCLM.comp ((ContinuousLinearMap.proj k).comp (dflat τ P))) P :=
    fun k => Complex.ofRealCLM.hasFDerivAt.comp P (hasFDerivAt_pi'.1 hF k)
  have hτd : ∀ i j, HasFDerivAt (fun Q : Pt E g => τ Q.1 i j)
      (((fderiv ℂ (fun b => τ b i j) P.1).restrictScalars ℝ).comp
        (ContinuousLinearMap.fst ℝ E (Fin g → ℂ))) P := by
    intro i j
    have h1 : DifferentiableAt ℂ (fun b => τ b i j) P.1 :=
      (hτ.2.1 i j).differentiableAt (hτ.1.mem_nhds hb)
    exact (h1.hasFDerivAt.restrictScalars ℝ).comp P hasFDerivAt_fst
  funext j
  have hφ := (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hFk (Sum.inl i)).fun_mul (hτd i j)).fun_add (hFk (Sum.inr j))
  have heq : (fun Q : Pt E g => Q.2 j) =ᶠ[nhds P] fun Q : Pt E g =>
      (∑ i, (flat τ Q (Sum.inl i) : ℂ) * τ Q.1 i j) + (flat τ Q (Sum.inr j) : ℂ) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hτ.1.mem_nhds hb)] with Q hQ
    have := congrFun (per_flatOf (hτ.2.2 _ hQ) Q.2) j
    simpa [per, flat, Matrix.vecMul, dotProduct] using this.symm
  have hsnd : HasFDerivAt (fun Q : Pt E g => Q.2 j)
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ E (Fin g → ℂ))) P :=
    hasFDerivAt_pi'.1 hasFDerivAt_snd j
  have huniq := (hφ.congr_of_eventuallyEq heq).unique hsnd
  have h1 := congrArg (fun D => D t) huniq
  have h2 := congrArg (fun D => D (Complex.I • t)) huniq
  simp [Finset.sum_add_distrib] at h1 h2
  simp [per, Matrix.vecMul, dotProduct]
  have e : ∀ s : Pt E g, ∑ x, ((dflat τ P s (Sum.inl x) : ℝ) : ℂ) * τ P.1 x j =
      ∑ i, τ P.1 i j * ((dflat τ P s (Sum.inl i) : ℝ) : ℂ) :=
    fun s => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp only [mul_left_comm _ Complex.I, ← Finset.mul_sum] at h2
  rw [e, e]
  linear_combination h2 - Complex.I * h1

end Family

theorem om0_I_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) :
    ∀ P ∈ cov B g, ∀ v w : Pt E g,
      om0 τ P ![Complex.I • v, Complex.I • w] = om0 τ P ![v, w] := by
  intro P hP v w
  have hs := hτ.2.2 P.1 hP.1
  have key : ∀ a b : Pt E g, om0 τ P ![a, b] = riem (dflat τ P a) (dflat τ P b) := fun a b => rfl
  rw [key, key, riem_eq_herm hs, riem_eq_herm hs, per_dflat_I hτ hP, per_dflat_I hτ hP,
    herm_I_smul]

end GlobalTheory.FlatTypeOneOne
