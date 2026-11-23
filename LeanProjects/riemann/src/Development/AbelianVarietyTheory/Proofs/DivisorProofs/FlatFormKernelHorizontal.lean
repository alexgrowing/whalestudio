import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.FlatKernel

variable {g : ℕ}

lemma per_im (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) :
    (fun i => (per τ x i).im) = (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.im := by
  ext i
  simp [per, Matrix.vecMul, dotProduct, Complex.im_sum]

lemma per_re (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) :
    (fun i => (per τ x i).re) =
      (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.re + fun i => x (Sum.inr i) := by
  ext i
  simp [per, Matrix.vecMul, dotProduct, Complex.re_sum]

lemma flatOf_per {τ : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit (τ.map Complex.im).det) (x : Fl g) :
    flatOf τ (per τ x) = x := by
  have hi : (fun i => (per τ x i).im) ᵥ* (τ.map Complex.im)⁻¹ = fun i => x (Sum.inl i) := by
    rw [per_im, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ h, Matrix.vecMul_one]
  ext (i | i)
  · exact congrFun hi i
  · simp only [flatOf, Sum.elim_inr]
    rw [hi, per_re]
    simp

lemma per_flatOf {τ : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit (τ.map Complex.im).det)
    (z : Fin g → ℂ) : per τ (flatOf τ z) = z := by
  have hp : (fun i => flatOf τ z (Sum.inl i)) =
      (fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹ := rfl
  have hq : (fun i => flatOf τ z (Sum.inr i)) = (fun i => (z i).re) -
      ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹) ᵥ* τ.map Complex.re := rfl
  ext i
  apply Complex.ext
  · rw [show (per τ (flatOf τ z) i).re = _ from congrFun (per_re τ (flatOf τ z)) i, hp, hq]
    simp
  · rw [show (per τ (flatOf τ z) i).im = _ from congrFun (per_im τ (flatOf τ z)) i, hp,
      Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ h, Matrix.vecMul_one]

def flatL (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] Fl g where
  toFun := flatOf τ
  map_add' z w := by
    ext (i | i) <;> simp [flatOf, Matrix.vecMul, dotProduct, add_mul, Finset.sum_add_distrib] <;> ring
  map_smul' c z := by
    ext (i | i)
    · simp [flatOf, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    · simp only [flatOf, Sum.elim_inr, Pi.sub_apply, Pi.smul_apply, Matrix.vecMul, dotProduct,
        smul_eq_mul, Complex.smul_re, Complex.smul_im, Finset.mul_sum, mul_sub]
      refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by simp only [RingHom.id_apply]; ring

@[simp] lemma flatL_apply (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    flatL τ z = flatOf τ z := rfl

lemma diffAt_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {M : E → Matrix (Fin n) (Fin n) ℝ} {x : E}
    (h : ∀ a c, DifferentiableAt ℝ (fun b => M b a c) x) :
    DifferentiableAt ℝ (fun b => (M b).det) x := by
  simp only [Matrix.det_apply']
  fun_prop

lemma diffAt_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {M : E → Matrix (Fin n) (Fin n) ℝ} {x : E}
    (h : ∀ a c, DifferentiableAt ℝ (fun b => M b a c) x) (hx : (M x).det ≠ 0) (k i : Fin n) :
    DifferentiableAt ℝ (fun b => (M b)⁻¹ k i) x := by
  have e : (fun b => (M b)⁻¹ k i) =
      fun b => ((M b).det)⁻¹ * ((M b).updateRow i (Pi.single k 1)).det := by
    ext b
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  refine ((diffAt_det h).inv hx).mul (diffAt_det fun a c => ?_)
  by_cases hai : a = i
  · subst hai
    simp
  · simpa [Matrix.updateRow_ne hai] using h a c

theorem orth {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) :
    (∀ P ∈ cov B g, ∀ v : Pt E g, (∀ w : Fin g → ℂ, om0 τ P ![v, (0, w)] = 0) ↔
      dflat τ P v = 0) ∧
    (∀ P ∈ cov B g, (∀ v : Pt E g, dflat τ P v = 0 → dflat τ P (Complex.I • v) = 0) ∧
      ∀ u : E, ∃! w : Fin g → ℂ, dflat τ P (u, w) = 0) := by
  have key : ∀ P ∈ cov B g, (∀ w, dflat τ P (0, w) = flatOf (τ P.1) w) ∧
      (∀ x, flatOf (τ P.1) (per (τ P.1) x) = x) ∧ (∀ z, per (τ P.1) (flatOf (τ P.1) z) = z) ∧
      ∃ γ' : E →L[ℂ] (Fin g → ℂ), ∀ u, dflat τ P (u, γ' u) = 0 := by
    rintro ⟨b0, z0⟩ hP
    have hb : b0 ∈ B := hP.1
    have hunit : ∀ b ∈ B, IsUnit ((τ b).map Complex.im).det := fun b hb' =>
      isUnit_iff_ne_zero.2 (hτ.2.2 b hb').2.det_pos.ne'
    have hτd : ∀ i j, DifferentiableAt ℂ (fun b => τ b i j) b0 := fun i j =>
      (hτ.2.1 i j).differentiableAt (hτ.1.mem_nhds hb)
    have hY : ∀ i j, DifferentiableAt ℝ (fun b => ((τ b).map Complex.im) i j) b0 := fun i j =>
      Complex.imCLM.differentiableAt.comp b0 ((hτd i j).restrictScalars ℝ)
    have hX : ∀ i j, DifferentiableAt ℝ (fun b => ((τ b).map Complex.re) i j) b0 := fun i j =>
      Complex.reCLM.differentiableAt.comp b0 ((hτd i j).restrictScalars ℝ)
    have hYi : ∀ i j, DifferentiableAt ℝ (fun b => ((τ b).map Complex.im)⁻¹ i j) b0 :=
      diffAt_inv hY (hunit b0 hb).ne_zero
    have hflat : DifferentiableAt ℝ (flat τ) (b0, z0) := by
      have hYi' : ∀ i j, DifferentiableAt ℝ
          (fun Q : Pt E g => ((τ Q.1).map Complex.im)⁻¹ i j) (b0, z0) :=
        fun i j => DifferentiableAt.comp (g := fun b => ((τ b).map Complex.im)⁻¹ i j)
          (f := Prod.fst) (b0, z0) (hYi i j) differentiableAt_fst
      have hX' : ∀ i j, DifferentiableAt ℝ
          (fun Q : Pt E g => ((τ Q.1).map Complex.re) i j) (b0, z0) :=
        fun i j => DifferentiableAt.comp (g := fun b => ((τ b).map Complex.re) i j)
          (f := Prod.fst) (b0, z0) (hX i j) differentiableAt_fst
      have hzi : ∀ i, DifferentiableAt ℝ (fun Q : Pt E g => (Q.2 i).im) (b0, z0) := fun i =>
        Complex.imCLM.differentiableAt.comp _ (by fun_prop)
      have hzr : ∀ i, DifferentiableAt ℝ (fun Q : Pt E g => (Q.2 i).re) (b0, z0) := fun i =>
        Complex.reCLM.differentiableAt.comp _ (by fun_prop)
      rw [differentiableAt_pi]
      rintro (i | i)
      · show DifferentiableAt ℝ (fun Q : Pt E g =>
          ∑ k, (Q.2 k).im * ((τ Q.1).map Complex.im)⁻¹ k i) (b0, z0)
        exact DifferentiableAt.fun_sum fun k _ => (hzi k).mul (hYi' k i)
      · show DifferentiableAt ℝ (fun Q : Pt E g => (Q.2 i).re -
          ∑ k, (∑ l, (Q.2 l).im * ((τ Q.1).map Complex.im)⁻¹ l k) * ((τ Q.1).map Complex.re) k i)
          (b0, z0)
        exact (hzr i).sub (DifferentiableAt.fun_sum fun k _ =>
          (DifferentiableAt.fun_sum fun l _ => (hzi l).mul (hYi' l k)).mul (hX' k i))
    have hlin : ∀ w, dflat τ (b0, z0) (0, w) = flatOf (τ b0) w := by
      intro w
      have h1 : HasFDerivAt (fun z : Fin g → ℂ => ((b0, z) : Pt E g))
          (ContinuousLinearMap.inr ℝ E (Fin g → ℂ)) z0 :=
        hasFDerivAt_prodMk_right b0 z0
      have h2 := hflat.hasFDerivAt.comp z0 h1
      have h3 : HasFDerivAt (fun z : Fin g → ℂ => flat τ (b0, z))
          (LinearMap.toContinuousLinearMap (flatL (τ b0))) z0 :=
        (LinearMap.toContinuousLinearMap (flatL (τ b0))).hasFDerivAt
      have := congrArg (fun f => f w) (h2.unique h3)
      simpa [dflat] using this
    obtain ⟨γ, hγ⟩ : ∃ γ : E → (Fin g → ℂ), γ = fun b => per (τ b) (flatOf (τ b0) z0) := ⟨_, rfl⟩
    have hγd : DifferentiableAt ℂ γ b0 := by
      rw [hγ, differentiableAt_pi]
      intro i
      show DifferentiableAt ℂ (fun b => ∑ k, ((flatOf (τ b0) z0 (Sum.inl k) : ℝ) : ℂ) * τ b k i +
        ((flatOf (τ b0) z0 (Sum.inr i) : ℝ) : ℂ)) b0
      exact (DifferentiableAt.fun_sum fun k _ => (hτd k i).const_mul _).add_const _
    have hγ0 : γ b0 = z0 := by rw [hγ]; exact per_flatOf (hunit b0 hb) z0
    refine ⟨hlin, flatOf_per (hunit b0 hb), per_flatOf (hunit b0 hb), fderiv ℂ γ b0, fun u => ?_⟩
    have hΦ : HasFDerivAt (fun b => ((b, γ b) : Pt E g))
        ((ContinuousLinearMap.id ℝ E).prod ((fderiv ℂ γ b0).restrictScalars ℝ)) b0 :=
      (hasFDerivAt_id b0).prodMk (hγd.hasFDerivAt.restrictScalars ℝ)
    have hcomp : HasFDerivAt (fun b => flat τ (b, γ b)) ((dflat τ (b0, z0)).comp
        ((ContinuousLinearMap.id ℝ E).prod ((fderiv ℂ γ b0).restrictScalars ℝ))) b0 := by
      have : HasFDerivAt (flat τ) (dflat τ (b0, z0)) (b0, γ b0) := by
        rw [hγ0]; exact hflat.hasFDerivAt
      exact this.comp b0 hΦ
    have hconst : HasFDerivAt (fun b => flat τ (b, γ b)) (0 : E →L[ℝ] Fl g) b0 := by
      refine (hasFDerivAt_const (flatOf (τ b0) z0) b0).congr_of_eventuallyEq ?_
      filter_upwards [hτ.1.mem_nhds hb] with b hb'
      rw [hγ]
      exact flatOf_per (hunit b hb') _
    have := congrArg (fun f => f u) (hcomp.unique hconst)
    simpa using this
  refine ⟨fun P hP v => ?_, fun P hP => ?_⟩
  · obtain ⟨hlin, hsurj, -, -⟩ := key P hP
    have hom : ∀ w, om0 τ P ![v, (0, w)] = riem (dflat τ P v) (flatOf (τ P.1) w) := fun w => by
      rw [← hlin w]; rfl
    constructor
    · intro h
      have hr : ∀ y, riem (dflat τ P v) y = 0 := fun y => by
        have := h (per (τ P.1) y)
        rwa [hom, hsurj] at this
      ext (i | i)
      · have := hr (Pi.single (Sum.inr i) 1)
        simpa [riem, Pi.single_apply] using this
      · have := hr (Pi.single (Sum.inl i) 1)
        simpa [riem, Pi.single_apply] using this
    · intro h w
      rw [hom, h]
      simp [riem]
  · obtain ⟨hlin, -, hinj, γ', hγ'⟩ := key P hP
    have hsplit : ∀ u w, dflat τ P (u, w) = dflat τ P (u, 0) + flatOf (τ P.1) w := fun u w => by
      rw [← hlin, ← map_add]
      simp
    have huniq : ∀ u w, dflat τ P (u, w) = 0 → w = γ' u := fun u w h => by
      have h2 := hγ' u
      rw [hsplit] at h h2
      have e : flatOf (τ P.1) w = flatOf (τ P.1) (γ' u) := add_left_cancel (h.trans h2.symm)
      rw [← hinj w, e, hinj]
    refine ⟨fun v hv => ?_, fun u => ⟨γ' u, hγ' u, fun w hw => huniq u w hw⟩⟩
    obtain ⟨u, w⟩ := v
    obtain rfl := huniq u w hv
    have e : Complex.I • ((u, γ' u) : Pt E g) = (Complex.I • u, γ' (Complex.I • u)) := by
      rw [Prod.smul_mk, map_smul]
    rw [e]
    exact hγ' _

end GlobalTheory.FlatKernel
