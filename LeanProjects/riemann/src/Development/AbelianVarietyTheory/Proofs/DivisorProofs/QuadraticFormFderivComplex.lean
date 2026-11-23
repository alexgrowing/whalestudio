import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReQuad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapFlatDerivative
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.ThetaMet
open scoped Real ContDiff

noncomputable section
namespace GlobalTheory.ThetaMetDc

theorem alg_identity {g : ℕ} (p y a b r dq : Fin g → ℝ) (Y X x' : Fin g → Fin g → ℝ)
    (hY : ∀ i j, Y i j = Y j i) (hX : ∀ i j, X i j = X j i)
    (hy : ∀ k, y k = ∑ j, p j * Y j k)
    (hd : ∀ k, ∑ j, (p j * x' j k + Y j k * a j) = r k)
    (hc : ∀ k, r k = ∑ j, (p j * x' j k + X j k * b j) + dq k) :
    ∑ i, (p i * r i + y i * a i) =
      ∑ i, (p i * ∑ k, (X i k * b k + p k * x' i k) + (∑ k, X i k * p k) * b i) +
        2 * ∑ i, p i * dq i := by
  have hd' : ∀ j, ∑ i, Y i j * a i = r j - ∑ i, p i * x' i j := fun j => by
    rw [← hd j, Finset.sum_add_distrib]; ring
  have e1 : ∑ i, y i * a i = ∑ j, p j * r j - ∑ j, ∑ i, p j * (p i * x' i j) := by
    calc ∑ i, y i * a i = ∑ i, ∑ j, p j * Y j i * a i :=
          Finset.sum_congr rfl fun i _ => by rw [hy, Finset.sum_mul]
      _ = ∑ j, ∑ i, p j * (Y i j * a i) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hY]; ring
      _ = ∑ j, p j * (r j - ∑ i, p i * x' i j) :=
          Finset.sum_congr rfl fun j _ => by rw [← Finset.mul_sum, hd' j]
      _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  have e2 : ∑ j, p j * r j = ∑ j, ∑ i, p j * (p i * x' i j) + ∑ j, ∑ i, p j * (X i j * b i) +
      ∑ j, p j * dq j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have eA : ∑ j, ∑ i, p j * (p i * x' i j) = ∑ i, ∑ k, p i * (p k * x' i k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have eC : ∑ j, ∑ i, p j * (X i j * b i) = ∑ i, ∑ k, p i * (X i k * b k) :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hX]
  have e3 : ∑ i, (∑ k, X i k * p k) * b i = ∑ i, ∑ k, p i * (X i k * b k) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by rw [hX]; ring
  have e4 : ∑ i, p i * ∑ k, (X i k * b k + p k * x' i k) =
      ∑ i, ∑ k, p i * (X i k * b k) + ∑ i, ∑ k, p i * (p k * x' i k) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e3, e4, e2, eA, eC]
  ring

theorem dc_identity : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ P ∈ cov B g, ∀ v : Pt E g, fderiv ℝ (quad τ) P (Complex.I • v) = fderiv ℝ (reQuad τ) P v + 2 * ∑ i, flat τ P (Sum.inl i) * dflat τ P v (Sum.inr i) := by
  intro g E _ _ B τ hτ P hP v
  obtain ⟨b, z⟩ := P
  have hb : b ∈ B := hP.1
  set F' := fderiv ℝ (flat τ) (b, z) with hF'
  have hF : HasFDerivAt (flat τ) F' (b, z) :=
    (GlobalTheory.FlatVert.differentiableAt_flat hτ hb z).hasFDerivAt
  have hpd : ∀ i, HasFDerivAt (fun Q : Pt E g => flat τ Q (Sum.inl i))
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g ⊕ Fin g => ℝ) (Sum.inl i)).comp F') (b, z) := by
    intro i
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g ⊕ Fin g => ℝ) (Sum.inl i)).hasFDerivAt.comp (b, z) hF
    exact this
  have hqd : ∀ i, HasFDerivAt (fun Q : Pt E g => flat τ Q (Sum.inr i))
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g ⊕ Fin g => ℝ) (Sum.inr i)).comp F') (b, z) := by
    intro i
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g ⊕ Fin g => ℝ) (Sum.inr i)).hasFDerivAt.comp (b, z) hF
    exact this
  set L : Fin g → Fin g → (E →L[ℂ] ℂ) := fun j k => fderiv ℂ (fun b => τ b j k) b with hL
  have hLd : ∀ j k, HasFDerivAt (fun b => τ b j k) (L j k) b := fun j k =>
    ((hτ.2.1 j k).differentiableAt (hτ.1.mem_nhds hb)).hasFDerivAt
  have hTd : ∀ j k, HasFDerivAt (fun Q : Pt E g => τ Q.1 j k)
      (((L j k).restrictScalars ℝ).comp (ContinuousLinearMap.fst ℝ E (Fin g → ℂ))) (b, z) := by
    intro j k
    have h1 : HasFDerivAt (fun b => τ b j k) ((L j k).restrictScalars ℝ) b := (hLd j k).restrictScalars ℝ
    have h2 : HasFDerivAt (fun Q : Pt E g => Q.1) (ContinuousLinearMap.fst ℝ E (Fin g → ℂ)) (b, z) :=
      hasFDerivAt_fst
    have := h1.comp (b, z) h2
    exact this
  have hYd : ∀ j k, HasFDerivAt (fun Q : Pt E g => (τ Q.1 j k).im)
      (Complex.imCLM.comp (((L j k).restrictScalars ℝ).comp
        (ContinuousLinearMap.fst ℝ E (Fin g → ℂ)))) (b, z) := by
    intro j k
    have := Complex.imCLM.hasFDerivAt.comp (b, z) (hTd j k)
    exact this
  have hXd : ∀ j k, HasFDerivAt (fun Q : Pt E g => (τ Q.1 j k).re)
      (Complex.reCLM.comp (((L j k).restrictScalars ℝ).comp
        (ContinuousLinearMap.fst ℝ E (Fin g → ℂ)))) (b, z) := by
    intro j k
    have := Complex.reCLM.hasFDerivAt.comp (b, z) (hTd j k)
    exact this
  set Sz : Fin g → (Pt E g →L[ℝ] ℂ) := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g => ℂ) i).comp
      (ContinuousLinearMap.snd ℝ E (Fin g → ℂ)) with hSz
  have hzd : ∀ i, HasFDerivAt (fun Q : Pt E g => Q.2 i) (Sz i) (b, z) := fun i =>
    (Sz i).hasFDerivAt
  have hyd : ∀ i, HasFDerivAt (fun Q : Pt E g => (Q.2 i).im) (Complex.imCLM.comp (Sz i)) (b, z) := by
    intro i
    have := Complex.imCLM.hasFDerivAt.comp (b, z) (hzd i)
    exact this
  have hrd : ∀ i, HasFDerivAt (fun Q : Pt E g => (Q.2 i).re) (Complex.reCLM.comp (Sz i)) (b, z) := by
    intro i
    have := Complex.reCLM.hasFDerivAt.comp (b, z) (hzd i)
    exact this
  have hquad : quad τ = fun Q => ∑ i, flat τ Q (Sum.inl i) * (Q.2 i).im := by
    funext Q
    simp only [quad, flat, flatOf, Sum.elim_inl]
    rw [Matrix.dotProduct_mulVec, dotProduct]
  have hre : reQuad τ = fun Q => ∑ i, flat τ Q (Sum.inl i) *
      ∑ k, (τ Q.1 i k).re * flat τ Q (Sum.inl k) := by
    funext Q
    simp [reQuad, dotProduct, Matrix.mulVec]
  have hQd := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (hpd i).fun_mul (hyd i)
  have hRd := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hpd i).fun_mul (HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => (hXd i k).fun_mul (hpd k))
  rw [hquad, hre, hQd.fderiv, hRd.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, hSz, Complex.imCLM_apply, Complex.reCLM_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_restrictScalars', Prod.smul_fst,
    Prod.smul_snd, Pi.smul_apply, map_smul]

  have hsym : ∀ i j, τ b i j = τ b j i := fun i j => ((hτ.2.2 b hb).1.apply i j).symm
  have heq : ∀ k, (fun Q : Pt E g => ∑ j, flat τ Q (Sum.inl j) * (τ Q.1 j k).im) =ᶠ[nhds (b, z)]
      fun Q => (Q.2 k).im := by
    intro k
    filter_upwards [(hτ.1.preimage continuous_fst).mem_nhds hb] with Q hQ
    have hu : IsUnit ((τ Q.1).map Complex.im).det := ((hτ.2.2 _ hQ).2.det_pos.ne').isUnit
    have h1 : ((fun i => (Q.2 i).im) ᵥ* ((τ Q.1).map Complex.im)⁻¹) ᵥ* (τ Q.1).map Complex.im =
        fun i => (Q.2 i).im := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
    have h2 := congrFun h1 k
    simpa [flat, flatOf, Matrix.vecMul, dotProduct] using h2
  have hd : ∀ k, ∑ j, (flat τ (b, z) (Sum.inl j) * ((L j k) v.1).re +
      (τ b j k).im * F' (Complex.I • v) (Sum.inl j)) = (v.2 k).re := by
    intro k
    have hl := HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => (hpd j).fun_mul (hYd j k)
    have hu := hl.unique ((hyd k).congr_of_eventuallyEq (heq k))
    have := congrArg (fun T : Pt E g →L[ℝ] ℝ => T (Complex.I • v)) hu
    simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, hSz, Complex.imCLM_apply, Complex.reCLM_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_restrictScalars', Prod.smul_fst,
    Prod.smul_snd, Pi.smul_apply, map_smul, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, zero_sub, sub_zero, mul_zero, mul_one] using this
  have hc : ∀ k, (v.2 k).re = ∑ j, (flat τ (b, z) (Sum.inl j) * ((L j k) v.1).re +
      (τ b j k).re * F' v (Sum.inl j)) + F' v (Sum.inr k) := by
    intro k
    have hfun : (fun Q : Pt E g => ∑ j, flat τ Q (Sum.inl j) * (τ Q.1 j k).re + flat τ Q (Sum.inr k)) =
        fun Q => (Q.2 k).re := by
      funext Q
      simp only [flat, flatOf, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, Matrix.vecMul, dotProduct,
        Matrix.map_apply]
      ring
    have hl := (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => (hpd j).fun_mul (hXd j k)).fun_add (hqd k)
    rw [hfun] at hl
    have hu := (hrd k).unique hl
    have := congrArg (fun T : Pt E g →L[ℝ] ℝ => T v) hu
    simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, hSz, Complex.imCLM_apply, Complex.reCLM_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_restrictScalars', Prod.smul_fst,
    Prod.smul_snd, Pi.smul_apply, map_smul, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, zero_sub, sub_zero, mul_zero, mul_one] using this
  have hy : ∀ k, (z k).im = ∑ j, flat τ (b, z) (Sum.inl j) * (τ b j k).im := fun k =>
    ((heq k).self_of_nhds).symm
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, dflat, ← hF']
  exact alg_identity (fun i => flat τ (b, z) (Sum.inl i)) (fun i => (z i).im)
    (fun i => F' (Complex.I • v) (Sum.inl i)) (fun i => F' v (Sum.inl i)) (fun i => (v.2 i).re)
    (fun i => F' v (Sum.inr i)) (fun i j => (τ b i j).im) (fun i j => (τ b i j).re)
    (fun i j => ((L i j) v.1).re) (fun i j => by rw [hsym]) (fun i j => by rw [hsym]) hy hd hc

end GlobalTheory.ThetaMetDc
