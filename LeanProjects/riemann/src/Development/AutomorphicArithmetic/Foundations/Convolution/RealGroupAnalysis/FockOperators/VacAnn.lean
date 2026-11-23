import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.AtLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem hasDerivAt_sumq {ι : Type} [Fintype ι] [DecidableEq ι] (K b r : ι → ℝ) (w : ι) :
    HasDerivAt (fun t : ℝ => ∑ w', (K w' * (b w' + (Pi.single w t : ι → ℝ) w') ^ 2 + r w')) (2 * K w * b w) 0 := by
  have h : ∀ w' ∈ (Finset.univ : Finset ι), HasDerivAt (fun t : ℝ => K w' * (b w' + (Pi.single w t : ι → ℝ) w') ^ 2 + r w')
      (if w' = w then 2 * K w * b w else 0) 0 := by
    intro w' _
    by_cases hw : w' = w
    · subst hw
      simp only [Pi.single_eq_same, if_true]
      have h0 : HasDerivAt (fun t : ℝ => b w' + t) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add (b w')
      refine (((h0.fun_pow 2).const_mul (K w')).add_const (r w')).congr_deriv ?_
      simp only [add_zero, Nat.add_one_sub_one, pow_one, mul_one, Nat.cast_ofNat]
      ring
    · simp only [Pi.single_eq_of_ne hw, if_neg hw]
      exact hasDerivAt_const _ _
  have := HasDerivAt.fun_sum h
  simpa using this

private theorem gauss_deriv {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (v : V4 F) (w : InfinitePlace F) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => gauss δ (v + Pi.single i (at1 w t)))
      (-2 * Real.pi * kap δ w i * cw w (v i) * gauss δ v) 0 := by
  obtain ⟨-, -, hp, -, h0, -, -, -⟩ := atLaws F w
  set p := TR.pInf F with hpdef
  let Kf : InfinitePlace F → ℝ := fun w' => ![1, 1, 2, -2 * p (rt δ) w'] i
  let bf : InfinitePlace F → ℝ := fun w' => p (v i) w'
  let Q : V4 F → A F := fun u => u 0 ^ 2 + u 1 ^ 2 + 2 * (u 2 ^ 2 - rt δ * u 3 ^ 2)
  let rf : InfinitePlace F → ℝ := fun w' => p (Q v) w' - Kf w' * bf w' ^ 2
  have hQ : ∀ (t : ℝ) w', p (Q (v + Pi.single i (at1 w t))) w' =
      Kf w' * (bf w' + (Pi.single w t : InfinitePlace F → ℝ) w') ^ 2 + rf w' := by
    intro t w'
    have h2 : p (2 : A F) w' = 2 := by
      rw [map_ofNat]
      rfl
    fin_cases i <;> simp [Q, Kf, bf, rf, hp, h2, map_add, map_mul, map_pow, map_sub, Pi.single_apply] <;> ring
  have hK : kap δ w i = ((Kf w : ℝ) : ℂ) := by
    fin_cases i <;> simp [kap, Kf, cw, hpdef]
  have hfun : (fun t : ℝ => gauss δ (v + Pi.single i (at1 w t))) = fun t : ℝ => Complex.exp (-(Real.pi : ℂ) *
      ((∑ w', (Kf w' * (bf w' + (Pi.single w t : InfinitePlace F → ℝ) w') ^ 2 + rf w') : ℝ) : ℂ)) := by
    funext t
    simp only [← hQ]
    rfl
  have hC : HasDerivAt (fun t : ℝ => ((∑ w', (Kf w' * (bf w' + (Pi.single w t : InfinitePlace F → ℝ) w') ^ 2 + rf w') : ℝ) : ℂ))
      ((2 * Kf w * bf w : ℝ) : ℂ) 0 := (hasDerivAt_sumq Kf bf rf w).ofReal_comp
  have hX := (hC.const_mul (-(Real.pi : ℂ))).cexp
  have e0 : v + Pi.single i (at1 w 0) = v := by
    rw [h0]
    simp
  have hval := (congrArg (gauss δ) e0).symm.trans (congrFun hfun 0)
  rw [hfun]
  refine hX.congr_deriv ?_
  beta_reduce at hval ⊢
  rw [← hval, hK]
  have hb : cw w (v i) = ((bf w : ℝ) : ℂ) := rfl
  rw [hb]
  push_cast
  ring

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacAnn :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F), ∀ φ ∈ Vac δ, ∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ := by
  intro F _ _ _ δ O φ hφ w i
  obtain ⟨-, -, -, -, -, -, -, hfin⟩ := atLaws F w
  apply Subtype.ext
  funext v
  have hg := gauss_deriv δ v w i
  have hne : gauss δ v ≠ 0 := Complex.exp_ne_zero _
  have hf : ∀ t : ℝ, finPartPi (v + Pi.single i (at1 w t)) = finPartPi v := by
    intro t
    have := hfin t i
    funext j
    have hj := congrFun this j
    simp only [finPartPi] at hj ⊢
    simp [hj]
  have h1 : (fun t : ℝ => φ.1 (v + Pi.single i (at1 w t))) = fun t : ℝ => (φ.1 v / gauss δ v) * gauss δ (v + Pi.single i (at1 w t)) := by
    funext t
    have := hφ (v + Pi.single i (at1 w t)) v (hf t)
    field_simp
    exact this
  have hd := O.d_spec w i φ v
  rw [h1] at hd
  have hu := hd.unique (hg.const_mul (φ.1 v / gauss δ v))
  change _ = (-2 * Real.pi * kap δ w i) * (O.x w i φ).1 v
  rw [hu, O.x_apply]
  field_simp
