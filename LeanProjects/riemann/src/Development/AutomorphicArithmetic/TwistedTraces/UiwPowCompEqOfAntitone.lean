import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HopOloc
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.UiwPow

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

open scoped InnerProductSpace

private theorem iw_scale {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (w : Pl K) [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure]
    (ν : Fin n → ℤ) (T : LL μ →L[ℂ] LL μ) (hT : IsOloc μ w m ((iwCoset w ν).indicator 1) T) :
    T = (((m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w))).toReal : ℝ) : ℂ) • Uiw μ w ν := by
  have hCO : CO (GLnLocal.iwahori (w.adicCompletion K) n) :=
    ⟨GLnLocal.isCompact_iwahori _ n, GLnLocal.isOpen_iwahori _ n⟩
  have h0 : m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) ≠ 0 :=
    (hCO.2.measure_pos m ⟨1, Subgroup.one_mem _⟩).ne'
  have ht : m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) ≠ ⊤ := hCO.1.measure_lt_top.ne
  obtain ⟨d, hd⟩ : ∃ d, d = (m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)))⁻¹ := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := hd ▸ ENNReal.inv_ne_zero.2 ht
  have hdt : d ≠ ⊤ := hd ▸ ENNReal.inv_ne_top.2 h0
  haveI : (d • m).IsHaarMeasure := Measure.IsHaarMeasure.smul m hd0 hdt
  have h1 : (d • m) (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) = 1 := by
    rw [Measure.smul_apply, hd, smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]
  have hop := UpperTheory.ConvolutionTheory.C.hopOloc K n μ w (d • m) (GLnLocal.iwahori (w.adicCompletion K) n)
    (Cartan.diagPow (w.adicCompletion K) n ν) hCO h1
  have hc : (m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨h0, ht⟩
  have hdc : d.toReal = ((m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w))).toReal)⁻¹ := by
    rw [hd, ENNReal.toReal_inv]
  ext1 v
  refine ext_inner_left ℂ fun u => ?_
  have e1 : ⟪u, Uiw μ w ν v⟫_ℂ = d.toReal • ∫ g, (iwCoset w ν).indicator 1 g * ⟪u, rhoL μ w g v⟫_ℂ ∂m := by
    have := hop u v
    rw [integral_smul_measure] at this
    exact this
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, e1, hT u v, hdc, Complex.real_smul, ← mul_assoc,
    Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hc), one_mul]

theorem UpperTheory.Uiw_pow_comp_eq_of_antitone :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)]
        (m : Measure (Gw n w)) [m.IsHaarMeasure] (e : Fin n → ℤ) (j : ℕ) (T T' : LL μ →L[ℂ] LL μ), Antitone e →
        IsOloc μ w m ((iwCoset w 0).indicator 1) T → IsOloc μ w m ((iwCoset w (j • e)).indicator 1) T' →
        (Uiw μ w e ^ j) ∘L T = T' := by
  intro K _ _ n μ _ w _ _ m _ e j T T' he hT hT'
  have h0 : prj (fixL μ w (GLnLocal.iwahori (w.adicCompletion K) n)) = Uiw μ w 0 := by
    have := UpperTheory.ConvolutionTheory.C.uiwPow K n μ w e he 0
    rw [pow_zero, zero_smul] at this
    exact this
  have h1 := UpperTheory.ConvolutionTheory.C.uiwPow K n μ w e he j
  rw [iw_scale μ w m 0 T hT, iw_scale μ w m _ T' hT', ← h0, ← h1]
  ext1 v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]
