import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.AtLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section
variable {F : Type} [Field F] [NumberField F]

private theorem psi_add (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem norm_psi (a : A F) : ‖ψ a‖ = 1 := by
  exact Circle.norm_coe _

private theorem cont_psi : Continuous (ψ : A F → ℂ) :=
  continuous_subtype_val.comp continuous_adelicChar

private theorem B_add (δ : F) (y v v' : V4 F) : B4 δ y (v + v') = B4 δ y v + B4 δ y v' := by
  simp only [B4, Pi.add_apply]
  ring

private theorem B_single (δ : F) (y : V4 F) (i : Fin 4) (a : A F) :
    B4 δ y (Pi.single i a) = a * B4 δ y (Pi.single i 1) := by
  fin_cases i <;> simp [B4] <;> ring

private theorem cont_B (δ : F) (v : V4 F) : Continuous fun y : V4 F => B4 δ y v := by
  unfold B4
  exact ((continuous_const.mul (((continuous_apply 2).mul continuous_const).sub
    (continuous_const.mul ((continuous_apply 3).mul continuous_const)))).sub
    ((continuous_apply 1).mul continuous_const)).sub ((continuous_apply 0).mul continuous_const)

variable [IsTotallyReal F]

private theorem cw_add (w : InfinitePlace F) (a b : A F) : cw w (a + b) = cw w a + cw w b := by
  simp [cw]
private theorem cw_sub (w : InfinitePlace F) (a b : A F) : cw w (a - b) = cw w a - cw w b := by
  simp [cw]
private theorem cw_mul (w : InfinitePlace F) (a b : A F) : cw w (a * b) = cw w a * cw w b := by
  simp [cw]
private theorem cw_neg (w : InfinitePlace F) (a : A F) : cw w (-a) = -cw w a := by
  simp [cw]
private theorem cw_two (w : InfinitePlace F) : cw w (2 : A F) = 2 := by
  have h1 : cw w (1 : A F) = 1 := by simp [cw]
  rw [show (2 : A F) = 1 + 1 by norm_num, cw_add, h1]
  norm_num

private theorem p_apply (δ : F) (O : Ops F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (y : V4 F) :
    (O.p δ w i φ).1 y = cc * cw w (B4 δ y (Pi.single i 1)) * φ.1 y := by
  fin_cases i <;>
    simp [Ops.p, B4, O.x_apply, cw_add, cw_sub, cw_mul, cw_neg, cw_two] <;> ring

private theorem psi_shift (δ : F) (w : InfinitePlace F) (i : Fin 4) (y v : V4 F) (t : ℝ) :
    ψ (B4 δ y (v + Pi.single i (at1 w t))) =
      ψ (B4 δ y v) * Complex.exp (cc * cw w (B4 δ y (Pi.single i 1)) * t) := by
  obtain ⟨h1, -, -, -, -, h6, -, -⟩ := atLaws F w
  rw [B_add, psi_add, B_single, h6, h1]
  congr 2
  simp only [cw]
  push_cast
  ring

private theorem deriv_gen {X : Type} [MeasurableSpace X] (μ : Measure X) (f G : X → ℂ) (u : ℝ → X → ℂ) (c : X → ℂ)
    (hf : Integrable f μ) (hG : Integrable G μ) (hu : ∀ t, AEStronglyMeasurable (u t) μ)
    (hn : ∀ t y, ‖u t y‖ = 1) (hd : ∀ t y, HasDerivAt (fun s => u s y) (c y * u t y) t)
    (hc : ∀ y, G y = c y * f y) :
    HasDerivAt (fun t => ∫ y, f y * u t y ∂μ) (∫ y, G y * u 0 y ∂μ) 0 := by
  have hm : ∀ t, AEStronglyMeasurable (fun y => f y * u t y) μ := fun t => hf.1.mul (hu t)
  have hm' : ∀ t, AEStronglyMeasurable (fun y => G y * u t y) μ := fun t => hG.1.mul (hu t)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t y => f y * u t y) (F' := fun t y => G y * u t y)
    (x₀ := (0 : ℝ)) (s := Set.univ) (bound := fun y => ‖G y‖) univ_mem
    (Eventually.of_forall hm)
    (hf.mono (hm 0) (ae_of_all _ fun y => by rw [norm_mul, hn, mul_one]))
    (hm' 0)
    (ae_of_all _ fun y t _ => by rw [norm_mul, hn, mul_one])
    hG.norm
    (ae_of_all _ fun y t _ => ?_)).2
  refine ((hd t y).const_mul (f y)).congr_deriv ?_
  rw [hc]
  ring

private theorem psi_deriv (δ : F) (w : InfinitePlace F) (i : Fin 4) (y v : V4 F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ψ (B4 δ y (v + Pi.single i (at1 w s))))
      (cc * cw w (B4 δ y (Pi.single i 1)) * ψ (B4 δ y (v + Pi.single i (at1 w t)))) t := by
  have h1 : HasDerivAt (fun s : ℝ => cc * cw w (B4 δ y (Pi.single i 1)) * (s : ℂ))
      (cc * cw w (B4 δ y (Pi.single i 1))) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (cc * cw w (B4 δ y (Pi.single i 1)))
  have h2 := h1.cexp.const_mul (ψ (B4 δ y v))
  simp only [psi_shift]
  refine h2.congr_deriv ?_
  ring

private theorem deriv_ops (O : Ops F) (δ : F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (u : ℝ → V4 F → ℂ) (c : V4 F → ℂ)
    (hu : ∀ t, AEStronglyMeasurable (u t) (adeleMeasurePi F)) (hn : ∀ t y, ‖u t y‖ = 1)
    (hd : ∀ t y, HasDerivAt (fun s => u s y) (c y * u t y) t) (hc : ∀ y, (O.p δ w i φ).1 y = c y * φ.1 y) :
    HasDerivAt (fun t => ∫ y, φ.1 y * u t y ∂(adeleMeasurePi F)) (∫ y, (O.p δ w i φ).1 y * u 0 y ∂(adeleMeasurePi F)) 0 :=
  deriv_gen (adeleMeasurePi F) φ.1 (O.p δ w i φ).1 u c (integrable_of_mem_schwartzBruhatPi φ.2)
    (integrable_of_mem_schwartzBruhatPi (O.p δ w i φ).2) hu hn hd hc

private theorem key (δ : F) (O : Ops F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (v : V4 F) :
    HasDerivAt (fun t : ℝ => ft4 δ φ.1 (v + Pi.single i (at1 w t))) (ft4 δ (O.p δ w i φ).1 v) 0 := by
  obtain ⟨-, -, -, -, h0, -, -, -⟩ := atLaws F w
  obtain ⟨u, hu⟩ : ∃ u : ℝ → V4 F → ℂ, ∀ t y, u t y = ψ (B4 δ y (v + Pi.single i (at1 w t))) := ⟨_, fun _ _ => rfl⟩
  have hm : ∀ t, AEStronglyMeasurable (u t) (adeleMeasurePi F) := fun t => by
    rw [show u t = fun y => ψ (B4 δ y (v + Pi.single i (at1 w t))) from funext (hu t)]
    exact (cont_psi.comp (cont_B δ _)).aestronglyMeasurable
  have hn : ∀ t y, ‖u t y‖ = 1 := fun t y => by rw [hu]; exact norm_psi _
  have hd : ∀ t y, HasDerivAt (fun s => u s y) (cc * cw w (B4 δ y (Pi.single i 1)) * u t y) t := fun t y => by
    rw [show (fun s => u s y) = fun s => ψ (B4 δ y (v + Pi.single i (at1 w s))) from funext fun s => hu s y, hu]
    exact psi_deriv δ w i y v t
  have h := deriv_ops O δ w i φ u (fun y => cc * cw w (B4 δ y (Pi.single i 1))) hm hn hd (fun y => p_apply δ O w i φ y)
  have e1 : (fun t : ℝ => ft4 δ φ.1 (v + Pi.single i (at1 w t))) = fun t => ∫ y, φ.1 y * u t y ∂(adeleMeasurePi F) := by
    simp only [ft4, hu]
  have e2 : ft4 δ (O.p δ w i φ).1 v = ∫ y, (O.p δ w i φ).1 y * u 0 y ∂(adeleMeasurePi F) := by
    simp only [ft4, hu, h0, Pi.single_zero, add_zero]
  rw [e1, e2]
  exact h

end

theorem UpperTheory.ConvolutionTheory.R2.Fo.dW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w i, O.d w i * W.Om (wW F) = W.Om (wW F) * O.p D.δ w i := by
  intro F E _ _ _ _ _ _ _ D W O w i
  refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
  rw [Module.End.mul_apply, Module.End.mul_apply]
  rw [W.Om_w (O.p D.δ w i φ) v]
  have hd := O.d_spec w i (W.Om (wW F) φ) v
  simp only [W.Om_w] at hd
  exact hd.unique (key D.δ O w i φ v)
