import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem psi_add (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem co_mkE (D : Dat F E) (u t : A F) : D.co (D.mkE u t) = ![u, t] := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  have h : D.mkE u t = ∑ i, (![u, t] : Fin 2 → A F) i • AdeleBaseChange.adeleBasis D.b i := by
    rw [Fin.sum_univ_two]
    simp only [AdeleBaseChange.adeleBasis_apply, D.b0, D.b1, Algebra.smul_def, map_one, Dat.mkE,
      AdeleBaseChange.algebraMap_adeleRing]
    simp
  unfold Dat.co
  rw [h, Module.Basis.repr_sum_self]

private theorem bar_mkE (D : Dat F E) (u t : A F) : D.bar (D.mkE u t) = D.mkE u (-t) := by
  have h1 : ∀ a : A F, D.bar (AdeleBaseChange.adeleMap F E a) = AdeleBaseChange.adeleMap F E a :=
    fun a => AdeleBaseChange.smul_adeleMap D.σ a
  have h2 : D.bar (rt D.θ) = - rt D.θ := by
    have : D.bar (rt D.θ) = rt (D.σ D.θ) := AdeleBaseChange.smul_algebraMap D.σ D.θ
    rw [this, D.conj]; simp [UpperTheory.ConvolutionTheory.R2.rt]
  simp only [Dat.mkE, map_add, map_mul, h1, h2, map_neg]
  ring

private theorem theta_sq (D : Dat F E) :
    rt D.θ * rt D.θ = AdeleBaseChange.adeleMap F E (rt D.δ) := by
  rw [UpperTheory.ConvolutionTheory.R2.rt, UpperTheory.ConvolutionTheory.R2.rt, AdeleBaseChange.adeleMap_algebraMap, ← D.sq, ← map_mul, pow_two]

private theorem nu_gl (b : A E) : nu F (gl (nU b)) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (gl (nU b)) = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.det]
  simp [nu, h]

private theorem ab_one : ab (1 : (A F)ˣ) = 1 := by simp [ab]

private theorem gl_val (b : A E) : (gl (nU b)).val = !![1, b; 0, 1] := rfl

private theorem gl_inv (b : A E) : (gl (nU b))⁻¹ = gl (nU (-b)) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, gl_val, gl_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem act_nU (D : Dat F E) (u t s z₀ z₁ : A F) :
    D.act (gl (nU (D.mkE u t)))⁻¹ ![0, s, z₀, z₁] =
      ![0, s - 2 * (u * z₀ - UpperTheory.ConvolutionTheory.R2.rt D.δ * (t * z₁)), z₀, z₁] := by
  rw [gl_inv]
  have hb : D.bar (-D.mkE u t) = - D.mkE u (-t) := by rw [map_neg, bar_mkE]
  have h0 : D.mkE 0 0 = 0 := by simp [Dat.mkE]
  have hθ := theta_sq D
  have e11 : ((gl (nU (-D.mkE u t))).val * D.herm ![0, s, z₀, z₁] *
      ((gl (nU (-D.mkE u t))).val.map D.bar)ᵀ) 1 1 = 0 := by
    rw [gl_val]
    simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two, h0]
  have e01 : ((gl (nU (-D.mkE u t))).val * D.herm ![0, s, z₀, z₁] *
      ((gl (nU (-D.mkE u t))).val.map D.bar)ᵀ) 0 1 = D.mkE z₀ z₁ := by
    rw [gl_val]
    simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two, h0]
  have e00 : ((gl (nU (-D.mkE u t))).val * D.herm ![0, s, z₀, z₁] *
      ((gl (nU (-D.mkE u t))).val.map D.bar)ᵀ) 0 0 =
      D.mkE (s - 2 * (u * z₀ - UpperTheory.ConvolutionTheory.R2.rt D.δ * (t * z₁))) 0 := by
    rw [gl_val]
    simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two, h0, hb]
    simp only [Dat.mkE, map_sub, map_mul, map_add, map_neg, map_zero, map_ofNat]
    linear_combination (2 * AdeleBaseChange.adeleMap F E t * AdeleBaseChange.adeleMap F E z₁) * hθ
  have z0 : D.co 0 = ![0, 0] := by rw [← h0, co_mkE]
  rw [Dat.act, Dat.unherm, e11, e01, e00, co_mkE, co_mkE, z0]
  ext i
  fin_cases i <;> simp

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.D.hatNE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ u t φ x z₀ z₁, hat (W.L (gl (nU (D.mkE u t))) φ).1 ![0, x, z₀, z₁] =
      ψ (-(x * (2 * (u * z₀ - rt D.δ * (t * z₁))))) * hat φ.1 ![0, x, z₀, z₁] := by
  intro F E _ _ _ _ _ _ _ D W u t φ x z₀ z₁
  set T : A F := 2 * (u * z₀ - rt D.δ * (t * z₁)) with hT
  have hup : ∀ s : A F, Function.update (![0, x, z₀, z₁] : V4 F) 1 s = ![0, s, z₀, z₁] := by
    intro s
    ext i
    fin_cases i <;> simp
  set g : A F → ℂ := fun s => φ.1 ![0, s, z₀, z₁] * ψ (-(s * x)) with hg
  have hR : hat φ.1 ![0, x, z₀, z₁] = ∫ s, g s ∂(adeleMeasure F) := by
    simp only [hat, hup, hg]
    rfl
  have hL : hat (W.L (gl (nU (D.mkE u t))) φ).1 ![0, x, z₀, z₁] =
      ∫ s, ψ (-(x * T)) * g (s - T) ∂(adeleMeasure F) := by
    simp only [hat, hup]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    have e : ψ (-(s * x)) = ψ (-(x * T)) * ψ (-((s - T) * x)) := by
      rw [← psi_add]; congr 1; ring
    simp only [W.L_apply, nu_gl, act_nU, hg, ← hT]
    simp [e, ab_one]
    ring
  rw [hL, hR, integral_const_mul, integral_sub_right_eq_self g T]
