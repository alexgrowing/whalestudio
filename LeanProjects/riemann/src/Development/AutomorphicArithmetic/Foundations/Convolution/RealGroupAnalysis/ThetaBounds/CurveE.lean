import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SplitA

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem pInf_sInf (x : TR.Rinf F) : TR.pInf F (TR.sInf F x) = x :=
  (TR.infEq F).symm_apply_apply x

private theorem pFin_sInf (x : TR.Rinf F) : pFin F (TR.sInf F x) = 0 := rfl

private noncomputable def cU (w : InfinitePlace F) (t : ℝ) : GL (Fin 2) (TR.Rinf F) :=
  ⟨!![1, Pi.single w t; 0, 1], !![1, Pi.single w (-t); 0, 1],
    by
      ext i j v
      fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h],
    by
      ext i j v
      fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h]⟩

private theorem cU_val (w : InfinitePlace F) (t : ℝ) : (cU w t).val = !![1, Pi.single w t; 0, 1] := rfl

private theorem cU_add (w : InfinitePlace F) (s t : ℝ) : cU w (s + t) = cU w s * cU w t := by
  refine Units.ext ?_
  rw [Units.val_mul, cU_val, cU_val, cU_val]
  ext i j v
  fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h, add_comm]

private theorem cU_der (w : InfinitePlace F) :
    HasDerivAt (fun t => TR.toL (cU w t).val) (TR.toL (Matrix.single 0 1 (Pi.single w 1))) 0 := by
  have e : (fun t => TR.toL (cU w t).val) =
      fun t : ℝ => TR.toL (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) + t • TR.toL (Matrix.single 0 1 (Pi.single w 1)) := by
    funext t
    ext i j v
    fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [cU_val, Matrix.single_apply, Pi.single_apply, h]
  rw [e]
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const (TR.toL (Matrix.single 0 1 (Pi.single w 1)) : TR.Lie F 2)).const_add
    (TR.toL (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) : TR.Lie F 2)
  simpa only [id, one_smul] using h

private theorem unipotent_placeEmbed_gl (w : InfinitePlace F) (t : ℝ) : gl (nU (Fo.at1 w t)) = TR.infGL F 2 (cU w t) := by
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    refine Units.ext ?_
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [cU_val, Fo.at1, pInf_sInf]
  · rw [TR.pFin_infGL]
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Fo.at1, pFin_sInf]

private theorem character_placeEmbed_exp (w : InfinitePlace F) (t : ℝ) (q : A F) :
    ψ (Fo.at1 w t * q) = Complex.exp (Fo.cc * ((t : ℂ) * Fo.cw w q)) := by
  rw [(UpperTheory.ConvolutionTheory.R2.C.splitA F).2]
  have h2 : (Fo.at1 w t * q).2 = 0 := by
    change (0 : FiniteAdeleRing (𝓞 F) F) * q.2 = 0
    exact zero_mul _
  rw [h2, AddChar.map_zero_eq_one, Circle.coe_one, mul_one, Finset.prod_eq_single w]
  · simp [Fo.at1, Fo.cc, Fo.cw, pInf_sInf]
  · intro v _ hv
    simp [Fo.at1, pInf_sInf, hv]
  · simp

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.curveE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D), CurveE O W := by
  intro F E _ _ _ _ _ _ _ D O W w
  refine ⟨fun t => nU (Fo.at1 w t), cU w, ⟨cU_add w, cU_der w⟩, unipotent_placeEmbed_gl w, fun φ t v => ?_⟩
  have he : (O.e D.δ w φ).1 v = Fo.cc * Fo.cw w (q4 D.δ v) * φ.1 v := by
    have a : ∀ i j (χ : S4 F), (O.x w i (O.x w j χ)).1 v = Fo.cw w (v i) * (Fo.cw w (v j) * χ.1 v) := fun i j χ => by
      rw [O.x_apply, O.x_apply]
    simp only [Fo.Ops.e, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply]
    change Fo.cc * (((O.x w 2 (O.x w 2 φ)).1 v - Fo.cw w (rt D.δ) * (O.x w 3 (O.x w 3 φ)).1 v) - (O.x w 1 (O.x w 0 φ)).1 v) = _
    rw [a, a, a]
    simp only [Fo.cw, q4, map_sub, map_mul, map_pow, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    push_cast
    ring
  have e1 : (fun s => (W.Om (nU (Fo.at1 w s)) φ).1 v) =
      fun s : ℝ => Complex.exp (Fo.cc * ((s : ℂ) * Fo.cw w (q4 D.δ v))) * φ.1 v := by
    funext s
    rw [W.Om_n, character_placeEmbed_exp]
  simp only []
  rw [e1, W.Om_n, character_placeEmbed_exp, he]
  have h0 : HasDerivAt (fun s : ℝ => Fo.cc * ((s : ℂ) * Fo.cw w (q4 D.δ v))) (Fo.cc * Fo.cw w (q4 D.δ v)) t := by
    simpa using (((hasDerivAt_id t).ofReal_comp).mul_const (Fo.cw w (q4 D.δ v))).const_mul Fo.cc
  rw [← mul_assoc (Complex.exp _)]
  exact h0.cexp.mul_const (φ.1 v)
