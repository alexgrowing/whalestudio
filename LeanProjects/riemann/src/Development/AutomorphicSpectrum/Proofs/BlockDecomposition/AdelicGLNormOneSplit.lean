import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import GroundTheory.AutomorphicForms.CuspidalDiscreteness

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitHomeo

open GroundTheory.Automorphic GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_splitCentre : Continuous (splitCentre E a) := by
  have e : splitCentre E a = fun t : ℝ =>
      Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) :=
    funext splitCentre_eq_scalar
  rw [e]
  refine Continuous.units_map _ ?_ |>.comp ((continuous_infId E).comp
    (continuous_expU.comp (continuous_pi fun _ => Complex.continuous_ofReal)))
  change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin a => x
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

variable (E) in

def expIdele (t : ℝ) : IdeleGroup E := infId E (expU fun _ : InfinitePlace E => (t : ℂ))

theorem pInf_expIdele (t : ℝ) (w : InfinitePlace E) :
    pInf E (expIdele E t : Ad E) w = Complex.exp t := by
  have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  change pInf E (1 - sInf E 1 + sInf E _) w = _
  simp only [map_add, map_sub, map_one, h, sub_self, zero_add]
  rfl

theorem pFin_expIdele (t : ℝ) : pFin E (expIdele E t : Ad E) = 1 := by
  change (1 : Af E) - 0 + 0 = 1
  simp

theorem ideleModule_expIdele (t : ℝ) :
    (IdeleGroup.ideleModule E (expIdele E t) : ℝ) = Real.exp (Module.finrank ℚ E * t) := by
  have h1 : ∀ v : InfinitePlace E, ‖(expIdele E t : Ad E).1 v‖ = Real.exp t := fun v => by
    have := pInf_expIdele (E := E) t v
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    refine (congrArg norm this).trans ?_
    rw [Complex.norm_exp, Complex.ofReal_re]
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(expIdele E t : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (expIdele E t : Ad E) v‖ = 1
    rw [pFin_expIdele]
    exact norm_one
  rw [IdeleGroup.ideleModule_eq]
  change (∏ v : InfinitePlace E, ‖(expIdele E t : Ad E).1 v‖ ^ v.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(expIdele E t : Ad E).2 v‖ = _
  simp only [h1, h2, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← Real.exp_nat_mul]

theorem det_splitCentre (t : ℝ) : AdelicGLn.det E a (splitCentre E a t) = expIdele E t ^ a := by
  rw [splitCentre_eq_scalar]
  refine Units.ext ?_
  change (Matrix.scalar (Fin a) (expIdele E t : Ad E)).det = _
  simp

theorem ideleModule_det_splitCentre (t : ℝ) :
    (IdeleGroup.ideleModule E (AdelicGLn.det E a (splitCentre E a t)) : ℝ) =
      Real.exp ((a * Module.finrank ℚ E : ℝ) * t) := by
  rw [det_splitCentre, map_pow, Positive.val_pow, ideleModule_expIdele, ← Real.exp_nat_mul]
  congr 1
  ring

def splitDeg (E : Type) [Field E] [NumberField E] (a : ℕ) (g : GA E a) : ℝ :=
  Real.log (IdeleGroup.ideleModule E (AdelicGLn.det E a g)) / (a * Module.finrank ℚ E : ℝ)

theorem continuous_splitDeg : Continuous (splitDeg E a) := by
  refine Continuous.div_const (Continuous.log ?_ fun g => ?_) _
  · exact continuous_subtype_val.comp
      (IdeleGroup.continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  · exact (IdeleGroup.ideleModule E (AdelicGLn.det E a g)).2.ne'

theorem coeff_ne_zero (ha : 0 < a) : (a * Module.finrank ℚ E : ℝ) ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.2 ha.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')

theorem splitCentre_neg_mul_mem (ha : 0 < a) (g : GA E a) :
    splitCentre E a (-splitDeg E a g) * g ∈ Reduction.normOneGL E a := by
  have hc := coeff_ne_zero (E := E) ha
  have hpos := (IdeleGroup.ideleModule E (AdelicGLn.det E a g)).2
  rw [Reduction.mem_normOneGL, map_mul, map_mul, Positive.val_mul, ideleModule_det_splitCentre,
    mul_neg, splitDeg, mul_div_cancel₀ _ hc, Real.exp_neg, Real.exp_log hpos, inv_mul_cancel₀ hpos.ne']

theorem splitDeg_splitCentre_mul (ha : 0 < a) (x : Reduction.normOneGL E a) (t : ℝ) :
    splitDeg E a (splitCentre E a t * (x : GA E a)) = t := by
  have hc := coeff_ne_zero (E := E) ha
  have hx : (IdeleGroup.ideleModule E (AdelicGLn.det E a (x : GA E a)) : ℝ) = 1 :=
    Reduction.mem_normOneGL.1 x.2
  rw [splitDeg, map_mul, map_mul, Positive.val_mul, ideleModule_det_splitCentre, hx, mul_one,
    Real.log_exp, mul_div_cancel_left₀ _ hc]

theorem splitCentre_neg_mul_self (t : ℝ) (g : GA E a) :
    splitCentre E a (-t) * (splitCentre E a t * g) = g := by
  rw [← mul_assoc, ← splitCentre_add, neg_add_cancel, splitCentre_zero, one_mul]

theorem exists_homeomorph (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ha : 0 < a) :
    ∃ e : Reduction.normOneGL E a × ℝ ≃ₜ GA E a, ∀ x t, e (x, t) = splitCentre E a t * (x : GA E a) := by
  refine ⟨{
    toFun := fun p => splitCentre E a p.2 * (p.1 : GA E a)
    invFun := fun g => (⟨splitCentre E a (-splitDeg E a g) * g, splitCentre_neg_mul_mem ha g⟩, splitDeg E a g)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }, fun _ _ => rfl⟩
  · rintro ⟨x, t⟩
    refine Prod.ext (Subtype.ext ?_) (splitDeg_splitCentre_mul ha x t)
    change splitCentre E a (-splitDeg E a (splitCentre E a t * (x : GA E a))) * _ = _
    rw [splitDeg_splitCentre_mul ha x t, splitCentre_neg_mul_self]
  · intro g
    change splitCentre E a (splitDeg E a g) * (splitCentre E a (-splitDeg E a g) * g) = g
    simpa using splitCentre_neg_mul_self (-splitDeg E a g) g
  · exact (continuous_splitCentre.comp continuous_snd).mul
      (continuous_subtype_val.comp continuous_fst)
  · refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_splitDeg
    exact (continuous_splitCentre.comp continuous_splitDeg.neg).mul continuous_id

end GlobalTheory.CompanionTheory.SplitHomeo
