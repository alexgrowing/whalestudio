import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.WhittakerHecke.IsCompactIntegralIdeleUnitsAndAbsEqOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open scoped ENNReal NNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb

def US : Subgroup (A ℚ)ˣ where
  carrier := UU
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun v => ?_⟩
    · change (a : A ℚ).1 * (b : A ℚ).1 = 1
      rw [ha, hb, one_mul]
    · rw [Units.val_mul, map_mul, map_mul, ha' v, hb' v, one_mul]
  one_mem' := ⟨rfl, fun v => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun v => ?_⟩
    · have h : ((a⁻¹ : (A ℚ)ˣ) : A ℚ).1 * (a : A ℚ).1 = 1 := congrArg Prod.fst (Units.inv_mul a)
      rwa [ha, mul_one] at h
    · have h : Valued.v (H.cp v ((a⁻¹ : (A ℚ)ˣ) : A ℚ)) * Valued.v (H.cp v (a : A ℚ)) = 1 := by
        rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
      rwa [ha' v, mul_one] at h

abbrev GG : Type := ↥(GroundTheory.Automorphic.Reduction.normOneGL ℚ 2)

abbrev Ga : Subgroup GG := GroundTheory.Automorphic.Reduction.rationalGLOne ℚ 2

theorem det_el (g : G1 ℚ) (t : (A ℚ)ˣ) : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (gl g * dM t) = t := by
  refine Units.ext ?_
  rw [GroundTheory.Automorphic.AdelicGLn.coe_det]
  have h : ((gl g * dM t : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) =
      (g : Matrix (Fin 2) (Fin 2) (A ℚ)) * !![1, 0; 0, (t : A ℚ)] := rfl
  rw [h, Matrix.det_mul, g.det_coe, one_mul, Matrix.det_fin_two_of]
  simp

theorem mem_norm (g : G1 ℚ) (t : US) : gl g * dM (t : (A ℚ)ˣ) ∈ GroundTheory.Automorphic.Reduction.normOneGL ℚ 2 := by
  rw [GroundTheory.Automorphic.Reduction.mem_normOneGL, det_el]
  exact UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one.2 _ t.2

def pm (p : G1 ℚ × US) : GG := ⟨gl p.1 * dM (p.2 : (A ℚ)ˣ), mem_norm _ _⟩

def us (U : UMeas) : Measure US := U.υ.comap Subtype.val

theorem measurableSet_US : MeasurableSet (US : Set (A ℚ)ˣ) := UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one.1.isClosed.measurableSet

theorem val_emb : MeasurableEmbedding (Subtype.val : US → (A ℚ)ˣ) := MeasurableEmbedding.subtype_coe measurableSet_US

instance us_prob (U : UMeas) : IsProbabilityMeasure (us U) := by
  haveI := U.prob
  refine ⟨?_⟩
  have h : U.υ (US : Set (A ℚ)ˣ)ᶜ = 0 := U.supp
  have h1 : U.υ (US : Set (A ℚ)ˣ) = 1 := (prob_compl_eq_zero_iff measurableSet_US).1 h
  unfold us
  rw [val_emb.comap_apply, Set.image_univ, Subtype.range_coe]
  exact h1

theorem us_mul (U : UMeas) (t : US) : MeasurePreserving (fun x : US => t * x) (us U) (us U) := by
  have hm : Measurable (fun x : US => t * x) := (continuous_const.mul continuous_id).measurable
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs]
  unfold us
  rw [val_emb.comap_apply, val_emb.comap_apply]
  have hs' : MeasurableSet (Subtype.val '' s : Set (A ℚ)ˣ) := val_emb.measurableSet_image.2 hs
  have hmt : Measurable (fun x : IdeleGroup ℚ => (t * x : (A ℚ)ˣ)) :=
    (continuous_const.mul continuous_id).measurable
  have hi : (U.υ.map (fun x : IdeleGroup ℚ => (t * x : (A ℚ)ˣ))) (Subtype.val '' s) = U.υ (Subtype.val '' s) := by
    rw [U.inv t t.2]
  rw [Measure.map_apply hmt hs'] at hi
  rw [← hi]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, hy, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hx : x ∈ US := by
      have : x = ((t⁻¹ * y : US) : (A ℚ)ˣ) := by
        simp [hyx]
      rw [this]
      exact Subtype.coe_prop _
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    have : t * ⟨x, hx⟩ = y := Subtype.ext hyx.symm
    simpa [this] using hy

theorem dM_mul (s t : (A ℚ)ˣ) : dM (s * t) = dM s * dM t := by
  apply Units.ext
  change !![1, 0; 0, ((s * t : (A ℚ)ˣ) : A ℚ)] = !![1, 0; 0, (s : A ℚ)] * !![1, 0; 0, (t : A ℚ)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem dM_gl (t : (A ℚ)ˣ) (g : G1 ℚ) : dM t * gl g = gl (cD t g) * dM t := by
  apply Units.ext
  change !![1, 0; 0, (t : A ℚ)] * (g : Matrix (Fin 2) (Fin 2) (A ℚ)) =
    (cD t g : Matrix (Fin 2) (Fin 2) (A ℚ)) * !![1, 0; 0, (t : A ℚ)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem pm_mul (p q : G1 ℚ × US) : pm p * pm q = pm (p.1 * cD (p.2 : (A ℚ)ˣ) q.1, p.2 * q.2) := by
  apply Subtype.ext
  change gl p.1 * dM (p.2 : (A ℚ)ˣ) * (gl q.1 * dM (q.2 : (A ℚ)ˣ)) =
    gl (p.1 * cD (p.2 : (A ℚ)ˣ) q.1) * dM ((p.2 : (A ℚ)ˣ) * (q.2 : (A ℚ)ˣ))
  have h : gl (p.1 * cD (p.2 : (A ℚ)ˣ) q.1) = gl p.1 * gl (cD (p.2 : (A ℚ)ˣ) q.1) := Units.ext rfl
  rw [dM_mul, h, mul_assoc, ← mul_assoc (dM _) (gl _), dM_gl]
  simp only [mul_assoc]

theorem exists_sl (y : GL (Fin 2) (A ℚ)) (h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 y = 1) : ∃ g : G1 ℚ, gl g = y := by
  refine ⟨⟨y.val, ?_⟩, Units.ext rfl⟩
  have := congrArg Units.val h
  rwa [GroundTheory.Automorphic.AdelicGLn.coe_det] at this

theorem range_pm : Set.range pm = {x : GG | GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ)) ∈ UU} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    change GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (gl p.1 * dM (p.2 : (A ℚ)ˣ)) ∈ UU
    rw [det_el]
    exact p.2.2
  · intro hx
    obtain ⟨g, hg⟩ := exists_sl ((x : GL (Fin 2) (A ℚ)) * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ))))⁻¹) (by
      have h1 := det_el 1 (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ)))
      simp only [map_one, one_mul] at h1
      rw [map_mul, map_inv, h1, mul_inv_cancel])
    refine ⟨(g, ⟨_, hx⟩), Subtype.ext ?_⟩
    change gl g * dM _ = _
    rw [hg, inv_mul_cancel_right]

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
