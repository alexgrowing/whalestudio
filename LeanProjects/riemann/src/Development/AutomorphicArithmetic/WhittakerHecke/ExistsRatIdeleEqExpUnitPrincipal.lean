import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import GroundTheory.GlobalFields.IdeleGroups.Rational
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private lemma iy_fst {y : ℝ} (h : y ≠ 0) : ((iy y : (A ℚ)ˣ) : A ℚ).1 = TR.infEq ℚ fun _ => y := by
  rw [iy, dif_neg h]
  change (1 : InfiniteAdeleRing ℚ) - TR.infEq ℚ 1 + TR.infEq ℚ (fun _ => y) = _
  rw [map_one, sub_self, zero_add]

private lemma iy_snd {y : ℝ} (h : y ≠ 0) : ((iy y : (A ℚ)ˣ) : A ℚ).2 = 1 := by
  rw [iy, dif_neg h]
  change (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) - 0 + 0 = 1
  rw [sub_zero, add_zero]

private lemma real_infEq (y : ℝ) : RationalIdeles.realEquiv (TR.infEq ℚ fun _ => y) = y :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal default)).apply_symm_apply y

private lemma val_eq_one {w : IdeleGroup ℚ} (hw : w ∈ IdeleGroup.standardOpenSubgroup ℚ) (v : H.P ℚ) :
    Valued.v (((w : A ℚ)).2 v) = 1 := by
  obtain ⟨h1, h2⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 hw v
  have a1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 h1
  have a2 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 h2
  have hm : Valued.v (((w : A ℚ)).2 v) * Valued.v ((((w⁻¹ : IdeleGroup ℚ) : A ℚ)).2 v) = 1 := by
    rw [← map_mul]
    have e : ((w : A ℚ)).2 v * (((w⁻¹ : IdeleGroup ℚ) : A ℚ)).2 v = 1 :=
      congrArg (fun z : A ℚ => z.2 v) (Units.mul_inv w)
    rw [e, map_one]
  refine le_antisymm a1 ?_
  have := mul_le_mul' (le_refl (Valued.v (((w : A ℚ)).2 v))) a2
  rwa [hm, mul_one] at this

theorem UpperTheory.exists_rat_idele_eq_exp_unit_principal :
    ∀ x : IdeleGroup ℚ, ∃ (t : ℝ) (u : IdeleGroup ℚ) (α : ℚˣ), u ∈ UU ∧ x = Un.cov t u α := by
  intro x
  have hx : x ∈ RationalIdeles.positiveSubgroup ⊔ (IdeleGroup.diagonal ℚ).range := by
    rw [RationalIdeles.positiveSubgroup_sup_diagonal_range]
    exact Subgroup.mem_top x
  obtain ⟨w, hw, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx
  obtain ⟨hw1, hw2⟩ := RationalIdeles.mem_positiveSubgroup.1 hw
  have het : Real.exp (Real.log (RationalIdeles.realPart w : ℝ) / 2) *
      Real.exp (Real.log (RationalIdeles.realPart w : ℝ) / 2) = (RationalIdeles.realPart w : ℝ) := by
    rw [← Real.exp_add, add_halves, Real.exp_log hw2]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, Real.exp t * Real.exp t = (RationalIdeles.realPart w : ℝ) := ⟨_, het⟩
  have hy : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  obtain ⟨P, hP⟩ : ∃ P : IdeleGroup ℚ, P = iy (Real.exp t) * iy (Real.exp t) := ⟨_, rfl⟩
  have hP1 : ((P : A ℚ)).1 = ((w : A ℚ)).1 := by
    apply RationalIdeles.realEquiv.injective
    have e : ((P : A ℚ)).1 = ((iy (Real.exp t) : A ℚ)).1 * ((iy (Real.exp t) : A ℚ)).1 := by
      rw [hP]
      rfl
    rw [e, iy_fst hy, map_mul, real_infEq, ht]
    exact RationalIdeles.coe_realPart w
  have hP2 : ((P : A ℚ)).2 = 1 := by
    have e : ((P : A ℚ)).2 = ((iy (Real.exp t) : A ℚ)).2 * ((iy (Real.exp t) : A ℚ)).2 := by
      rw [hP]
      rfl
    rw [e, iy_snd hy, one_mul]
  have hPi : (((P⁻¹ : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    have e : (((P⁻¹ : IdeleGroup ℚ) : A ℚ)).2 * ((P : A ℚ)).2 = 1 :=
      congrArg (fun z : A ℚ => z.2) (Units.inv_mul P)
    rwa [hP2, mul_one] at e
  refine ⟨t, P⁻¹ * w, a, ⟨?_, fun v => ?_⟩, ?_⟩
  · have e : (((P⁻¹ : IdeleGroup ℚ) : A ℚ)).1 * ((P : A ℚ)).1 = 1 :=
      congrArg (fun z : A ℚ => z.1) (Units.inv_mul P)
    rw [hP1] at e
    exact e
  · have e : H.cp v (((P⁻¹ * w : IdeleGroup ℚ) : A ℚ)) =
        (((P⁻¹ : IdeleGroup ℚ) : A ℚ)).2 v * ((w : A ℚ)).2 v := rfl
    rw [e, hPi]
    change Valued.v ((1 : v.adicCompletion ℚ) * ((w : A ℚ)).2 v) = 1
    rw [one_mul]
    exact val_eq_one hw1 v
  · rw [Un.cov, ← hP, mul_assoc, mul_inv_cancel_left, mul_comm]
