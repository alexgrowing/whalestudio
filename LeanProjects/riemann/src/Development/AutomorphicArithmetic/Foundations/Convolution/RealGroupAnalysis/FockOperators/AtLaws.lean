import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SplitA

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.atLaws :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F), (∀ t : ℝ, ψ (at1 w t) = Complex.exp (cc * t)) ∧ (∀ t, (at1 w t).2 = 0) ∧ (∀ t, TR.pInf F (at1 w t) = Pi.single w t) ∧
    (∀ s t, at1 w (s + t) = at1 w s + at1 w t) ∧ at1 w 0 = 0 ∧ (∀ t a, at1 w t * a = at1 w (t * TR.pInf F a w)) ∧
    (∀ a : A F, a.2 = 0 → a = ∑ w', at1 w' (TR.pInf F a w')) ∧ ∀ t i, finPartPi (Pi.single i (at1 w t) : V4 F) = 0 := by
  intro F _ _ _ w
  have hp : ∀ (w' : InfinitePlace F) (t : ℝ), TR.pInf F (at1 w' t) = Pi.single w' t := fun _ t => (TR.infEq F).symm_apply_apply _
  have h2 : ∀ (w' : InfinitePlace F) (t : ℝ), (at1 w' t).2 = 0 := fun _ t => rfl
  have hfin : ∀ x y : A F, (x + y).2 = x.2 + y.2 := fun _ _ => rfl
  have hmul : ∀ x y : A F, (x * y).2 = x.2 * y.2 := fun _ _ => rfl
  refine ⟨fun t => ?_, h2 w, hp w, fun s t => ?_, ?_, fun t a => ?_, fun a ha => ?_, fun t i => ?_⟩
  · rw [(UpperTheory.ConvolutionTheory.R2.C.splitA F).2 (at1 w t), hp, h2, AddChar.map_zero_eq_one, Circle.coe_one, mul_one,
      Finset.prod_eq_single w]
    · simp [cc]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ w) h
  · refine TR.ad_ext ?_ ?_
    · rw [map_add, hp, hp, hp, Pi.single_add]
    · change (at1 w (s + t)).2 = (at1 w s + at1 w t).2
      rw [hfin, h2, h2, h2, add_zero]
  · refine TR.ad_ext ?_ ?_
    · rw [hp, map_zero, Pi.single_zero]
    · change (at1 w 0).2 = (0 : A F).2
      rw [h2]
      rfl
  · refine TR.ad_ext ?_ ?_
    · rw [map_mul, hp, hp]
      ext w'
      by_cases h : w' = w
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    · change (at1 w t * a).2 = (at1 w (t * TR.pInf F a w)).2
      rw [h2, hmul, h2, zero_mul]
  · refine TR.ad_ext ?_ ?_
    · rw [map_sum]
      simp_rw [hp]
      ext w'
      simp [Finset.sum_apply, Pi.single_apply]
    · change a.2 = (∑ w', at1 w' (TR.pInf F a w')).2
      rw [ha]
      have : ∀ s : Finset (InfinitePlace F), (∑ w' ∈ s, at1 w' (TR.pInf F a w')).2 = 0 := by
        intro s
        induction s using Finset.induction_on with
        | empty => rfl
        | insert b s hb ih => rw [Finset.sum_insert hb, hfin, h2, ih, add_zero]
      exact (this _).symm
  · funext j
    by_cases h : j = i
    · subst h
      simp [finPartPi, h2]
    · simp [finPartPi, Pi.single_eq_of_ne h]
