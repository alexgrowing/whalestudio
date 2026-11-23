import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.TendstoPowZeroOfValuation
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import GroundTheory.GlobalFields.SemilocalAlgebras.LocalDegree

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I.PlaceCoordinates

open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem cont_symm (v : P F) (w : P E) (i : Kv v ≃+* Kv w) (hi : Continuous i) :
    Continuous i.symm := by
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  exact i.toEquiv.continuous_symm_iff.2
    (AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi)

private theorem eq_completionMap (v : P F) (w : P E) [w.asIdeal.LiesOver v.asIdeal] (i : Kv v →+* Kv w)
    (hi : Continuous i) (hc : ∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) (k : Kv v) :
    i k = completionMap v w k := by
  have h := (HeightOneSpectrum.denseRange_algebraMap F v).equalizer hi (continuous_completionMap v w)
    (funext fun x => by
      simp only [Function.comp]
      rw [hc, completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (Kv w)])
  exact congrFun h k

private theorem eq_of_below_self {w w' : P E} (h : Below w w') : w' = w := by
  refine HeightOneSpectrum.ext ?_
  rw [show w.asIdeal = _ from h]
  ext x
  exact Iff.rfl

private theorem coord (D : Dat F E) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * D.θ := by
  refine ⟨D.b.repr x 0, D.b.repr x 1, ?_⟩
  conv_lhs => rw [← D.b.sum_repr x]
  simp [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def]

private theorem place_eq (D : Dat F E) (v : P F) (w w' : P E) [w'.asIdeal.LiesOver v.asIdeal]
    (i : Kv v ≃+* Kv w) (hi : Continuous i)
    (hc : ∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x))
    (h : completionMap v w' (i.symm (algebraMap E (Kv w) D.θ)) = algebraMap E (Kv w') D.θ) : w' = w := by
  have hF : ∀ a : F, i.symm (algebraMap E (Kv w) (algebraMap F E a)) = algebraMap F (Kv v) a := fun a => by
    rw [← hc, RingEquiv.symm_apply_apply]
  refine eq_of_below_self (I.below E E w w' ((completionMap v w').comp i.symm.toRingHom)
    ((continuous_completionMap v w').comp (cont_symm v w i hi)) fun x => ?_)
  obtain ⟨a, b, rfl⟩ := coord D x
  change completionMap v w' (i.symm (algebraMap E (Kv w) _)) = algebraMap E (Kv w') _
  simp only [map_add, map_mul, hF, h, completionMap_algebraMap, Algebra.algebraMap_self, RingHom.id_apply,
    IsScalarTower.algebraMap_apply F E (Kv w')]

private theorem sE_snd_above (D : Dat F E) (v : P F) (θ k : Kv v) (w' : P E)
    [hl : w'.asIdeal.LiesOver v.asIdeal] :
    (sE D v θ k).2 w' = completionMap v w' (k / 2) +
      completionMap v w' (k / (2 * θ)) * algebraMap E (Kv w') D.θ := by
  have hb : AdeleBaseChange.below F w' = v := (below_eq_iff _ _).2 hl
  subst hb
  obtain ⟨-, -, hs, -⟩ := sgLaws F (AdeleBaseChange.below F w')
  change completionMap (AdeleBaseChange.below F w') w' ((sg (AdeleBaseChange.below F w') (k / 2)).2 (AdeleBaseChange.below F w')) +
    completionMap (AdeleBaseChange.below F w') w' ((sg (AdeleBaseChange.below F w') (k / (2 * θ))).2 (AdeleBaseChange.below F w')) * algebraMap E (Kv w') D.θ = _
  rw [show (sg (AdeleBaseChange.below F w') (k / 2)).2 (AdeleBaseChange.below F w') = k / 2 from hs _,
    show (sg (AdeleBaseChange.below F w') (k / (2 * θ))).2 (AdeleBaseChange.below F w') = k / (2 * θ) from hs _]

private theorem sE_snd_not_above (D : Dat F E) (v : P F) (θ k : Kv v) (w' : P E) (hb : AdeleBaseChange.below F w' ≠ v) :
    (sE D v θ k).2 w' = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hs, -⟩ := sgLaws F v
  change completionMap (AdeleBaseChange.below F w') w' ((sg v (k / 2)).2 (AdeleBaseChange.below F w')) +
    completionMap (AdeleBaseChange.below F w') w' ((sg v (k / (2 * θ))).2 (AdeleBaseChange.below F w')) * algebraMap E (Kv w') D.θ = _
  rw [(hs _).2 _ hb, (hs _).2 _ hb, map_zero, zero_mul, add_zero]

private theorem sE_fst (D : Dat F E) (v : P F) (θ k : Kv v) : (sE D v θ k).1 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hs, -⟩ := sgLaws F v
  change InfinitePlace.infiniteAdeleRingMap (sg v (k / 2)).1 +
    InfinitePlace.infiniteAdeleRingMap (sg v (k / (2 * θ))).1 * (rt D.θ).1 = 0
  rw [(hs _).1, (hs _).1, map_zero, zero_mul, add_zero]

end UpperTheory.ConvolutionTheory.R2.I.PlaceCoordinates

open UpperTheory.ConvolutionTheory.R2.I.PlaceCoordinates GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange in
theorem UpperTheory.ConvolutionTheory.R2.I.place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (w : P E) (i : Kv v ≃+* Kv w), Continuous i →
      (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) →
      ∃ θ : Kv v, θ ^ 2 = algebraMap F (Kv v) D.δ ∧ θ ≠ 0 ∧ ∀ k, sg w (i k) = sE D v θ k := by
  intro F E _ _ _ _ _ D v w i hi hc
  have hb : Below v w := I.below F E v w i.toRingHom hi hc
  haveI hl : w.asIdeal.LiesOver v.asIdeal := ⟨hb⟩
  have hθE : D.θ ≠ 0 := D.b1 ▸ D.b.ne_zero 1
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = i.symm (algebraMap E (Kv w) D.θ) := ⟨_, rfl⟩
  have hiθ : i θ = algebraMap E (Kv w) D.θ := by rw [hθ, RingEquiv.apply_symm_apply]
  have hsq : θ ^ 2 = algebraMap F (Kv v) D.δ := by
    apply i.injective
    rw [map_pow, hiθ, hc, ← map_pow, D.sq]
  have hne : θ ≠ 0 := fun h => hθE ((map_eq_zero _).1 (by rw [← hiθ, h, map_zero]))
  have h2 : (2 : Kv v) ≠ 0 := by
    have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
    exact two_ne_zero
  refine ⟨θ, hsq, hne, fun k => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, hs, -⟩ := sgLaws E w
  obtain ⟨-, -, hs0, -⟩ := sgLaws E w
  refine Prod.ext ((hs _).1.trans (sE_fst D v θ k).symm) (FiniteAdeleRing.ext E fun w' => ?_)
  by_cases hv : AdeleBaseChange.below F w' = v
  · haveI hl' : w'.asIdeal.LiesOver v.asIdeal := (below_eq_iff _ _).1 hv
    change (sg w (i k)).2 w' = (sE D v θ k).2 w'
    rw [sE_snd_above]
    by_cases hw : w' = w
    · subst hw
      have e := eq_completionMap v w' i.toRingHom hi hc
      have e' : ∀ x, completionMap v w' x = i x := fun x => (e x).symm
      rw [show (sg w' (i k)).2 w' = i k from hs0 _, e', e', ← hiθ, ← map_mul, ← map_add]
      congr 1
      field_simp
      ring
    · have hj : completionMap v w' θ ≠ algebraMap E (Kv w') D.θ := fun h =>
        hw (place_eq D v w w' i hi hc (hθ ▸ h))
      have hj2 : completionMap v w' θ ^ 2 = algebraMap E (Kv w') D.θ ^ 2 := by
        rw [← map_pow, hsq, completionMap_algebraMap, ← map_pow, D.sq,
          IsScalarTower.algebraMap_apply F E (Kv w')]
      have hneg : algebraMap E (Kv w') D.θ = -completionMap v w' θ := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 hj2 with h | h
        · exact absurd h hj
        · rw [h, neg_neg]
      rw [(hs _).2 _ hw, hneg, mul_neg, ← map_mul, ← map_neg, ← map_add]
      rw [show k / 2 + -(k / (2 * θ) * θ) = 0 by field_simp; ring, map_zero]
  · have hw : w' ≠ w := fun h => hv (h ▸ (below_eq_iff _ _).2 hl)
    exact ((hs _).2 _ hw).trans (sE_snd_not_above D v θ k w' hv).symm
