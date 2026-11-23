import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.convFub :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.ConvFub := by
  classical
  intro hc E _ _ _ n f hf ⟨C, hC⟩ α X _ _ _ _ ν _ u a hu ha ⟨D, hD⟩ g
  have hS : MeasurableSet ((Set.univ : Set X) ×ˢ invSet E n) :=
    (isOpen_univ.prod GlobalTheory.CuspRep.isOpen_invSet).measurableSet
  have h1 : ContinuousOn (fun z : X × Lie E n => chart f (u z.1 * g) z.2) (Set.univ ×ˢ invSet E n) :=
    (hc E n f hf).1.comp (f := fun z : X × Lie E n => (u z.1 * g, z.2))
      (((hu.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
      fun z hz => ⟨trivial, hz.2⟩
  have h2 : Measurable fun z : X × Lie E n => chart f (u z.1 * g) z.2 := by
    have := h1.measurable_piecewise (g := fun _ => 0) continuousOn_const hS
    convert this using 1
    funext z
    by_cases hz : z ∈ (Set.univ : Set X) ×ˢ invSet E n
    · rw [Set.piecewise_eq_of_mem _ _ _ hz]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz, chart]
      exact dif_neg fun h => hz ⟨trivial, h⟩
  have hb : ∀ g y, ‖chart f g y‖ ≤ C := fun g y => by
    unfold chart
    split_ifs
    · exact hC _
    · simpa using (norm_nonneg _).trans (hC 1)
  haveI : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hα : Integrable (fun y => α y) (volume : Measure (Lie E n)) := α.integrable
  have ha' : Integrable a ν := Integrable.of_bound ha.measurable.aestronglyMeasurable D (.of_forall hD)
  have hi : Integrable (fun z : X × Lie E n => chart f (u z.1 * g) z.2 * (a z.1 * α z.2)) (ν.prod volume) :=
    (ha'.mul_prod hα).bdd_mul h2.aestronglyMeasurable (.of_forall fun z => hb _ _)
  calc ∫ x, conv f α (u x * g) * a x ∂ν
      = ∫ x, (∫ y, chart f (u x * g) y * (a x * α y)) ∂ν := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [conv]
        rw [← integral_mul_const]
        exact integral_congr_ae (.of_forall fun y => by ring)
    _ = ∫ y, ∫ x, chart f (u x * g) y * (a x * α y) ∂ν := integral_integral_swap hi
    _ = _ := by
        unfold conv
        refine integral_congr_ae (.of_forall fun y => ?_)
        simp only [chart]
        split_ifs with h
        · rw [← integral_mul_const]
          exact integral_congr_ae (.of_forall fun x => by simp only [mul_assoc])
        · simp
