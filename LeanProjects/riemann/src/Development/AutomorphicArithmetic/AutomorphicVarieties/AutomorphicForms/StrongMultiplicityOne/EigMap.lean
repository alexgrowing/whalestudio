import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}

private theorem sum_Tj {ϖ : w.adicCompletion E} (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ s : Finset (GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n),
      ∀ F : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * F c =
          ∑ c ∈ s, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * F c := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ j).2
  refine ⟨hf.toFinset, fun F => finsum_eq_sum_of_support_subset _ fun c hc => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hc

private theorem eig_zero (h : B.card = n) : Eig w B (fun _ : GL (Fin n) (w.adicCompletion E) => (0 : ℂ)) :=
  ⟨h, fun _ _ _ => rfl, fun _ _ _ _ _ => by simp⟩

private theorem eig_sub {W W' : GL (Fin n) (w.adicCompletion E) → ℂ} (h : Eig w B W) (h' : Eig w B W') :
    Eig w B (fun y => W y - W' y) := by
  refine ⟨h.card, fun g k hk => by simp only [h.inv g k hk, h'.inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  have e := h.eig ϖ hϖ j hj g
  have e' := h'.eig ϖ hϖ j hj g
  rw [hs] at e e' ⊢
  simp only [mul_sub, Finset.sum_sub_distrib, e, e']

private theorem eig_int {X : Type} [MeasurableSpace X] (μ : Measure X) (hB : B.card = n)
    (F : X → GL (Fin n) (w.adicCompletion E) → ℂ) (a : X → ℂ) (h : ∀ x, Eig w B (F x))
    (hi : ∀ y, Integrable (fun x => F x y * a x) μ) : Eig w B (fun y => ∫ x, F x y * a x ∂μ) := by
  refine ⟨hB, fun g k hk => by simp only [fun x => (h x).inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  rw [hs]
  simp only [← integral_const_mul]
  rw [← integral_finset_sum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := (h x).eig ϖ hϖ j hj g
  rw [hs] at e
  simp only [← mul_assoc, ← e, Finset.sum_mul]

end

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.StrongMultiplicityOne.eigMap :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.EigMap := by
  intro hC E _ _ _ n w B f hf
  refine ⟨fun hN g => ?_, fun hN α g => ?_, fun f' hf' g => eig_sub (hf g) (hf' g)⟩
  · refine eig_int ((vecMeasure E (Pos n)).restrict (vecDomain E (Pos n))) (hf 1).card
      (fun X y => f (uGL X * (g * finGL E n (locGL E n w y))))
      (fun X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) (fun X => ?_) fun y => ?_
    · simpa only [mul_assoc] using hf (uGL X * g)
    · have hc : Continuous fun X : Pos n → Ad E => f (uGL X * (g * finGL E n (locGL E n w y))) *
          (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
        (hN.cont.comp (continuous_uGL.mul continuous_const)).mul
          (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg))
      exact (hc.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure
  · refine eig_int volume (hf 1).card (fun x y => chart f (g * finGL E n (locGL E n w y)) x) α (fun x => ?_) fun y => ?_
    · by_cases hx : IsUnit (Matrix.of x)
      · have := hf (g * infGL E n hx.unit)
        simpa only [chart, dif_pos hx, mul_assoc, GlobalTheory.CuspRep.infGL_comm] using this
      · simpa only [chart, dif_neg hx] using eig_zero (w := w) (hf 1).card
    · obtain ⟨C, hC'⟩ := hN.bdd
      haveI : BorelSpace (Lie E n) := inferInstance
      haveI : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
      haveI : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      refine α.integrable.bdd_mul (c := C) ((hC E n f hN.cont).2 _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      unfold chart
      split_ifs
      · exact hC' _
      · simpa using (norm_nonneg _).trans (hC' 1)
