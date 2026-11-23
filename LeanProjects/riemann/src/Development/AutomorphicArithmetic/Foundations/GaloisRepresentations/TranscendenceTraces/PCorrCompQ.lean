import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrCompQ_of :
    CycComp → WtBC → WtComp → TrBCQ → TrCompQ → CorrCompQ := by
  intro hC hBC hWC hTB hTC S Y X c d
  haveI := c.fin
  haveI := d.fin
  have pb := IsPullback.of_hasPullback d.p c.f
  have hbw := hBC _ _ d.p c.f d.w pb d.wt
  have hw := hWC (pullback.snd d.p c.f) c.p (Wt.comap (pullback.fst d.p c.f) d.w) c.w hbw c.wt
  let e : Corr S X := ⟨pullback d.p c.f, pullback.snd d.p c.f ≫ c.p, pullback.fst d.p c.f ≫ d.f,
    Wt.mul (pullback.snd d.p c.f) (Wt.comap (pullback.fst d.p c.f) d.w) c.w, inferInstance, hw⟩
  refine ⟨e, pullback.fst d.p c.f, pullback.snd d.p c.f, pb, rfl, rfl, rfl, ?_, ?_⟩
  · exact hC c d e _ _ pb rfl rfl rfl
  · intro l _ n i hl hl2
    have hpull : pullHQ l (sch.map (pullback.fst d.p c.f ≫ d.f)) n i =
        pullHQ l (sch.map (pullback.fst d.p c.f)) n i ∘ₗ pullHQ l (sch.map d.f) n i := by
      simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]
    have key := hTB l n i _ _ d.p c.f d.w pb d.wt hl2
    show trHQ l (pullback.snd d.p c.f ≫ c.p) _ n i ∘ₗ pullHQ l (sch.map (pullback.fst d.p c.f ≫ d.f)) n i =
      (trHQ l c.p c.w n i ∘ₗ pullHQ l (sch.map c.f) n i) ∘ₗ (trHQ l d.p d.w n i ∘ₗ pullHQ l (sch.map d.f) n i)
    rw [hTC l n i _ _ _ _ hbw c.wt hl, hpull]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply]
    exact congrArg (trHQ l c.p c.w n i) (LinearMap.congr_fun key _).symm
