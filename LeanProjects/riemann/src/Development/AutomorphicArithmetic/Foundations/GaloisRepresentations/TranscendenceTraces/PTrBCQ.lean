import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trBCQ_of :
    TrHl → TrBC → WtBC → TrBCQ := by
  intro hHl hBC hWt l _ n i Z' S' Z S v p' p g _ w hpb hw hl
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  have hw' : IsWt p' (Wt.comap v w) := hWt v p' p g w hpb hw
  have hl' : IsUnit ((l : ℕ) : Γ(S', ⊤)) := by
    have := hl.map g.appTop.hom
    rwa [map_natCast] at this
  have key : pullHl l (sch.map g) n i ∘ₗ trHl l p w n i =
      trHl l p' (Wt.comap v w) n i ∘ₗ pullHl l (sch.map v) n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    have hk : IsUnit ((↑(l ^ k) : ℕ) : Γ(S, ⊤)) := by
      rw [Nat.cast_pow]
      exact hl.pow k
    show (pull (ZMod (l ^ k)) (sch.map g) (tw (l ^ k) i) n) ((trHl l p w n i x).1 k) =
      (trHl l p' (Wt.comap v w) n i (pullHl l (sch.map v) n i x)).1 k
    rw [hHl l n i p w hw hl x k, hHl l n i p' (Wt.comap v w) hw' hl' _ k]
    exact hBC (l ^ k) n i v p' p g w hpb hw hk (x.1 k)
  unfold trHQ pullHQ
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, key]
