import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionRealSubfieldRingEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.SplitByCompl

theorem eq_of_w_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L),
    s.w = s'.w → s = s' := by
  intro L _ _ _ s s' h
  have hv : s.v = s'.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  obtain ⟨v, si⟩ := s
  obtain ⟨v', si'⟩ := s'
  dsimp only at hv
  subst hv
  obtain ⟨i, hi, -, hix⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L ⟨v, si⟩
  obtain ⟨i', hi', -, hix'⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L ⟨v, si'⟩
  dsimp only at hix hix'
  generalize hw : SplitPlace.w ⟨v, si⟩ = w at i hix hi
  generalize hw' : SplitPlace.w ⟨v, si'⟩ = w' at i' hix' hi'
  have hww : w = w' := hw.symm.trans (h.trans hw')
  subst hww
  have e : (i' : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) = i :=
    DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) v).equalizer
      hi' hi (funext fun y => by
        have h1 := hix (algebraMap _ L y)
        have h2 := hix' (algebraMap _ L y)
        rw [AlgHom.commutes] at h1 h2
        exact h2.trans h1.symm))
  have e' : ∀ x, i' x = i x := fun x =>
    congrArg (fun f : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L => f x) e
  have hs : si = si' := AlgHom.ext fun x => i.injective (by rw [hix, ← e', hix'])
  rw [hs]

end GlobalTheory.SplitByCompl
