import Development.WeilBound.CoreStatements.SatakeConjugation.CsdIff

noncomputable section

open NumberField IsDedekindDomain

namespace PositivityTheory.NCmp

open GlobalTheory.CuspRep

def SatFlipLoc : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (w : HeightOneSpectrum (𝓞 L))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion L))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
      GlobalTheory.LFun.HasSatGL (conjSrc (cc L) w) (σ.ρ.comp (ParLaws.flip (conjLoc (cc L) w) a)) (B.map (·⁻¹))

end PositivityTheory.NCmp
