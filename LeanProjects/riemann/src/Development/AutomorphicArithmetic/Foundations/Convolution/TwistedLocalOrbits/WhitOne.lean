import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.whitOne :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → π.IsIrreducible → ∀ ψ : AddChar E Circle, Continuous ψ → ψ ≠ 1 →
      Module.rank ℂ (TwJacquet π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n)) ≤ 1 := by
  intro E _ _ _ _ n V _ _ π hs hirr ψ hψc hψ1
  exact PositivityTheory.rg.gu.whit.whitLeOne E n ψ V π hs hirr hψc hψ1
