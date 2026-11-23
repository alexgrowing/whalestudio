import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemFin

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocPlSplit

theorem nonempty_of_not_isConjPl {D : D7} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w) :
    Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F (w.under (𝓞 D.host.F))) := by
  obtain ⟨-, ι, -⟩ := Formalism.IndefR.Fin.idem_data w h (w.under (𝓞 D.host.F)) rfl
  exact ⟨ι⟩

theorem locPl_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ locPl G t →
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F (w.under (𝓞 D.host.F))) := by
  intro D T L sc G μ₀ hL t w hw
  refine nonempty_of_not_isConjPl ?_
  rcases Finset.mem_union.1 hw with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨e, he⟩ := G.pl.w_split v hv
    exact Formalism.IndefR.Fin.idemAt_split he
  · exact (hL.Q_pl t w h).2 w h

end GlobalTheory.LocPlSplit
