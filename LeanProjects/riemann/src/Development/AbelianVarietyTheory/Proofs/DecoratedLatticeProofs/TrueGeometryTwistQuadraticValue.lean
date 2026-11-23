import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumFactorsOverTwistPrimesLocalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDisjointIdempotents
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam

theorem xi_eq_xiOff_mul_join : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ t (J : QJ a t), J.Reads → ∀ j (hj : j + 1 ≤ B.R.m) α γ z, J.A.xi j hj (J.ι j α) (J.ι (j + 1) γ) z = xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z * ∏ i, B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) (J.P i) (homOf I l Z j hj z)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ t J hJ j hj α γ z
  rw [(GlobalTheory.T.finiteDatum_factors_over_twistPrimes_local I hW.tr.ok hW.tr.tw l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is).1 j hj (J.ι j α) (J.ι (j + 1) γ) z]
  congr 1
  symm
  refine Finset.prod_bij (fun i _ => J.P i) ?_ ?_ ?_ ?_
  · intro i _
    rw [Finset.mem_filter, hJ.eq i]
    refine ⟨Finset.mem_univ _, fun h => ?_⟩
    exact Finset.disjoint_left.1 ((GlobalTheory.PkPlaces.pk_places W hW.pk).2 t).1 ((hW.lev.2.1 _).2 h) (J.mem i)
  · intro i₁ _ i₂ _ h
    exact hJ.inj (((hJ.eq i₁).symm.trans (congrArg Subtype.val h)).trans (hJ.eq i₂))
  · intro P hP
    have hv : P.1 ∉ (B.primes X).vGs := (Finset.mem_filter.1 hP).2
    have hq : P.1 ∈ Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := by
      rcases Finset.mem_union.1 P.2 with h | h
      · exact absurd h hv
      · exact h
    obtain ⟨i, hi⟩ := hJ.surj _ ((hW.tq.Q t P.1).2 hq)
    exact ⟨i, Finset.mem_univ _, Subtype.ext ((hJ.eq i).trans hi)⟩
  · intro i _
    rfl

end GlobalTheory.Fam
