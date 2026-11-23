import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistScalarStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QLevAt

theorem qLev_of_reads : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ t (J : QJ a t), J.Reads → ∀ row col (F : QFam a.v ((a.fam row col).t t)) (h : F.r = J.r), F.χ = chrK W t → (∀ i, HEq (F.Q i) (J.E (Fin.cast h i)).toAt) → QLev (a.fam row col) F := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT t J hJ row col F h hχ hQ
  obtain ⟨χ, r, Q, eqv⟩ := F
  dsimp only at h hχ hQ ⊢
  subst hχ
  obtain rfl : Q = fun i => (J.E (Fin.cast h i)).toAt := funext fun i => eq_of_heq (hQ i)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Equiv.ofBijective (fun i => ⟨J.pl (Fin.cast h i), J.mem _⟩) ⟨?_, ?_⟩, fun i => ?_⟩
    · intro i i' e
      have e' := hJ.inj (congrArg Subtype.val e)
      exact Fin.ext (by simpa using congrArg Fin.val e')
    · rintro ⟨PP, hPP⟩
      obtain ⟨i, hi⟩ := hJ.surj PP hPP
      exact ⟨Fin.cast h.symm i, Subtype.ext (by simp [hi])⟩
    · obtain ⟨ε, hε, h3⟩ := (J.G (Fin.cast h i)).q.above
      exact ⟨(J.G (Fin.cast h i)).idem,
        (GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G (Fin.cast h i)).idem hε h3).symm⟩
  · intro i j d hd hj x hx
    exact GlobalTheory.T.true_geometry_twist_value W hW u a ha haT t (J.pl (Fin.cast h i)) (J.mem _) (J.E (Fin.cast h i)) (hJ.res _) j d hd hj x hx
  · intro i x hx g hg
    exact GlobalTheory.T.true_geometry_twist_scalar W hW u a ha haT t (J.pl (Fin.cast h i)) (J.mem _) (J.E (Fin.cast h i)) x hx g hg

end GlobalTheory.QLevAt
