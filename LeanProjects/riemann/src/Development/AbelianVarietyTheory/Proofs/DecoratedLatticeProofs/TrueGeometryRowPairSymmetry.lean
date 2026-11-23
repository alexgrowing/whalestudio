import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFiniteIndexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFiniteIndexAltBis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Fam.LocLev

theorem prod_bij : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u) (t : W.P.T) (f : GlobalTheory.QTw.BadPr I (W.P.I.tup t) → ℂ) (g : Fin a.n → ℂ), (∀ n (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → f P = g n) → ∏ P ∈ Finset.univ.filter (fun P : GlobalTheory.QTw.BadPr I (W.P.I.tup t) => P.1 ∈ (B.primes X).vGs), f P = ∏ n, g n := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a t f g hfg
  have hv : ∀ n : Fin a.n, (a.pl n).1 ∈ (B.primes X).vGs := fun n => (hW.lev.2.1 _).1 (a.pl n).2
  refine Finset.prod_bij' (fun P hP => a.pl.symm ⟨P.1, (hW.lev.2.1 _).2 (Finset.mem_filter.1 hP).2⟩)
    (fun n _ => (⟨(a.pl n).1, Finset.mem_union.2 (Or.inl (hv n))⟩ : GlobalTheory.QTw.BadPr I (W.P.I.tup t)))
    (fun _ _ => Finset.mem_univ _) (fun n _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, hv n⟩) ?_ ?_ ?_
  · intro P hP
    apply Subtype.ext
    simp
  · intro n _
    simp
  · intro P hP
    apply hfg
    simp

theorem loc_all : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (pk W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat hi n j hj
  rcases lt_trichotomy (j + 2) B.R.m with h | h | h
  · exact GlobalTheory.T.true_geometry_finite_index W hW u a ha hat n j hj h
  · exact GlobalTheory.T.true_geometry_finite_index_alt W hW u a ha hat n j hj h
  · exact GlobalTheory.T.true_geometry_row_pair_identity W hW u a ha hat hi n j hj (by omega)

theorem xiLev_eq_const_mul_locFac : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : QJ a t), J.Reads → ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξl : Fin a.n → Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, (∀ n, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (pk W).ψ _ _ (a.pl n).1 ((a.G n).cg j) (Ξl n)) ∧ ∀ z, B.embLL (∏ P ∈ Finset.univ.filter (fun P : GlobalTheory.QTw.BadPr I (W.P.I.tup t) => P.1 ∈ (B.primes X).vGs), GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = C j * ∏ n, Ξl n z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat hi
  choose c hc hspec using fun n j hj => loc_all W hW u a ha hat hi n j hj
  refine ⟨fun j => if h : j + 1 ≤ B.R.m then ∏ n, c n j h else 1, fun j hj => ?_, ?_⟩
  · dsimp only
    rw [dif_pos (by omega)]
    exact Finset.prod_ne_zero_iff.2 fun n _ => hc n j _
  · intro t J hR j hj α γ
    choose Ξ hΞ hΞe using fun n => hspec n j hj t J hR α γ
    refine ⟨Ξ, hΞ, fun z => ?_⟩
    rw [map_prod, prod_bij W hW u a t _ (fun n => c n j hj * Ξ n z) (fun n P hP => hΞe n P hP z),
      Finset.prod_mul_distrib]
    dsimp only
    rw [dif_pos hj]

end GlobalTheory.Fam.LocLev
end
