import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistsAtLinked
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvPSizeRowsDlog
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.ChiGrid

namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow

section Transfer

variable {D : Formalism.BasicNotions.D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem fieldHas_of_same {G G₀ : GridData Lc sc} {K : Type} [Field K] {e : K →+* ℂ} (hv : G.pl.v0 = G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) (h : FieldHas G₀ e) : FieldHas G e := by
  have hS : G.pl.S0 = G₀.pl.S0 := by unfold Places.S0; rw [hv]
  have hd : ∀ v, G.pl.depth sc v = G₀.pl.depth sc v := fun v => by unfold Places.depth; rw [hv]
  refine ⟨fun i h1 h2 => ?_, fun v hv' => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    have := hch ⟨a, by omega⟩
    simp only at this
    rw [this]
    exact h.values _ h1 h2
  · rw [hd]
    exact h.roots v (hS ▸ hv')

theorem lamOf_of_same {G G₀ : GridData Lc sc} (hw : G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) : lamOf G = lamOf G₀ := by
  unfold lamOf
  rw [hw]
  congr 1
  funext a
  exact hch a

end Transfer

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem gridFit_of_parts {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} (hs : TwistedPlaceChoiceLiesOverPair D ex.nch)
    (hc : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w))
    (hp : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w)))
    (h1 : Formalism.L2.Host.ValLL0 D p.R.C) (h2 : FieldHas G (Formalism.L2.Host.embLL0 D))
    (h3 : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp) (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G)) : GridFit p G :=
  ⟨h1, h2, hs, hc, hp, h3, h4⟩

theorem hasGrid_of_full (p : PtAt ex Csz) (CF : ℝ) (hp : p.Ties)
    (hs : TwistedPlaceChoiceLiesOverPair D ex.nch)
    (hc : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w))
    (hpw : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w)))
    (G : Grid p CF) (h2 : FieldHas G (Formalism.L2.Host.embLL0 D)) (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G))
    (hF : Full p.R.toRealDat G) : HasGrid (@Fld) p CF := by
  have hfit := gridFit_of_parts hs hc hpw hp.real.valLL0 h2 hp.real.psiChoice h4
  obtain ⟨W, M, ρ, ξ, cv, rm, S, rp, n, e, c, hIs, hOK, hSq⟩ := hF
  exact ⟨G, W, hIs.weil, hfit, n, ⟨M, ρ, ξ, cv, rm, S, rp, e, c⟩, ⟨hIs, hp.eSer, hOK, hSq⟩⟩

end GlobalTheory.Mem.LiteralAutomorphy.GridRow

namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow

theorem rowE_hasGrid_fld : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (CF : ℝ) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEl hL CF K B f T w Z Wt p0 t nch n xd c)) → RowE (IsGoodE (prmR (NEa hL N (GridA CF)) S Γ).s) (IsLinked (prmR (NEa hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.Ties → GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF := by
  intro hL CF N S Γ hN
  refine ((GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.twists_at_linked hL (prmR (NEa hL N (GridA CF)) S Γ) (IsGoodE (prmR (NEa hL N (GridA CF)) S Γ).s)).and
    ((rowE_pinned_grid hL CF N S Γ hN).and (rowE_full_grid hL CF N S Γ))).imp fun κ K β c b _ _ _ H t ht => ?_
  obtain ⟨hw1, hw2, hcond, hpow⟩ := H.1
  obtain ⟨G₀, hF₀, hT₀⟩ := H.2.1 t ht
  obtain ⟨G, hv, hw, hch, hFull⟩ := H.2.2 t ht G₀
  exact hasGrid_of_full _ CF ht ⟨hw1, fun w w' a b c => (hw2 w w' a b c).2.2⟩ hcond hpow G (fieldHas_of_same hv hch hF₀)
    (lamOf_of_same hw hch ▸ hT₀) hFull

end GlobalTheory.Mem.LiteralAutomorphy.GridRow
