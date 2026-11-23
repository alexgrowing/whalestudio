import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBadStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

noncomputable section

namespace GlobalTheory.ChiRatStd

open GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT

set_option maxHeartbeats 1600000 in

theorem chiRatAll_of_reads {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
    {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (L : (I.stp u a i).Cl → Submodule (𝓞 B.host.E) (B.sp.X i).V) (hL : L = I.latAt u a i)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (L c.1)))
    (k : Ch → TC.GA B (B.R.N i))
    (hR : I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k)
    (hfin : ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) (β : Ch) :
    Formalism.L2.G.Cmp.ChiRatAll (K β).lev B.embLL := by
  subst hL
  obtain ⟨c, rfl⟩ := hR.onto β
  intro κ
  have hF : ChiFin I l Z (K (chOf c)).lev := by
    obtain ⟨n, hn, h⟩ := hfin (chOf c)
    exact ⟨n, hn, fun κ _ => h κ⟩
  obtain ⟨x, hx, ⟨q, hq⟩, -⟩ := GlobalTheory.T.exists_levelElement_same_character_near_bad I hOk hP l Z u a i hi bad Ch chOf K k hR c hF κ
  obtain ⟨κ', hg, hq', -⟩ := (hR.lev c x.1 q hq).1 x.2
  have hc := hR.chr c x κ' hg (by rw [hq']; exact hq)
  exact ⟨_, by rw [← hx]; exact hc.symm⟩

set_option maxHeartbeats 1600000 in

theorem chiRatAll_twChart : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch),
    V4.MuIsW (w.st Z) f T Wt w.I.xi →
    ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
    ∀ (u : (w.D Z).what₂.Word) (μ : (w.D Z).what₂.Tup) (hμ : μ ≠ (w.D Z).what₂.mu0) (j : ℕ) (hj : j + 1 ≤ (w.D Z).R.m)
      (β : tt.ch.Ch u μ (j + 1)),
      Formalism.L2.G.Cmp.ChiRatAll (tt.forms.ch u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (w.D Z).what₂.embLL := by
  intro K B f T w _ _ _ Z t Wt nch n _ tt hstd u μ hμ j hj β
  obtain ⟨k, hR⟩ := hstd.1.reads u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  exact chiRatAll_of_reads w.I w.ok w.pins w.l Z u μ (j + 1) hj _ _ _ (hstd.1.lat u μ (j + 1))
    (fun β => tt.forms.ch u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β) k hR
    (fun β => tt.forms.chi_fin u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β) β

end GlobalTheory.ChiRatStd
