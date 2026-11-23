import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FcLargeOfSup

noncomputable section

namespace GlobalTheory.LiftRef

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up Formalism.AUTREP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def autOf {D : D7} {μt : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μt j) (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W))
    (hS : NG.IsIrrRep Mr.wt.ρ S) : NG.AutRep D.host.E D.R.nV :=
  { Mr.wt with S := S, irrS := hS }

def AtRows (hL : GlobalTheory.Published.LocalLanglandsGL)
    (q : ∀ (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (Rw : RowSide D), ParIn hL D cf rep Rw →
      MtFam D → Prop) : Prop :=
  OverRows fun _ _ _ _ w Z _ _ _ _ Y => ∀ Rw (a : ParIn hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw) (M : MtFam (w.st Z).toD7) tup Q,
    MtAd Y M → MtInput (w.st Z).toD7 M tup Q → q (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw a M

theorem evG_and {p q : Ctx → Prop} (hp : EvG p) (hq : EvG q) : EvG fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 C5 c6 Cb he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (fc_large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (fc_large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx hg =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx) hg, hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx) hg⟩⟩

theorem evG_mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : EvG p) : EvG q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx hg => h X (ha3 X h1 h2 h3 h4 hx hg)⟩

theorem overRows_and_mono {p q r : RowP} (hp : OverRows p) (hq : OverRows q)
    (h : ∀ K B f T w Z Wt hX z p0 Y, p K B f T w Z Wt hX z p0 Y → q K B f T w Z Wt hX z p0 Y → r K B f T w Z Wt hX z p0 Y) :
    OverRows r := by
  unfold OverRows EvLgG at *
  refine evG_mono (fun K hK => ?_) (evG_and hp hq)
  refine large₂.mono (fun B f T _ hpq hKP w hw Z Wt hX z p0 Y h1 h2 h3 h4 h5 => ?_) (large₂.and hK.1 hK.2)
  exact h _ _ _ _ _ _ _ _ _ _ _ (hpq.1 hKP w hw Z Wt hX z p0 Y h1 h2 h3 h4 h5) (hpq.2 hKP w hw Z Wt hX z p0 Y h1 h2 h3 h4 h5)

end GlobalTheory.LiftRef

end
