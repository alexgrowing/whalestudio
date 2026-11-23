import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiesOverFramedOfSquareLevelMoves
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsConjLevelMapByLevelMoves
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculusStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevMoveCommLevelMapOfTrivialMod
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.LevPullEquiv

set_option maxHeartbeats 1000000 in

theorem pull_actLev : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (G G₂ : Type) [Group G] [Group G₂] (lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La) (lev₂ : G₂ → Dw.La →ₗ[𝓞 D.host.E] Dw.La), ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) → ActLev (Xo := d.Xo₂) d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) → ∀ (g : G) (g₂ : G₂), CongMod l.Mb (lev₂ g₂) (lev g) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ f₂ ∈ sec d.Xo₂ d.c₂ a n, Pull d f f₂ → Pull d (actLev c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g f) (actLev d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g₂ f₂) := by
  intro D j H Dw l Xo c d hpq hlev hA2 hbase G G₂ _ _ lev lev₂ hact hact₂ g g₂ hcong a n f hf f₂ hf₂ hpull
  intro k _ _ _ _ hk y₂ y hov
  have e1 : evR Xo c (actLev c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g f) y =
      evR Xo c f (mvPt _ _ g y) :=
    evalAt_actL hact (GlobalTheory.TransferCompare.evalWD_framed _ _) frMap_trans_id g hf.1 y
  have e2 : evR d.Xo₂ d.c₂ (actLev d.c₂ (fun g => (lev₂ g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g₂ f₂) y₂ =
      evR d.Xo₂ d.c₂ f₂ (mvPt _ _ g₂ y₂) :=
    evalAt_actL hact₂ (GlobalTheory.TransferCompare.evalWD_framed _ _) frMap_trans_id g₂ hf₂.1 y₂
  rw [e1, e2]
  obtain ⟨ρ, ν, hi, hmv, hfm⟩ := mvPt_spec hact.total g y
  obtain ⟨ρ₂, ν₂, hi₂, hmv₂, hfm₂⟩ := mvPt_spec hact₂.total g₂ y₂
  obtain ⟨hd, hM, -, -, -, hE, hlift, -, -⟩ := id hlev
  obtain ⟨r', m', hsq₁, hsq₂, hE'⟩ := GlobalTheory.exists_conj_levelMap D.host.E H Dw l Xo c 0 d hE ρ ν (asIso ρ₂) ν₂
    (lev g) LinearMap.id (lev₂ g₂) LinearMap.id hmv hmv₂ hcong (fun x => ⟨0, by simp⟩)
  have hov' := GlobalTheory.frOver_of_square_of_frMove D.host.E H Dw l Xo c 0 d ρ ν ρ₂ ν₂ r' m' hsq₁ hsq₂ k y _ y₂ _ hov hfm hfm₂
  obtain ⟨z₂, hz₂⟩ := hlift k hk _
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have hN := GlobalTheory.levelMaps_closed hL D.host.E H Dw hpq
  obtain ⟨g', ρ', ν', hg', -, hmv', hfm'⟩ :=
    GlobalTheory.exists_levMove_of_frOver hL D.host.E H Dw l Xo c 0 d hN hd hM hE r' m' hE' k hk _ z₂ _ hz₂ hov'
  obtain ⟨e₁, e₂⟩ := GlobalTheory.levMove_comm_levelMap_of_trivial_mod D.host.E H Dw l Xo c 0 d hpq hlev hA2 hbase ρ'.hom ν'
    (g'.f d.l₂.M) (g'.f d.l₂.A) inferInstance hmv' (fun x => GlobalTheory.LevelFibre.sub_mem_of_inGam hd hg' x)
  obtain ⟨⟨ι, hι, hone⟩, -, -⟩ := GlobalTheory.T.framedPointMove_calculus D.host.E H Dw l Xo c
  have hfin := GlobalTheory.frOver_of_square_of_frMove D.host.E H Dw l Xo c 0 d (𝟙 _) ι ρ'.hom ν' d.r d.m
    (by rw [e₁, Category.comp_id]) (by rw [e₂, hι, Category.comp_id]) k _ _ z₂ _ hz₂ (hone k _) hfm'
  exact hpull k hk _ _ hfin

end GlobalTheory.LevPullEquiv
