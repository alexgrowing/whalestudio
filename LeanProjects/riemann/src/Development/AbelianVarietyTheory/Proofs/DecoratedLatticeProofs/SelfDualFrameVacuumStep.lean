import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaStepVectorEqTupleCombOfLevelCombStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDisjointIdempotentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamSplit

theorem stepVecOf_unique {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    {LS : LevDat D.host.E ℂ S.rank} {χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f f' : WO S T → ℂ}
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f)
    (h' : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f') : f = f' := by
  obtain ⟨-, e, he, hθ⟩ := h
  obtain ⟨-, e', he', hθ'⟩ := h'
  obtain rfl := GlobalTheory.DatumFourier.idemSum_unique S he he'
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  rw [hall Tm hTm, hθ'.2 Tm hTm]

end GlobalTheory.FamSplit

namespace GlobalTheory.FamSplit

theorem split_datum : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (j : ℕ), j < D.R.m → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ), IsSDFrame V β Λ 1 ∨ IsSDFrame V β Λ (D.host.g 0 * D.host.g 1) → IsVacO (pk W).ψ (pk W).θ (Yc D j) V (cart ((pk W).MY j)) (cart M) ((pk W).ΛY j) Λ vac → ∃ dG, IsDG W j M Λ β vac dG ∧ ∀ t, ∃ dQ, IsDQ W t j M Λ β vac dQ ∧ ∀ v, IsStepVecOf (pk W).ψ (pk W).θ (Yc D j) V (cart ((pk W).MY j)) (cart M) ((pk W).ΛY j) Λ ((pk W).βY j) β ((pk W).datYt t j (lvP W)) ((pk W).chi (j + 1)) ((pk W).Q t) ((pk W).xiR t) vac v ↔ v = comb (pk W).ψ _ _ dQ (comb (pk W).ψ _ _ dG vac) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW j hj V S M Λ β vac hSD hvac
  have hLev := hW.bot.hyp.2.2.2.1.lev
  obtain ⟨cY, hY⟩ := hLev.βY j hj
  have sdY : IsSelfDualC (Yc D j) ((pk W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY j hj)
  have frY : Formalism.L2.DIV.IsFrame ((pk W).βY j) ((pk W).ΛY j) := hY.1
  have sdV : IsSelfDualC V Λ := hSD.elim (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _)
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _)
  have frV : Formalism.L2.DIV.IsFrame β Λ := hSD.elim (fun h => h.elim fun _ h => h.1) (fun h => h.elim fun _ h => h.1)
  have hex := GlobalTheory.PlaceDatum.stepVecExists D
  obtain ⟨⟨eG, heG⟩, hQt⟩ := GlobalTheory.T.level_places_disjoint_idempotents W hW
  obtain ⟨fG, hfG⟩ := hex (pk W).ψ (pk W).θ (Yc D j) V (cart ((pk W).MY j)) (cart M) ((pk W).ΛY j) Λ ((pk W).βY j) β
    (datY _ D.R.r D.R.t j (r_le_Y j) (pk W).Pg ∅ (lvP W) (pk W).chi (fun _ => 1) Frm.B) ((pk W).chi (j + 1)) ∅
    (fun _ => 1) sdY sdV frY frV (Finset.disjoint_empty_right _) ⟨eG, heG⟩ vac hvac
  obtain ⟨dG, hdG, rfl⟩ := GlobalTheory.T.levelStepVector_eq_heisenbergCombination_vacuum D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdV frY frV hfG
  have hdG' : GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) dG := by
    simpa only [datY, Finset.union_empty] using hdG
  refine ⟨dG, ⟨hdG', hfG⟩, fun t => ?_⟩
  obtain ⟨hdis, hne, ⟨e, he⟩, ⟨eQ, heQ⟩⟩ := hQt t
  obtain ⟨fQ, hfQ⟩ := hex (pk W).ψ (pk W).θ (Yc D j) V (cart ((pk W).MY j)) (cart M) ((pk W).ΛY j) Λ ((pk W).βY j) β
    (datY _ D.R.r D.R.t j (r_le_Y j) ∅ ((pk W).Q t) (LevelP.triv _ _ _) (pk W).chi ((pk W).xiR t) Frm.B)
    ((pk W).chi (j + 1)) ((pk W).Q t) ((pk W).xiR t) sdY sdV frY frV (Finset.disjoint_empty_left _) ⟨eQ, heQ⟩ vac hvac
  obtain ⟨dQ, hdQ, rfl⟩ := GlobalTheory.T.levelStepVector_eq_heisenbergCombination_vacuum D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdV frY frV hfQ
  have hdQ' : GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 D.host.F)) dQ := by
    simpa only [datY, Finset.empty_union] using hdQ
  have hfull := GlobalTheory.T.thetaStepVector_eq_tupleComb_of_levelComb D _ _ (Yc D j) V _ _ _ _ _ _ D.R.r D.R.t j (r_le_Y j) (pk W).Pg ((pk W).Q t) (lvP W) (pk W).chi
    ((pk W).chi (j + 1)) ((pk W).xiR t) vac dG dQ sdY sdV frY frV hdis hne ⟨e, he⟩ hdG' hdQ' hfG hfQ
  refine ⟨dQ, ⟨hdQ', hfQ⟩, fun v => ⟨fun hv => stepVecOf_unique hv hfull, ?_⟩⟩
  rintro rfl
  exact hfull

end GlobalTheory.FamSplit
