import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameFOfDiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSRestRe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestVectorEvaluationIdentifiesLevelRowsConjStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationGoodRowsToConjugateGoodRowsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoicesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowIsometryConjugatedGoodRowsFinrankStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelColumnsGoodRowsLePrincipalAndFiniteDimensioStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdelicPointCarriesRowLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2

namespace GlobalTheory.Mem.SRe

set_option maxHeartbeats 4000000 in

theorem exists_sRest_top : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (F0 : ∀ u, Forms0 D u) (P : SPack D F0) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), GapHyp D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (t : GA D (D.sp.Y 0)) (c : ℝ), 0 < c ∧ SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ R eE P.X P.inst P.G t j ∧ ∀ (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F0 F'), ∃ (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)) (S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF)), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  intro hDS hHC hCusp hDSU hRF D G' _ _ Pl0 T A Ks _ _ _ R F F0 P eE hGap hph hL hR hDs hLev hGrp hPin hE0 hM hRange hNorm hDall
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_finiteAdelicPoint_carries_rowLevel D G' Pl0 T A Ks R F P.X P.inst P.pin hLev hGrp hPin hE0
  obtain ⟨v₀, hv, c, hc, hev⟩ :=
    GlobalTheory.T.lowestVector_evaluation_identifies_levelRows_conj hDS hCusp hDSU hRF D G' Pl0 T A Ks R F P.X P.inst t P.pin hGap hLev hM.inf hM.ν0 ht
  have hg := GlobalTheory.T.evaluation_goodRows_to_conjugate_goodRows D G' Pl0 T A Ks R F P.X P.inst P.G t v₀ c hLev hM.inf hv ht hev
  have hle := (GlobalTheory.T.levelColumnsGoodRows_le_principal_and_finiteDimensional hHC hCusp D G' Pl0 T A Ks R F hLev hM.inf hM.ν0).1
  obtain ⟨hfr, j, hj⟩ :=
    GlobalTheory.T.exists_rowIsometry_conjugatedGoodRows_finrank D G' Pl0 T A Ks R F P.X P.inst P.G t v₀ c eE hc hv hM.HE hRange hNorm hle hev hg.1
  refine ⟨hfr hDall, j, t, c, hc, ht, hg.2, hj, ?_⟩
  intro N hh F' hs
  have hF := GlobalTheory.T.finX_spectralRedivisionFullChoices D ⟨P.toNew (hfr hDall) j, N, hh⟩ P.X P.Y P.fin
  obtain ⟨S, hS⟩ := exists_sRest_re D F0 P (hfr hDall) j N hh F' hs hF hph hL hR hDs
  exact ⟨hF, S, hS⟩

end GlobalTheory.Mem.SRe
