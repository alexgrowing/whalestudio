import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTPh
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRepIntertwinerImageModelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEvaluationMapSmoothAutomorphicValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEvaluationIntertwinerCuspidalValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEvaluationHasRowLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEquivariantRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIntertwinerMapSobolevContinuousEachSlotStatement
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem exists_multR_eval_of_star_mem : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ φ : L2X X, star φ ∈ HHX X → ∃ S ∈ MultR R F, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) := by
  intro hIC hCD hDU hFD D G' _ _ Pl0 T A Ks _ _ _ R F X h t hιE hgap hlev hinf hν0 hsee c v₀ hc hv₀ φ hφ
  obtain ⟨Φ, hΦ, hΦw⟩ := Formalism.L2.SG.EvalTOnto.rows_eq_hom X (fun v => Formalism.L2.SG.EvalTPh.phLoc_int_of_gap X hgap v) (star φ) hφ
  have hrep := GlobalTheory.T.exists_continuousRep_intertwinerImage_models hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ
  have hmm : IsMultMap R.θ (MP R) (JR R F) (chiR R F) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t) :=
    { aut := GlobalTheory.T.conjugateEvaluationMap_smooth_automorphic_values hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep
      cusp := GlobalTheory.T.conjugate_evaluation_intertwiner_cuspidal_values hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep
      lev := GlobalTheory.T.conjugatedIntertwinerEvaluation_has_row_level hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep
      equiv := fun τ g hg v w hw => GlobalTheory.T.conjugated_intertwiner_equivariant_real_place hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep τ g hg v w hw
      cont := fun τ v x => GlobalTheory.T.conjIntertwinerMap_sobolevContinuous_separately hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep τ v x }
  have hmem : GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t ∈ MultR R F := (Submodule.span_le (p := MultR R F)).1 le_rfl hmm
  refine ⟨GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t, hmem, ?_⟩
  · have hw : GlobalTheory.ConjRowMult.vecC X (MP R) c v₀ = X.B.w := GlobalTheory.ConjRowMult.vecC_eq X (MP R) c v₀ X.B.w hv₀
    obtain ⟨ψ, hψ⟩ := hrep v₀
    rw [hw, hΦw] at hψ
    have key : ∀ x, ev (MP R) v₀ (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t) ((iotaX X h).symm x * t) = star (ψ x) := by
      intro x
      rw [ev_apply]
      refine (GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t v₀ _).trans ?_
      rw [hw, hΦw, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
      have e : ∀ a b : GA D (D.sp.Y 0), a * b * b⁻¹ = a := fun a b => mul_inv_cancel_right a b
      erw [e, ContinuousMulEquiv.apply_symm_apply]
    filter_upwards [hψ.2.2, Lp.coeFn_star φ] with x h1 h2
    rw [key x, ← h1, h2, Pi.star_apply, star_star]

end GlobalTheory.Mem.SRe

end
