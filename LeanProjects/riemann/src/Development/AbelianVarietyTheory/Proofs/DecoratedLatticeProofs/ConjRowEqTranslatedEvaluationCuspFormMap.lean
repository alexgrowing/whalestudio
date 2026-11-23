import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesTestDataOfNoncompactGapsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesSmoothAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesIsCuspFunStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapHasLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapIntertwinesRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjIntertwinerPointValueSobolevContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SeeOnto

theorem see_onto : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ φ : L2X X, star φ ∈ HHX X → ∃ T ∈ MultT θ M J χ, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) := by
  intro hDS D X h θ S M J χ t v₀ hS hθ hGap hIdE hM hCV φ hφ
  obtain ⟨c, hc, hv₀⟩ := hCV
  have hL := (GlobalTheory.T.discreteSeriesTestData_of_noncompactGaps D X hGap).2.2.2.2.2
  obtain ⟨Φ, hΦ, hΦw⟩ := Formalism.L2.SG.EvalTOnto.rows_eq_hom X hL (star φ) hφ
  have hrep := GlobalTheory.T.exists_continuous_leftInvariant_rep_conjugateTensor hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ
  have hmult : GlobalTheory.ConjRowMult.conjMap X M c Φ h t ∈ Mult θ M J χ :=
    Submodule.subset_span
      ⟨GlobalTheory.T.conjugateIntertwiner_values_smoothAutomorphic hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       GlobalTheory.T.conjugateIntertwiner_values_isCuspFun hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       GlobalTheory.T.conjugate_evaluation_map_has_level hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       fun τ g hg v w hw => GlobalTheory.T.conjugate_evaluation_map_intertwines_real_places hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep τ g hg v w hw,
       fun τ v x => GlobalTheory.T.conjIntertwiner_pointValue_sobolevContinuous hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep τ v x⟩
  refine ⟨PiTensorProduct.lift (GlobalTheory.ConjRowMult.conjMap X M c Φ h t), (mem_multT θ M J χ _).2 (by simpa using hmult), ?_⟩
  have hw : GlobalTheory.ConjRowMult.vecC X M c v₀ = X.B.w := GlobalTheory.ConjRowMult.vecC_eq X M c v₀ X.B.w hv₀
  obtain ⟨ψ, hψ⟩ := hrep v₀
  rw [hw, hΦw] at hψ
  have key : ∀ x, evS X h t (PiTensorProduct.lift (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) (PiTensorProduct.tprod ℂ v₀)) x = star (ψ x) := by
    intro x
    rw [evS, PiTensorProduct.lift.tprod]
    refine (GlobalTheory.ConjRowMult.conjMap_apply X M c Φ h t v₀ _).trans ?_
    rw [hw, hΦw, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    have e : ∀ a b : GA D (D.sp.Y 0), a * b * b⁻¹ = a := fun a b => mul_inv_cancel_right a b
    erw [e, ContinuousMulEquiv.apply_symm_apply]
  filter_upwards [hψ.2.2, Lp.coeFn_star φ] with x h1 h2
  rw [key x, ← h1, h2, Pi.star_apply, star_star]

end GlobalTheory.Core.SeeOnto

end
