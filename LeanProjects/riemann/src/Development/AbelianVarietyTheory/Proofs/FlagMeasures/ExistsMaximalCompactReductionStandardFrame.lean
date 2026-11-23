import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsIdentificationFstEqOneOfFiniteAdelicStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedTypePrimePlacesChoiceOnePerConjugatePairStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReducedMatrixOfActsAsDegreeOnePrimeFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFixedPlaceConjugatorLiftsActByReductionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabPin

theorem frameRed_exists : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ c red, FrameRed X h t PY c red := by
  intro D X h t PY hF hstd hι
  obtain ⟨c, fr, hB⟩ := GlobalTheory.T.exists_fixed_place_conjugator_lifts_act_by_reductions D X h t PY hF hstd hι (GlobalTheory.T.cmField_splitPlace_eq_of_place_eq D.host.E)
  obtain ⟨ρ, hρ⟩ := GlobalTheory.RowLev.exists_red_actsBy X.B.I D.R.r D.host.g D.nd.PlG
    (fun k v => Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw k v)) fr X.n_eq (GlobalTheory.T.fixedTypePrimePlaces_choice_one_per_conjugate_pair D X)
  have hg : X.B.g = D.host.g 0 * D.host.g 1 := X.g_eq
  refine ⟨c, ρ.toFun, ⟨?_, ?_, ?_, ?_⟩, fun kv => GlobalTheory.T.exists_splitPlace_eq_fixedTypePrimePlace D kv, ?_⟩
  · intro k hk kv
    exact (Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ k _).2
      (GlobalTheory.T.reducedMatrix_of_actsAs_degree_one_prime_frame X.B.I D.R.r (D.host.g kv.1) _ (fr kv.1 kv.2) k hk _ (hρ k hk kv.1 kv.2))
  · exact ρ.map_mul
  · exact ρ.surj
  · intro k hk
    rw [hg]
    exact ρ.ker k hk
  · intro kv s hs x γ hx
    obtain ⟨hK, hact, hoth⟩ := hB kv s hs x γ hx
    set k := (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 with hk
    have hfin : (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).1 = 1 := by
      apply GlobalTheory.T.rowsIdentification_fst_eq_one_of_finiteAdelic D X h
      have hn : (GfC (D.sp.Y 0)).Normal := by unfold GfC; infer_instance
      exact hn.conj_mem _ (PY.into _) t
    refine ⟨k, hK, ?_, ?_, ?_⟩
    · obtain ⟨g, hg'⟩ : ∃ g : Formalism.L2.Theta.GA D (D.sp.Y 0), g = PY.ψ (c * x * c⁻¹) := ⟨_, rfl⟩
      have e : (Formalism.L2.SG.RowsJoinPinned.iotaX X h).symm (1, k) = MulAut.conj t g := by
        rw [ContinuousMulEquiv.symm_apply_eq, hg']
        exact Prod.ext hfin.symm rfl
      show PY.ψ (c * x * c⁻¹) = (t⁻¹ * (Formalism.L2.SG.RowsJoinPinned.iotaX X h).symm (1, k) * t : Formalism.L2.Theta.GA D (D.sp.Y 0))
      rw [e, MulAut.conj_apply, ← hg']
      exact (by group : g = t⁻¹ * (t * g * t⁻¹) * t)
    · exact Units.ext (GlobalTheory.RowLev.PlFrame.ActsAs.unique (fr kv.1 kv.2) hK (hρ k hK kv.1 kv.2) hact)
    · intro kv' hne
      exact Units.ext (GlobalTheory.RowLev.PlFrame.ActsAs.unique (fr kv'.1 kv'.2) hK (hρ k hK kv'.1 kv'.2) (hoth kv' hne))

end GlobalTheory.LabPin
