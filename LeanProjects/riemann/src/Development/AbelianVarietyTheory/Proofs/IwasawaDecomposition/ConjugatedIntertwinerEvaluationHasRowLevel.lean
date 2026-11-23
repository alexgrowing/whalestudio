import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerHasColumnLevel

open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
noncomputable section

namespace GlobalTheory.ConjRowLevelSee

theorem conjMap_level_of_seeAt : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ JR R F, ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = chiR R F k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t _ _ _ _ _ hsee c _ Φ hΦ hrep u (k : GA D (D.sp.Y 0)) hk (g : GA D (D.sp.Y 0))
  obtain ⟨ψ, hψ⟩ := hrep u
  show star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)))
      (iotaX X h ((g * k * t⁻¹ : GA D (D.sp.Y 0))))) = _ *
    star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)))
      (iotaX X h ((g * t⁻¹ : GA D (D.sp.Y 0)))))
  rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  obtain ⟨hJ, hχ⟩ := hsee.conj k
  have hmem := hJ.1 hk
  have hval := hχ hk
  set x := iotaX X h ((t⁻¹)⁻¹ * k * t⁻¹ : GA D (D.sp.Y 0)) with hxdef
  have hx : x.1 = 1 ∧ x.2 ∈ X.K2 := hmem
  have hxeq : x = (1, x.2) := Prod.ext hx.1 rfl
  have hΦk : X.B.R (1, x.2) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) =
      X.chi2 x.2 • Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)) := by
    obtain ⟨T', -, hT'⟩ := hΦ
    rw [← hT']
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (T' _)) (GlobalTheory.ConjRowLevel.reg_comp_Re X x.2 hx.2)
  have hrep2 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ (1, x.2)
  rw [hΦk] at hrep2
  have key := Formalism.L2.SG.EvalTOntoRep.contRep_unique X hrep2 (Formalism.L2.SG.EvalTOntoRep.contRep_smul X _ hψ)
  have e1 : (g * k * t⁻¹ : GA D (D.sp.Y 0)) = g * t⁻¹ * ((t⁻¹)⁻¹ * k * t⁻¹) := by group
  have hkey : ∀ z, ψ (z * x) = X.chi2 x.2 * ψ z := by
    intro z
    conv_lhs => rw [hxeq]
    exact congrFun key z
  have hm : iotaX X h ((g * k * t⁻¹ : GA D (D.sp.Y 0))) = iotaX X h ((g * t⁻¹ : GA D (D.sp.Y 0))) * x := by
    rw [e1, hxdef]
    exact map_mul (iotaX X h) _ _
  rw [hm, hkey, star_mul']
  exact congrArg (· * _) hval

end GlobalTheory.ConjRowLevelSee
