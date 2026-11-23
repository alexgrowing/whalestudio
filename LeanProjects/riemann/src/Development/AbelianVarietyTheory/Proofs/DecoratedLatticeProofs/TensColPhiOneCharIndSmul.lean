import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SourceLiftAtGluedPlaceProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBaseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientPara
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

section Translate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_phiOne_charInd_smul (χ : AddChar 𝓀[k] ℂ) (P₁ : Pair k n') (Q : Pair k n) (g : GL n k)
    (x : Matrix n (n' ⊕ Fin 1) k) :
    tensCol (phiOne P₁ Q) (charInd χ Q) ((g⁻¹ : GL n k).val * x) =
      tensCol (phiOne P₁ (g • Q)) (charInd χ (g • Q)) x := by
  have hcol : (fun i => ((g⁻¹ : GL n k).val * x) i (Sum.inr 0)) = (g⁻¹ : GL n k) • (fun i => x i (Sum.inr 0)) := rfl
  have hsub : ((g⁻¹ : GL n k).val * x).submatrix id Sum.inl = (g⁻¹ : GL n k).val * x.submatrix id Sum.inl := rfl
  have hphi : ∀ z : Matrix n n' k, phiOne P₁ (g • Q) z = phiOne P₁ Q ((g⁻¹ : GL n k).val * z) := by
    intro z
    have h := phiOne_smul (P := P₁) (Q := Q) (x := z) (1 : GL n' k) g
    rw [one_smul] at h
    rw [h, Units.val_one, Matrix.mul_one]
  have hchi : ∀ y : n → k, charInd χ (g • Q) y = charInd χ Q ((g⁻¹ : GL n k) • y) := by
    intro y
    unfold charInd vecInd
    rw [Pair.smul_lat, mem_smul_iff]
    split_ifs with hy
    · have hv := Pair.hasVal_ev (P := g • Q) (x := y) (by rw [Pair.smul_lat, mem_smul_iff]; exact hy)
      rw [Pair.smul_hasVal] at hv
      rw [hv.ev_eq]
    · simp
  unfold tensCol
  rw [hsub, hcol, hphi, hchi]

end Translate

end GlobalTheory.FinPl

namespace GlobalTheory.FinPl

end GlobalTheory.FinPl
