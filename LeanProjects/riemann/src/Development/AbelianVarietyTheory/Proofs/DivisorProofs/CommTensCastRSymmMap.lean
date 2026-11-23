import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.ConjFrame

theorem comm_tensCastR_symm_map {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (σ : E →ₐ[F1] E) (τ : E →ₐ[F2] E) (hστ : ∀ x, σ x = τ x) (x : E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2) :
    Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E
        ((GlobalTheory.StdFrame.tensCastR h).symm (Algebra.TensorProduct.map τ (AlgHom.id F2 (FiniteAdeleRing (𝓞 F2) F2)) x)) =
      Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F1) F1)
        (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E ((GlobalTheory.StdFrame.tensCastR h).symm x)) := by
  subst h
  have hc : ∀ y, (GlobalTheory.StdFrame.tensCastR (rfl : F1 = F1)).symm y =
      (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).symm y := fun _ => rfl
  simp only [hc]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, hστ]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem swapAE_conjAL : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) (x : ReciprocityTheory.Aut.AL D.host.E), Formalism.IndefR.Lev.swapAE D ((GlobalTheory.StdFrame.tensCastR hF).symm (ReciprocityTheory.Aut.conjAL D.host.E x)) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Formalism.IndefR.Lev.swapAE D ((GlobalTheory.StdFrame.tensCastR hF).symm x)) := by
  intro D hF x
  exact comm_tensCastR_symm_map hF D.sp.cm.sig ((IsCMField.complexConj D.host.E).toAlgHom) (fun _ => rfl) x

end GlobalTheory.ConjFrame

end
