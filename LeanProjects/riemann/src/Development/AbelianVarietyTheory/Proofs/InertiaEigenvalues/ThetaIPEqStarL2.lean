import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalPreimageOfSupportedAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalKernelNormSqMulLatticeIndexEqOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.GoodModulus

theorem thetaInner_eq_star_l2 {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (x y : WO S T' → ℂ) :
    thetaIP μ 𝓕 x y = star (GlobalTheory.AdelicScalar.l2 μ 𝓕 x y) := by
  unfold thetaIP GlobalTheory.AdelicScalar.l2 Formalism.IndefR.Lift.pet
  show _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  congr 1; funext w
  simp [mul_comm]

theorem goodMod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, GoodMod R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ v f hf hoff k hk
  obtain ⟨a, rfl⟩ := GlobalTheory.T.exists_local_preimage_of_supportedAtPlace D (Wc D i) v f hf k hk
  have hW := hL.thP.ωP i t
  have hvac := GlobalTheory.T.pairFixedVector_latticeVacuum_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  have hunr := GlobalTheory.T.weilDatumCharacters_unramified_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  obtain ⟨φ, hφ, hc⟩ := GlobalTheory.VacCoef.vac_coef D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW μ 𝓕 hμ v hunr
  have hmod := GlobalTheory.T.sphericalKernel_normSq_mul_latticeIndex_eq_one D (Wc D i) (Vc D i).rank _ v φ hφ (fun w h => (hunr w h).1) a
  have h1 := hc a (R.vP i t) (R.vP i t) hvac hvac
  have hne := (vecNe D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ).1
  have hne' : GlobalTheory.AdelicScalar.l2 μ 𝓕 (R.vP i t) (R.vP i t) ≠ 0 := by
    intro h; apply hne; rw [thetaInner_eq_star_l2, h, star_zero]
  have e : coef R i t μ 𝓕 (GlobalTheory.FinZeta.embV (Wc D i) v a) = star (φ a) := by
    unfold coef
    rw [thetaInner_eq_star_l2, thetaInner_eq_star_l2, h1, star_mul', mul_div_assoc, div_self (star_ne_zero.2 hne'), mul_one]
  rw [e, norm_star]
  exact hmod

end GlobalTheory.RawLift.GoodModulus

end
