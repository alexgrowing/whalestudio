import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralNormSqMatrixCoefficientNeZeroDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientPureTensorEqSmulInnerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixCoeffRightTranslateDefiniteFormScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.Core.Rk.RealOcc

theorem pt_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.FullP →
    ∀ (i : Fin D.R.m) (t : T), ∃ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W),
      R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w) ≠ 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hF i t
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
  have hL : GlobalTheory.RawLift.Laws R F := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.thP⟩
  obtain ⟨-, v, w, -, hne⟩ := GlobalTheory.RawLift.vecNe D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ
  refine ⟨v, w, fun h => hne ?_⟩
  unfold GlobalTheory.RawLift.jointVec GlobalTheory.RawLift.thetaIP
  rw [h]
  simp

set_option maxHeartbeats 1000000 in

theorem real_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t (y : (R.HV i t).H), y ≠ 0 → ∀ m : Measure (GA D (Vc D i)), m.IsHaarMeasure → ∃ (l : (R.cV i).W →ₗ[ℂ] ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank), ∀ ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∀ mR : Measure (GinfC (Vc D i)), mR.IsHaarMeasure → ∫ b : GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t P) (R.ptP i t P) b * GlobalTheory.Core.Rk.IP.rcoef m (fun g => l (R.extV i t y g)) (fun g => l (R.extV i t y g)) b ∂mR ≠ 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t y hy m hm
  obtain ⟨v, w, hJ⟩ := pt_ne D G Pl0 T A Ks R F hG.core hF i t
  have hw : w ≠ 0 := by
    rintro rfl
    refine hJ ?_
    rw [map_zero]
    unfold RealDat.ptP
    exact map_zero _
  have H2 := GlobalTheory.T.matrixCoeff_rightTranslate_definiteForm_scalar D G Pl0 T A Ks R F hG.core i t y m hm
  obtain ⟨z2, h2, h2ne⟩ := H2
  refine ⟨innerₛₗ ℂ w, R.ioP i (PiTensorProduct.tprod ℂ v) w, fun ν 𝓕 hν mR hmR => ?_⟩
  have H1 := GlobalTheory.T.weilCoefficient_pureTensor_eq_smul_inner D G Pl0 T A Ks R F hG.core hF i t v ν 𝓕 hν
  obtain ⟨z1, h1, h1ne⟩ := H1
  have e1 : ∀ b : GinfC (Vc D i),
      GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w))
                   (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b = z1 * ⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ :=
    fun b => h1 w b b.2
  have e : ∀ b : GinfC (Vc D i),
      GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w))
                   (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b *
        GlobalTheory.Core.Rk.IP.rcoef m (fun g => innerₛₗ ℂ w (R.extV i t y g)) (fun g => innerₛₗ ℂ w (R.extV i t y g)) b =
      (z1 * z2) * ((‖⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun b => by
    calc _ = (z1 * ⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ) * (z2 * ⟪(R.cV i).ρ (b : GA D (Vc D i)) w, w⟫_ℂ) :=
          congrArg₂ (· * ·) (e1 b) (h2 w b b.2)
      _ = _ := by
        rw [← inner_conj_symm ((R.cV i).ρ (b : GA D (Vc D i)) w) w, Complex.ofReal_pow, ← Complex.mul_conj']
        ring
  rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, integral_complex_ofReal]
  exact mul_ne_zero (mul_ne_zero (h1ne w hJ) (h2ne hy)) (Complex.ofReal_ne_zero.2
    (GlobalTheory.T.integral_normSq_matrix_coefficient_ne_zero_definite D (Vc D i) (D.sp.V_sig _) (hG.core.models.vpos i) (R.cV i) (hG.core.models.cV i) w hw mR hmR))

end GlobalTheory.Core.Rk.RealOcc

end
