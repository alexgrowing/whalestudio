import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedTrans

theorem entry_tr (zz xx : ℂ) (r : ℝ) :
    -(Real.pi * Complex.I) * (-((2 * (Complex.I * (r : ℂ) * (starRingEnd ℂ (zz + xx) * -xx)).re : ℝ) : ℂ)) +
      -((Real.pi * r : ℝ) : ℂ) * ((‖zz + xx‖ ^ 2 : ℝ) : ℂ) =
    -((Real.pi * r : ℝ) : ℂ) * ((‖zz‖ ^ 2 : ℝ) : ℂ) +
      (-(Real.pi : ℂ) * (2 * (r : ℂ) * (zz * starRingEnd ℂ xx)) - (Real.pi : ℂ) * (2 * (r : ℂ) * (xx * starRingEnd ℂ xx)) / 2) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

theorem heisO_finRat_real : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank), X = (fun τ a b => -(((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T M τ) * GlobalTheory.FockPos.frAt frS τ) a b)) → ∀ w : WO S T, w.map (finPart D) = 0 → heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f w = GlobalTheory.FockPos.gaussO θ frS frT w * (Φ (GlobalTheory.FockPos.zCo θ frS frT w + X) * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, GlobalTheory.FockPos.zCo θ frS frT w τ a b * starRingEnd ℂ (X τ a b)) - (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2)) := by
  intro D ψ θ S T frS frT hS hT hψ hθ f hf Φ hΦ M X hX w hw
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨z, rfl⟩ : ∃ z, GlobalTheory.FockCompare.iotaW σ T S z = w := ⟨_, hch.iota_pi hw⟩
  have e : GlobalTheory.FockCompare.iotaW σ T S z + GlobalTheory.VacUnique.finRat S T M =
      ratW T S M + GlobalTheory.FockCompare.iotaW σ T S (z - GlobalTheory.VacUnique.infRat S T M) := by
    rw [GlobalTheory.VacUnique.ratW_eq hch, AddMonoidHom.map_sub]; abel
  show ψ (symplOH S T _ (GlobalTheory.VacUnique.finRat S T M)) * f (_ + GlobalTheory.VacUnique.finRat S T M) = _
  rw [GlobalTheory.FinTranslate.symplOH_real_fin (GlobalTheory.VacUnique.finRat_inf S T M) hw, AddChar.map_zero_eq_one, one_mul, e,
    hf.quasi, AddChar.map_neg_eq_inv, GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ hθ hψ S T _ _ (Or.inr (hch.real_iota T S _)),
    GlobalTheory.VacUnique.piW_ratW hθ, hch.pi_iota, ← Complex.exp_neg,
    hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO]
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) with hZ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z - GlobalTheory.VacUnique.infRat S T M)) = Z + X := by
    rw [hZ, GlobalTheory.ThetaLawOF.zCo_iota hch, GlobalTheory.ThetaLawOF.zCo_iota hch, hX]; funext τ a b
    show ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) - Matrix.of (GlobalTheory.VacUnique.infRat S T M τ)) * GlobalTheory.FockPos.frAt frS τ) a b = _
    rw [Matrix.mul_sub, Matrix.sub_mul]
    exact sub_eq_add_neg _ _
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T M) (z - GlobalTheory.VacUnique.infRat S T M) =
      ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (starRingEnd ℂ ((Z + X) τ a b) * -X τ a b)).re := by
    rw [GlobalTheory.ThetaLawOF.omO_frame frS frT hS hT, ← hz2, GlobalTheory.ThetaLawOF.zCo_iota hch]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hX]
    simp only [neg_neg]
  rw [hz2, hom]
  have kE : Complex.exp (-(-(Real.pi * Complex.I) * ((∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ ((Z + X) τ a b) * -X τ a b)).re : ℝ) : ℂ))) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry_tr (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    simp only [Pi.add_apply] at h ⊢
    push_cast at h ⊢
    linear_combination h
  rw [← mul_assoc, kE]
  ring

end GlobalTheory.MovedTrans

end
