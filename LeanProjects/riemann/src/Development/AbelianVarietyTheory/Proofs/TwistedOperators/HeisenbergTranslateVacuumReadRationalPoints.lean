import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaValueIdentityUnitFramesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelComplexPointMatchesCosetsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HeisRatRead

open GlobalTheory.FinTranslate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7}

theorem ratW_sub_realPt_inf (S T : HSp D) (ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ).map (infPart D) = 0 := by
  ext i j
  change infPart D (incA D (ℓ i j) - pairA D.host.F 1 0 ⊗ₜ[D.host.F] ℓ i j) = 0
  rw [map_sub]
  change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ ℓ i j) -
    Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 1 0 ⊗ₜ ℓ i j) = 0
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one]
  exact sub_eq_zero.2 rfl

theorem realPt_sub (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T (X - Y) = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T Y := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt, Matrix.of_apply, Matrix.sub_apply, TensorProduct.tmul_sub]

theorem actO_inf (S T : HSp D) (h : GA D T) {w : WO S T} (hw : w.map (infPart D) = 0) :
    (actO S T 1 h w).map (infPart D) = 0 := by
  have hw' : ∀ k l, infPart D (w k l) = 0 := fun k l => congrFun (congrFun hw k) l
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold actO
  simp only [Matrix.mul_apply, map_sum, map_mul, hw', mul_zero, zero_mul, Finset.sum_const_zero]

theorem actO_add (S T : HSp D) (h : GA D T) (u v : WO S T) :
    actO S T 1 h (u + v) = actO S T 1 h u + actO S T 1 h v := by
  simp only [actO, Matrix.mul_add, Matrix.add_mul]

end GlobalTheory.HeisRatRead

namespace GlobalTheory.HeisRatRead

open GlobalTheory.FinTranslate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem heis_translate_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∀ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
    w.map (infPart D) = 0 → heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i →
    x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w →
    ∀ X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      R.ωP i A.μ0 (1, g) (heisO R.ψ (Vc D i) (Wc D i) x (R.vacP i)) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
        R.ψ (-(symplOH (Vc D i) (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) +
            symplOH (Vc D i) (Wc D i) (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (actO (Vc D i) (Wc D i) 1 g w))) *
          R.ωP i A.μ0 (1, g) (R.vacP i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) := by
  intro D G _ _ Pl0 T0 A T _ R hL hF hT i g x hx ℓ w hw hρw hxe X
  have hW := hT.ωP i A.μ0
  have hv := hT.vP i A.μ0
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hv.1.2.theta
  set F := R.ωP i A.μ0 (1, g) (R.vacP i) with hFdef
  have hFθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) F := hW.om_pres _ _ hf
  set lf := ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ with hlf
  have hlf0 : lf.map (infPart D) = 0 := ratW_sub_realPt_inf (Vc D i) (Wc D i) ℓ
  set gw := actO (Vc D i) (Wc D i) 1 g w with hgw
  have hgw0 : gw.map (infPart D) = 0 := actO_inf (Vc D i) (Wc D i) g hw
  have hgx : actO (Vc D i) (Wc D i) 1 g x = lf + gw := by
    rw [hxe, actO_add, ← GlobalTheory.HeckeVacuum.act_mul, mul_inv_cancel, GlobalTheory.HeckeVacuum.act_one]
  have hFw : heisO R.ψ (Vc D i) (Wc D i) gw F = F := by
    have := hW.om_heis 1 g w (R.vacP i) hf
    rw [hρw] at this
    exact this.symm
  set P := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X
  set z := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)
  have hP0 : P.map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) X
  have hz0 : z.map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) (X - ℓ)
  have hl0 : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ).map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) ℓ
  have hzF : F (z + gw) = F z := by
    have := congrFun hFw z
    simp only [heisO, symplOH_real_fin hgw0 hz0, AddChar.map_zero_eq_one, one_mul] at this
    exact this
  have hpt : P + (lf + gw) = ratW (Wc D i) (Vc D i) ℓ + (z + gw) := by
    simp only [z, P, hlf, realPt_sub]
    abel
  have hratW : ratW (Wc D i) (Vc D i) ℓ = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ + lf := by
    rw [hlf]; abel
  rw [hW.om_heis 1 g x (R.vacP i) hf, ← hFdef]
  show R.ψ (symplOH (Vc D i) (Wc D i) P (actO (Vc D i) (Wc D i) 1 g x)) * F (P + actO (Vc D i) (Wc D i) 1 g x) = _
  rw [hgx, hpt, hFθ.quasi, hzF, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  rw [hratW, symplOH_add_right, symplOH_add_left, symplOH_add_right, symplOH_add_right,
    symplOH_real_fin hlf0 hP0, symplOH_real_fin hgw0 hP0, symplOH_real_fin hgw0 hl0, symplOH_fin_real hlf0 hz0]
  ring

end GlobalTheory.HeisRatRead
