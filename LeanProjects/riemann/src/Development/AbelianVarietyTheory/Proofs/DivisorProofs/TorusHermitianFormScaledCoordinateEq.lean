import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDualStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelDataX
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawOF
variable {D : D7}

theorem zCo_iota {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hch : GlobalTheory.FockCompare.Chart θ σ) {S T : HSp D}
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (z : GlobalTheory.FockCompare.RW T S) :
    GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) =
      fun τ => (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ := by
  funext τ
  have e : compAt θ τ (GlobalTheory.FockCompare.iotaW σ T S z) = Matrix.of (z τ) := congrFun (hch.pi_iota T S z) τ
  simp only [GlobalTheory.FockPos.zCo, e]
  rfl

theorem frAt_inv {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt fr τ)⁻¹ * GlobalTheory.FockPos.frAt fr τ = 1 ∧ GlobalTheory.FockPos.frAt fr τ * (GlobalTheory.FockPos.frAt fr τ)⁻¹ = 1 :=
  ⟨Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne fr τ)),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne fr τ))⟩

theorem coord_back {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹) *
      GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) := by
  have h1 := (frAt_inv frS τ).1
  have h2 := (frAt_inv frT τ).1
  calc _ = ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * GlobalTheory.FockPos.frAt frT τ) * Matrix.of (Z τ) *
        ((GlobalTheory.FockPos.frAt frS τ)⁻¹ * GlobalTheory.FockPos.frAt frS τ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.ThetaLawOF

namespace GlobalTheory.ThetaLawOF
variable {D : D7}

theorem trace_conjTranspose_mul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) :
    (Aᴴ * B).trace = ∑ a, ∑ b, starRingEnd ℂ (A a b) * B a b := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl

theorem omO_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (x y : GlobalTheory.FockCompare.RW T S) :
    GlobalTheory.VacUnique.omO S T x y = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (y τ) * GlobalTheory.FockPos.frAt frS τ) a b) *
        ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (x τ) * GlobalTheory.FockPos.frAt frS τ) a b)).re := by
  rw [GlobalTheory.VacUnique.omO_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  show 2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (Matrix.of (x τ)) (Matrix.of (y τ))).re = _
  rw [GlobalTheory.FockJetOrigin.hAt_coord (BS := fun τ => GlobalTheory.FockPos.frAt frS τ)
    (BT := fun τ => GlobalTheory.FockPos.frAt frT τ) (GlobalTheory.FockPos.frAt_on frS hS τ) (GlobalTheory.FockPos.frAt_on frT hT τ),
    trace_conjTranspose_mul, GlobalTheory.FockJetOrigin.realPlace_cmTrace_zero_element_eq_I_mul_abs, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]

theorem torusHermitianForm_scaled_coordinate_eq {N N' : ℕ} {δ : ℂ} (hδ : δ ≠ 0) (Z X : Formalism.MainNotions.TaylorLogMetric.VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Z) (δ • X) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b) := by
  have e : (∑ τ, ∑ i, ∑ j, (δ • Z) τ i j * starRingEnd ℂ ((δ • X) τ i j)) =
      (δ * starRingEnd ℂ δ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (X τ i j) := by
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hL : (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ).abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ := rfl
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [Formalism.MainNotions.TaylorLogMetric.Hf, e, hL, GlobalTheory.MomDict.area_lamOf D D.host.ccK δ D.host.ccK_ne_bot, hxi, Complex.mul_conj]
  have h0 : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hδ).ne'
  have h1 : ((Ideal.absNorm D.host.ccK : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0)
  have h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : Real.sqrt D.host.d ≠ 0)
  push_cast
  field_simp

theorem al_mul_self {N N' : ℕ} (T0 : Formalism.MainNotions.TaylorLogMetric.Tor D) (x : Formalism.MainNotions.TaylorLogMetric.VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.al D T0 x * Formalism.MainNotions.TaylorLogMetric.al D T0 x = 1 := by
  rw [Formalism.MainNotions.TaylorLogMetric.al, ← mul_zpow, show (-1 : ℂ) * -1 = 1 by norm_num, _root_.one_zpow]

theorem entry (zz xx : ℂ) (r : ℝ) :
    (Real.pi : ℂ) * Complex.I * ((2 * (Complex.I * (r : ℂ) * (starRingEnd ℂ zz * xx)).re : ℝ) : ℂ) -
      2 * (Real.pi : ℂ) * (r : ℂ) * (zz * starRingEnd ℂ xx) - (Real.pi : ℂ) * (r : ℂ) * (xx * starRingEnd ℂ xx) =
      (Real.pi : ℂ) * (r : ℂ) * ((‖zz‖ ^ 2 : ℝ) - (‖zz + xx‖ ^ 2 : ℝ) : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

end GlobalTheory.ThetaLawOF

end
