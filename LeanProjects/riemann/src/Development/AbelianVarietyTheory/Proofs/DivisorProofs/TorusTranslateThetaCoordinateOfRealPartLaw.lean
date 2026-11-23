import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableFockVacuumGaussianDefinitePair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelDataX
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem U_thY_of_law : ∀ {D : D7} (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1 → ∀ (δ : ℂ), δ ≠ 0 → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (f : WO S T → ℂ) (c : ℂ), (∀ z : GlobalTheory.FockCompare.RW T S, f (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1))) = c * Complex.exp (-(↑Real.pi * Complex.I) * ↑(-(GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) z))) * f (GlobalTheory.FockCompare.iotaW σ T S z)) → ∀ Y, Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M) (GlobalTheory.VacRealForm.thY σ S T (fun τ => B.1.map (tauE D τ)) (fun τ => B'.1.map (tauE D τ)) f δ) Y = c * GlobalTheory.VacRealForm.thY σ S T (fun τ => B.1.map (tauE D τ)) (fun τ => B'.1.map (tauE D τ)) f δ Y := by
  intro D σ S T B B' hB hB' δ hδ M f c hf Y
  set Bc : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ := fun τ => B.1.map (tauE D τ) with hBc
  set B'c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ := fun τ => B'.1.map (tauE D τ) with hB'c
  set X : RW T S := Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M with hXdef
  set Z : RW T S := δ⁻¹ • Y with hZ
  have hY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  have hinv : ∀ τ, ((B⁻¹ : GL (Fin S.rank) D.host.E).1).map (tauE D τ) = (B.1.map (tauE D τ))⁻¹ := fun τ =>
    (Matrix.inv_eq_left_inv (by
      rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)])).symm
  have hX : infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = frPt Bc B'c X := by
    funext τ
    show (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1).map (tauE D τ) = B'c τ * Matrix.of (X τ) * (Bc τ)⁻¹
    rw [Matrix.map_mul, Matrix.map_mul, hinv]
    rfl
  have hadd : δ⁻¹ • (Y + δ • X) = Z + X := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have hfr : frPt Bc B'c (Z + X) = frPt Bc B'c Z + frPt Bc B'c X := (frL Bc B'c).map_add Z X
  have hlaw := hf (frPt Bc B'c Z)
  rw [hX] at hlaw
  have hom : omO S T (frPt Bc B'c X) (frPt Bc B'c Z) =
      ∑ τ, ∑ a, ∑ b, 2 * (((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I * (starRingEnd ℂ (Z τ a b) * X τ a b)).re :=
    omO_frame B B' hB hB' X Z
  have harea : Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) =
      Complex.normSq δ * (Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d / 2 :=
    GlobalTheory.MomDict.area_lamOf D _ δ D.host.ccK_ne_bot
  have hxi := (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D).1
  have hN : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by
    have h : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast h
  have hd : Real.sqrt D.host.d ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)).ne'
  have hδn : Complex.normSq δ ≠ 0 := (Complex.normSq_pos.2 hδ).ne'
  have hHf : ∀ u v : RW T S, Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • u) (δ • v) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, u τ a b * starRingEnd ℂ (v τ a b) := by
    intro u v
    show (∑ τ, ∑ a, ∑ b, (δ • u) τ a b * starRingEnd ℂ ((δ • v) τ a b)) /
      (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) : ℂ) = _
    have e : ∀ τ a b, (δ • u) τ a b * starRingEnd ℂ ((δ • v) τ a b) =
        (Complex.normSq δ : ℂ) * (u τ a b * starRingEnd ℂ (v τ a b)) := fun τ a b => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← Complex.mul_conj]; ring
    simp only [e, ← Finset.mul_sum]
    rw [harea, hxi]
    have h1 : ((Complex.normSq δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hδn
    have h2 : ((Ideal.absNorm D.host.ccK : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN
    have h3 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
    generalize (∑ τ, ∑ a, ∑ b, u τ a b * starRingEnd ℂ (v τ a b)) = s
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    field_simp
  have key : -(↑Real.pi * Complex.I) * ↑(-(omO S T (frPt Bc B'c X) (frPt Bc B'c Z))) +
      ((Real.pi * Formalism.L2.Pj.xiR D * sqSum (Z + X) : ℝ) : ℂ) +
      (-(Real.pi : ℂ) * Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Z) (δ • X) -
        (Real.pi : ℂ) * Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) (δ • X) / 2) =
      ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ) := by
    have hOm : omO S T (frPt Bc B'c X) (frPt Bc B'c Z) =
        2 * Formalism.L2.Pj.xiR D * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)).im := by
      rw [hom]
      simp only [Complex.im_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hSq : sqSum (Z + X) = sqSum Z + 2 * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)).re + sqSum X := by
      unfold sqSum
      simp only [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Pi.add_apply, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hQ : (∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) = ((sqSum X : ℝ) : ℂ) := by
      unfold sqSum
      push_cast
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hHf, hHf, hOm, hSq, hQ]
    generalize (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) = p
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;> ring
  show gZ σ S T Bc B'c f (δ⁻¹ • (Y + δ • X)) * _ = c * gZ σ S T Bc B'c f (δ⁻¹ • Y)
  rw [hadd, ← hZ]
  unfold gZ
  rw [hfr, hlaw, hY, ← key, Complex.exp_add, Complex.exp_add]
  ring

end GlobalTheory.VacRealForm
