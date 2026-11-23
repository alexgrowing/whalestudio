import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestFunctionOfFockVacuumThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelTestFunctionMapLinearInjectiveEquivarStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatchStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensityStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeightStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.TorWt

variable {D : D7} {S T : HSp D}

theorem eq_zero_of_rho_finW_zero (C : Ctx S T) {F : WO S T → ℂ} (hF : C.IsTh F)
    (h0 : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.rho (finW S T y) F 0 = 0) : F = 0 := by
  obtain ⟨h0th, hlin, hfl⟩ := GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C
  have key := (hfl F hF).2.2.2.1
  have r0 : IsRealPt (0 : WO S T) := by
    ext i j
    simp
  have hv : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, F (-(ratW T S yᵀ - finW S T y)) = 0 := by
    intro y
    have e := key y 0 r0
    rw [h0 y, zero_sub] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (Complex.exp_ne_zero _)
  obtain ⟨R, hRc, -, hadd, -, hR2, -, hfin, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  have hrat := (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.2
  obtain ⟨B, hB⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).1
  have hdom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hd := (GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hdom).2.2.2.1
  have hRe : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, R (embR C.X y) = ratW T S yᵀ - finW S T y := by
    intro y
    obtain ⟨h1, h2, h3, -⟩ := hrat y
    have e : C.realPt (ratW T S yᵀ - finW S T y) = embR C.X y := by
      have := hadd (ratW T S yᵀ - finW S T y) (finW S T y)
      rw [sub_add_cancel, h1, hfin _ h2, add_zero] at this
      exact this.symm
    rw [← e, hR2 _ h3]
  have hG : (fun v => F (-(R v))) = fun _ => (0 : ℂ) := by
    refine hd.equalizer (hF.cont.comp (continuous_neg.comp hRc)) continuous_const (funext fun y => ?_)
    simp only [Function.comp_apply]
    rw [hRe y]
    exact hv y
  refine (hlin F 0 hF h0th).2 fun w hw => ?_
  have e := congrFun hG (-(C.realPt w))
  rw [map_neg, neg_neg, hR2 w hw] at e
  rw [e]
  rfl

end GlobalTheory.AdSpan.TorWt

namespace GlobalTheory.AdSpan.TorWt

variable {D : D7} {S T : HSp D}

theorem rho_add_smul (C : Ctx S T) (w : WO S T) (F G : WO S T → ℂ) (a : ℂ) :
    C.rho w (F + a • G) = C.rho w F + a • C.rho w G := by
  funext x
  simp only [Ctx.rho, heisO, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem fvec_Th_rmul (C : Ctx S T) {B B' : C.Bas} (hB : C.IsB B) (hB' : C.IsB B') {b : Frame C.X.Ψ T.rank}
    (hb : b ∈ Bor C.X.Ψ T.rank) (hx : C.xB B' = rmul (C.xB B) b)
    (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ)
    (hQ : C.toH Q ∈ Harm.rowHighest ℂ c c') (φ : TF S.rank C.g) (hφ : SW.IsSB φ) :
    C.fvec B' (C.Th (C.xB B') φ) Q = bchar (wtOf C.X C.hr c c' S.rank) b • C.fvec B (C.Th (C.xB B) φ) Q := by
  obtain ⟨h0th, hlin, hfl⟩ := GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C
  have hdom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hdom' := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B' hB').2.1
  have hth : ∀ x ∈ C.X.dom, ∀ ψ : TF S.rank C.g, SW.IsSB ψ → C.IsTh (C.Th x ψ) :=
    fun x hx ψ hψ => (GlobalTheory.T.adelicZakTheta_exists_unique D S T C x hx ψ hψ).1.1
  have hhe : ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (ψ : TF S.rank C.g), SW.IsSB ψ →
      SW.IsSB (heisG C.X C.bas y ψ) := fun y ψ h =>
    ((GlobalTheory.SW.heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 y ψ h).1
  have hw := (GlobalTheory.T.thetaSeries_testFunction_holomorphic_weight D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even c c')
  set la := bchar (wtOf C.X C.hr c c' S.rank) b
  have t1 : C.IsTh (C.fvec B' (C.Th (C.xB B') φ) Q) :=
    (GlobalTheory.T.fockPolynomialVector_laws D S T C B' hB' (fun _ => 1) _ (hth _ hdom' φ hφ) Q).1
  have t2 : C.IsTh (C.fvec B (C.Th (C.xB B) φ) Q) :=
    (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) _ (hth _ hdom φ hφ) Q).1
  have tG : C.IsTh (C.fvec B' (C.Th (C.xB B') φ) Q + (-la) • C.fvec B (C.Th (C.xB B) φ) Q) :=
    ((hlin _ _ t1 ((hfl _ t2).1 (-la))).1)

  have val : ∀ (B₀ : C.Bas), C.IsB B₀ → C.xB B₀ ∈ C.X.dom → ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E,
      C.rho (finW S T y) (C.fvec B₀ (C.Th (C.xB B₀) φ) Q) 0 =
        thP C.X C.hr C.bas C.idx (heisG C.X C.bas (-y) φ) (C.toH Q) (C.xB B₀) := by
    intro B₀ hB₀ hd₀ y
    have e1 := (GlobalTheory.T.fockPolynomialVector_laws D S T C B₀ hB₀ (fun _ => 1) _ (hth _ hd₀ φ hφ) Q).2.2.2.2.2 (finW S T y)
      ((GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.2 y).2.1
    rw [← e1, ((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hd₀ φ hφ).2.2.1 y)]
    exact ((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 B₀ hB₀ _ (hhe (-y) φ hφ)).2 Q
  have hG := eq_zero_of_rho_finW_zero C tG fun y => by
    rw [rho_add_smul, Pi.add_apply, Pi.smul_apply, val B' hB' hdom' y, val B hB hdom y, hx,
      (hw _ (hhe (-y) φ hφ) _ hQ).2.1 _ hdom b hb, smul_eq_mul]
    ring
  rw [neg_smul, ← sub_eq_add_neg, sub_eq_zero] at hG
  exact hG

end GlobalTheory.AdSpan.TorWt

namespace GlobalTheory.AdSpan.TorWt

variable {D : D7} {S T : HSp D}

theorem conj_exp_mul_exp (x : ℝ) : conj (cexp ((x : ℂ) * I)) * cexp ((x : ℂ) * I) = 1 := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  ring

theorem conj_exp (x : ℝ) : conj (cexp ((x : ℂ) * I)) = cexp (-((x : ℂ) * I)) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  ring

theorem det_sgnM_ne (C : Ctx S T) : (sgnM C.X).det ≠ 0 := by
  rw [sgnM, det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  unfold sgn
  split_ifs <;> norm_num

theorem mem_UH_tor (C : Ctx S T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) :
    B ρ * diagonal (fun a => cexp ((t a : ℂ) * I)) * (B ρ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := by
  set P := B ρ
  set d : Matrix (Fin T.rank) (Fin T.rank) ℂ := diagonal (fun a => cexp ((t a : ℂ) * I))
  set G := gramAt D T ρ
  have hP : Pᴴ * G * P = sgnM C.X := hB ρ
  have hdet : IsUnit P.det := by
    have h := congrArg Matrix.det hP
    rw [det_mul, det_mul] at h
    refine isUnit_iff_ne_zero.2 fun h0 => det_sgnM_ne C ?_
    rw [← h, h0, mul_zero]
  have hdd : dᴴ * sgnM C.X * d = sgnM C.X := by
    simp only [d, sgnM, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext a
    simp only [Pi.star_apply, RCLike.star_def]
    rw [mul_comm, ← mul_assoc, mul_comm _ (conj _), conj_exp_mul_exp, one_mul]
  show (P * d * P⁻¹)ᴴ * G * (P * d * P⁻¹) = G
  calc (P * d * P⁻¹)ᴴ * G * (P * d * P⁻¹) = (P⁻¹)ᴴ * (dᴴ * (Pᴴ * G * P) * d) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * G * P) * P⁻¹ := by rw [hP, hdd]
    _ = (P * P⁻¹)ᴴ * G * (P * P⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [mul_nonsing_inv _ hdet]; simp

theorem compAt_torAt (C : Ctx S T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ)
    (τ : D.what₂.Tau) : compAt C.θ τ (mt T (torAt C.θ T B ρ t)) =
      if τ = ρ then B ρ * diagonal (fun a => cexp ((t a : ℂ) * I)) * (B ρ)⁻¹ else 1 := by
  have h := GlobalTheory.PointAtPlaceHom.atTau_spec C.inf T ρ (mem_UH_tor C hB ρ t)
  split_ifs with e
  · subst e
    exact h.2.1
  · exact h.2.2 τ e

end GlobalTheory.AdSpan.TorWt

namespace GlobalTheory.AdSpan.TorWt

variable {D : D7} {S T : HSp D}

theorem mvB_torAt (C : Ctx S T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) :
    C.mvB (torAt C.θ T B ρ t) B = fun τ => if τ = ρ then B ρ * diagonal (fun a => cexp ((t a : ℂ) * I)) else B τ := by
  have hdet : IsUnit (B ρ).det := by
    have h := congrArg Matrix.det (hB ρ)
    rw [det_mul, det_mul] at h
    refine isUnit_iff_ne_zero.2 fun h0 => det_sgnM_ne C ?_
    rw [← h, h0, mul_zero]
  funext τ
  simp only [Ctx.mvB, compAt_torAt C hB ρ t τ]
  split_ifs with e
  · subst e
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.mul_one]
  · rw [Matrix.one_mul]

def bT (C : Ctx S T) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) : Frame C.X.Ψ T.rank := fun σ =>
  if σ = C.m.e ρ then (diagonal (fun a => cexp (-((t a : ℂ) * I))) : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  else (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)

theorem mat_bT (C : Ctx S T) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (σ : C.X.Ψ) :
    mat (bT C ρ t) σ = if σ = C.m.e ρ then diagonal (fun a => cexp (-((t a : ℂ) * I))) else 1 := by
  funext a c
  by_cases e : σ = C.m.e ρ <;> simp [mat, bT, e] <;> rfl

theorem bT_mem (C : Ctx S T) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) : bT C ρ t ∈ Bor C.X.Ψ T.rank := by
  intro σ
  by_cases e : σ = C.m.e ρ
  · have h : mat (bT C ρ t) σ = diagonal (fun a => cexp (-((t a : ℂ) * I))) := by
      rw [mat_bT, if_pos e]
    refine ⟨?_, fun a c hca => ?_⟩
    · rw [h, det_diagonal]
      exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.exp_ne_zero _
    · have := congrFun (congrFun h a) c
      simp only [mat, Matrix.of_apply] at this
      rw [this, diagonal_apply_ne _ (ne_of_gt hca)]
  · have h : mat (bT C ρ t) σ = 1 := by
      rw [mat_bT, if_neg e]
    refine ⟨by rw [h, det_one]; exact one_ne_zero, fun a c hca => ?_⟩
    have := congrFun (congrFun h a) c
    simp only [mat, Matrix.of_apply] at this
    rw [this, one_apply_ne (ne_of_gt hca)]

theorem xB_mvB_torAt (C : Ctx S T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) :
    C.xB (C.mvB (torAt C.θ T B ρ t) B) = rmul (C.xB B) (bT C ρ t) := by
  rw [mvB_torAt C hB ρ t]
  funext σ a c
  show conj ((if C.m.e.symm σ = ρ then B ρ * diagonal (fun a => cexp ((t a : ℂ) * I)) else B (C.m.e.symm σ)) a c) =
    (mat (C.xB B) σ * mat (bT C ρ t) σ) a c
  rw [mat_bT]
  by_cases e : σ = C.m.e ρ
  · subst e
    rw [if_pos (Equiv.symm_apply_apply _ _), if_pos rfl, mul_diagonal, mul_diagonal, map_mul, conj_exp]
    simp [mat, Ctx.xB]
  · have e' : C.m.e.symm σ ≠ ρ := fun h => e (by rw [← h, Equiv.apply_symm_apply])
    rw [if_neg e', if_neg e, Matrix.mul_one]
    rfl

end GlobalTheory.AdSpan.TorWt

namespace GlobalTheory.AdSpan.TorWt

variable {D : D7} {S T : HSp D}

theorem bchar_bT (C : Ctx S T) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (la : Wt C.X.Ψ T.rank) :
    bchar la (bT C ρ t) = ∏ a, cexp (-((t a : ℂ) * I)) ^ la (C.m.e ρ) a := by
  have hb : ∀ σ i, bT C ρ t σ i i = if σ = C.m.e ρ then cexp (-((t i : ℂ) * I)) else 1 := by
    intro σ i
    have := congrFun (congrFun (mat_bT C ρ t σ) i) i
    simp only [mat, Matrix.of_apply] at this
    rw [this]
    split_ifs <;> simp
  unfold bchar
  rw [Finset.prod_eq_single (C.m.e ρ) (fun σ _ hσ => Finset.prod_eq_one fun i _ => by
    rw [hb, if_neg hσ, _root_.one_zpow]) (fun h => absurd (Finset.mem_univ _) h)]
  exact Finset.prod_congr rfl fun i _ => by rw [hb, if_pos rfl]

theorem detPow_torAt (C : Ctx S T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ)
    (m : D.what₂.Tau → ℤ) : detPow C.θ T m (torAt C.θ T B ρ t) = (∏ a, cexp ((t a : ℂ) * I)) ^ m ρ := by
  have hdet : IsUnit (B ρ).det := by
    have h := congrArg Matrix.det (hB ρ)
    rw [det_mul, det_mul] at h
    refine isUnit_iff_ne_zero.2 fun h0 => det_sgnM_ne C ?_
    rw [← h, h0, mul_zero]
  unfold detPow
  rw [Finset.prod_eq_single ρ (fun τ _ hτ => by rw [compAt_torAt C hB ρ t τ, if_neg hτ, det_one, _root_.one_zpow])
    (fun h => absurd (Finset.mem_univ _) h), compAt_torAt C hB ρ t ρ, if_pos rfl, det_mul, det_mul,
    det_diagonal, mul_comm, ← mul_assoc, ← det_mul, nonsing_inv_mul _ hdet, det_one, one_mul]

theorem scalar_eq (t : Fin T.rank → ℝ) (k : ℤ) (w : Fin T.rank → ℤ) :
    cexp (((∑ a, ((k - w a : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) =
      (∏ a, cexp ((t a : ℂ) * I)) ^ k * ∏ a, cexp (-((t a : ℂ) * I)) ^ w a := by
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.AdSpan.TorWt

namespace GlobalTheory.AdSpan.TorWt

theorem torAt_fvec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q ∈ Harm.rowHighest ℂ c c' → ∀ (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (m : D.what₂.Tau → ℤ), RealScal C om B (torAt C.θ T B ρ t) (detPow C.θ T m (torAt C.θ T B ρ t)) → torAt C.θ T B ρ t ∈ GinfC T ∧ om (1, torAt C.θ T B ρ t) (C.fvec B f Q) = cexp (((∑ a, ((m ρ - ThFr.wtOf C.X C.hr c c' S.rank (C.m.e ρ) a : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) • C.fvec B f Q := by
  intro D S T C om hom B hB f hf hF c c' Q hQ ρ t m hz
  refine ⟨GlobalTheory.PointAtPlaceHom.atTau_mem T ρ _, ?_⟩
  obtain ⟨φ, hφ, rfl⟩ := GlobalTheory.T.exists_testFunction_of_fockVacuum_thetaFunction D S T C B hB f hf hF
  have hB' : C.IsB (C.mvB (torAt C.θ T B ρ t) B) := (((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.2.2.2.2 _).1
  have hdom' := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 _ hB').2.1
  have hth' : C.IsTh (C.Th (C.xB (C.mvB (torAt C.θ T B ρ t) B)) φ) := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hdom' φ hφ).1.1
  have e1 := ((GlobalTheory.T.weakWeilRep_carries_derivatives_vacua_fockVectors D S T C om hom 1 (torAt C.θ T B ρ t) _ hf).2 B hB).2 Q
  have h1 : (fun τ => compAt C.θ τ (mt S (1 : GA D S))) = fun _ => 1 :=
    funext fun τ => GlobalTheory.PointAtPlaceHom.infMat_one S (C.θ τ)
  rw [h1] at e1
  have e2 : om (1, torAt C.θ T B ρ t) (C.fvec B (C.Th (C.xB B) φ) Q) =
      C.fvec (C.mvB (torAt C.θ T B ρ t) B) (om (1, torAt C.θ T B ρ t) (C.Th (C.xB B) φ)) Q := e1
  rw [e2, hz φ hφ, (GlobalTheory.T.fockPolynomialVector_laws D S T C _ hB' (fun _ => 1) _ hth' Q).2.2.2.2.1,
    fvec_Th_rmul C hB hB' (bT_mem C ρ t) (xB_mvB_torAt C hB ρ t) c c' Q hQ φ hφ, smul_smul,
    detPow_torAt C hB ρ t m, bchar_bT, scalar_eq t (m ρ) (ThFr.wtOf C.X C.hr c c' S.rank (C.m.e ρ))]

end GlobalTheory.AdSpan.TorWt

end
