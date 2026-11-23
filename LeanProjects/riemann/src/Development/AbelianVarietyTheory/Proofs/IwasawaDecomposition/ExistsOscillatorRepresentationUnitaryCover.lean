import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockExistsUniqueGaussianVectorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerGaussianVectorsFockSpaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetOneSubConjTransposeMulContractionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianInnerEqInvariantKernelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRepOfActionOnTotalFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseSpanCoherentVectorsFockStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOfWeakDerivOnInvariantTotalSetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOscillatorGaussianKernelRightStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianVectorAnnihilatorEquationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInnerPolynomialMovingGaussianStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerLieActionAdjointGaussianPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtGaussianParametersAtIdentityStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

def gauss (F : Fock (Ix P Q)) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) (x : Ix P Q → ℂ) : F.H :=
  (GlobalTheory.T.fock_existsUnique_gaussian_vector P Q F A x h).exists.choose

theorem hasCoeff_gauss (F : Fock (Ix P Q)) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) : HasCoeff F (gauss F h x) (expPS (gaussPoly A x)) :=
  (GlobalTheory.T.fock_existsUnique_gaussian_vector P Q F A x h).exists.choose_spec

theorem gauss_congr (F : Fock (Ix P Q)) {A B : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (h' : (1 - Bᴴ * B).PosDef) {x y : Ix P Q → ℂ} (e : A = B) (e' : x = y) : gauss F h x = gauss F h' y := by
  subst e e'; rfl

abbrev Par (P Q : ℕ) : Type :=
  ℂ × {Y : Matrix (Ix P Q) (Fin Q) ℂ // IsNeg Y} × (Ix P Q → ℂ) × (Ix P Q → ℂ)

def vec (F : Fock (Ix P Q)) (p : Par P Q) : F.H :=
  (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) • gauss F p.2.1.2.posDef (linX p.2.1.1 p.2.2.1 p.2.2.2)

def act (T0 : GrpData P Q) (g : T0.G) (p : Par P Q) : Par P Q :=
  ((T0.sq g : ℂˣ) * p.1, ⟨(T0.cov g : Mat P Q) * p.2.1.1, p.2.1.2.mul (T0.cov_mem g)⟩,
    (T0.cov g : Mat P Q) *ᵥ p.2.2.1, p.2.2.2 ᵥ* (T0.cov g⁻¹ : Mat P Q))

def base (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) (x : Ix P Q → ℂ) : Par P Q :=
  (c, ⟨baseY A, isNeg_baseY h⟩, baseV x, baseF x)

theorem vec_base (F : Fock (Ix P Q)) (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) : vec F (base c h x) = c • gauss F h x := by
  simp only [vec, base, scal_base, mul_one]
  rw [gauss_congr F _ h (matA_baseY A) (linX_base A x)]

theorem inner_vec (F : Fock (Ix P Q)) (p q : Par P Q) :
    inner ℂ (vec F p) (vec F q) = star p.1 * q.1 * ker p.2.1.1 p.2.2.1 p.2.2.2 q.2.1.1 q.2.2.1 q.2.2.2 := by
  obtain ⟨c, ⟨Y, hY⟩, v, φ⟩ := p
  obtain ⟨c', ⟨Y', hY'⟩, v', φ'⟩ := q
  have h1 := GlobalTheory.T.inner_gaussianVectors_fockSpace P Q F _ _ _ _ hY.posDef hY'.posDef _ _
    (hasCoeff_gauss F hY.posDef (linX Y v φ)) (hasCoeff_gauss F hY'.posDef (linX Y' v' φ'))
  have h2 := GlobalTheory.T.gaussian_inner_eq_invariantKernel P Q Y Y' v φ v' φ' hY.isUnit hY'.isUnit (GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions P Q _ _ hY.posDef hY'.posDef)
  simp only at h1 h2
  simp only [vec, inner_smul_left, inner_smul_right, h1, ← h2, map_mul, starRingEnd_apply]
  ring

theorem isUnit_form {Y Y' : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) (h' : IsNeg Y') :
    IsUnit (Yᴴ * Jm P Q * Y').det := by
  have h1 : IsUnit (-(Yᴴ * Jm P Q * Y')).det := by
    rw [form_factor Y Y' h.isUnit h'.isUnit, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    exact (h.isUnit.star.mul (GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions P Q _ _ h.posDef h'.posDef)).mul h'.isUnit
  rw [Matrix.det_neg] at h1
  exact isUnit_of_mul_isUnit_right h1

theorem dense_vec (F : Fock (Ix P Q)) : Dense (Submodule.span ℂ (Set.range (vec F)) : Set F.H) := by
  have h0 : (1 - (0 : Matrix (Fin P) (Fin Q) ℂ)ᴴ * (0 : Matrix (Fin P) (Fin Q) ℂ)).PosDef := by
    simpa using Matrix.PosDef.one
  refine (GlobalTheory.T.dense_span_coherent_vectors_fock P Q F (gauss F h0) (hasCoeff_gauss F h0)).mono (Submodule.span_mono ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨base 1 h0 x, by rw [vec_base, one_smul]⟩

theorem exists_rep (T0 : GrpData P Q) (F : Fock (Ix P Q)) :
    ∃ π : T0.G →* (F.H →L[ℂ] F.H), (∀ g x, ‖π g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => π g x) ∧
      ∀ g p, π g (vec F p) = vec F (act T0 g p) := by
  have hc : Continuous fun g : T0.G => (T0.cov g : Mat P Q) :=
    Units.continuous_val.comp (continuous_fst.comp T0.emb.continuous)
  refine GlobalTheory.T.exists_unitaryRep_of_action_on_total_family T0.G (Par P Q) F.H (act T0) (vec F) (fun p => ?_) (fun g h p => ?_) (dense_vec F)
    (fun g p q => ?_) (fun p q => ?_)
  · simp [act]
  · simp [act, mul_assoc, Matrix.mul_assoc]
  · rw [inner_vec, inner_vec]
    simp only [act]
    rw [ker_mul (T0.cov_mem g) (by rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])]
    have h : star ((T0.sq g : ℂˣ) : ℂ) * (T0.sq g : ℂˣ) = 1 := by
      rw [Complex.star_def, Complex.conj_mul', RealPar.Cover.norm_sq]; simp
    rw [star_mul']
    linear_combination (star p.1 * q.1 * ker p.2.1.1 p.2.2.1 p.2.2.2 q.2.1.1 q.2.2.1 q.2.2.2) * h
  · simp only [inner_vec]
    refine (continuous_const.mul (RealPar.Cover.continuous_sq.mul continuous_const)).mul
      (GlobalTheory.T.continuous_oscillatorGaussianKernel_right P Q T0.G _ _ _ _ _ _ ?_ ?_ ?_ fun g => isUnit_form q.2.1.2 (act T0 g p).2.1.2)
    · exact hc.matrix_mul continuous_const
    · exact hc.matrix_mulVec continuous_const
    · exact continuous_const.matrix_vecMul (hc.comp continuous_inv)

theorem hasDerivAt_exp_entry (X : Mat P Q) (a b : Ix P Q) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

theorem expt_inv (T0 : GrpData P Q) {Z : Mat P Q} (hZ : Z ∈ upq P Q) (t : ℝ) :
    (T0.expt (t • Z))⁻¹ = T0.expt (t • -Z) := by
  rw [inv_eq_iff_mul_eq_one, smul_neg, ← neg_smul, ← T0.expt_add Z hZ, add_neg_cancel, zero_smul, T0.expt_zero]

theorem neg_mem_upq {Z : Mat P Q} (hZ : Z ∈ upq P Q) : -Z ∈ upq P Q := by
  simpa using RealPar.KStabLie.smul_mem_upq hZ (-1)

theorem adjZ_neg {Z : Mat P Q} (hZ : Z ∈ upq P Q) : adjZ (-Z) = Z := by
  have h : Zᴴ * Jm P Q = -(Jm P Q * Z) := eq_neg_of_add_eq_zero_left hZ
  rw [adjZ, Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_neg, neg_neg,
    ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]

theorem hasDerivAt_inner_act (T0 : GrpData P Q) (F : Fock (Ix P Q)) {Z : Mat P Q} (hZ : Z ∈ upq P Q)
    (f : MvPolynomial (Ix P Q) ℂ) (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) :
    HasDerivAt (fun t : ℝ => inner ℂ (F.ι f) (vec F (act T0 (T0.expt (t • Z)) (base c h x))))
      (inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) (vec F (base c h x))) 0 := by
  set g : ℝ → Mat P Q := fun t => (T0.cov (T0.expt (t • Z)) : Mat P Q) with hg
  set g' : ℝ → Mat P Q := fun t => (T0.cov (T0.expt (t • Z))⁻¹ : Mat P Q) with hg'
  have g0 : g 0 = 1 := by simp [hg, T0.expt_zero]
  have g0' : g' 0 = 1 := by simp [hg', T0.expt_zero]
  obtain ⟨hA, hx, hs⟩ := GlobalTheory.T.hasDerivAt_gaussian_parameters_at_identity P Q A x Z g g' g0 g0'
    (fun a b => by
      simpa only [hg, T0.expt_cov _ (RealPar.KStabLie.smul_mem_upq hZ _)] using hasDerivAt_exp_entry Z a b)
    (fun a b => by
      simpa only [hg', expt_inv T0 hZ, T0.expt_cov _ (RealPar.KStabLie.smul_mem_upq (neg_mem_upq hZ) _), Matrix.neg_apply] using
        hasDerivAt_exp_entry (-Z) a b)
  have hn : ∀ t, IsNeg (g t * baseY A) := fun t => (isNeg_baseY h).mul (T0.cov_mem _)
  have hp := GlobalTheory.T.hasDerivAt_inner_polynomial_moving_gaussian P Q F _ _ (fun t => gauss F (hn t).posDef
    (linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t))) _ _ (fun t => hasCoeff_gauss F _ _) hA hx f
  have e0 : gauss F (hn 0).posDef (linX (g 0 * baseY A) (g 0 *ᵥ baseV x) (baseF x ᵥ* g' 0)) = gauss F h x :=
    gauss_congr F _ _ (by rw [g0, Matrix.one_mul, matA_baseY])
      (by rw [g0, g0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, linX_base])
  obtain ⟨a1, a2⟩ := GlobalTheory.T.gaussianVector_annihilator_equations P Q F A x _ (hasCoeff_gauss F h x)
  have h5 := ((((RealPar.Cover.hasDerivAt_sq (T := T0) hZ).mul_const c).fun_mul hs).fun_mul hp)
  simp only [vec_base, inner_smul_right, GlobalTheory.T.inner_lieAction_adjoint_gaussian_polynomial P Q F A x _ a1 a2 Z f]
  simp only [vec, inner_smul_right]
  refine h5.congr_deriv ?_
  simp only [e0]
  simp only [g0, g0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, scal_base, zero_smul, T0.expt_zero,
    map_one, Units.val_one]
  ring

theorem exists_isOsc (P Q : ℕ) (T0 : GrpData P Q) (F : Fock (Ix P Q)) :
    ∃ Om : T0.G →* (F.H →L[ℂ] F.H), IsOsc T0 F Om := by
  obtain ⟨π, h1, h2, h3⟩ := exists_rep T0 F
  refine ⟨π, h1, h2, fun Z hZ f => ?_⟩
  refine GlobalTheory.T.hasDerivAt_of_weak_deriv_on_invariant_total_set F.H (fun t => π (T0.expt (t • Z))) (Set.range (vec F)) _ _ ?_ (fun s t => ?_) (fun t => h1 _)
    (fun y => (h2 y).comp (T0.expt_cont.comp_continuous (by fun_prop)
      fun t => RealPar.KStabLie.smul_mem_upq hZ t)) (dense_vec F) ?_ ?_
  · simp [T0.expt_zero]
  · simp only [T0.expt_add Z hZ, map_mul]
  · rintro t _ ⟨p, rfl⟩
    exact ⟨_, (h3 _ p).symm⟩
  · rintro _ ⟨p, rfl⟩
    have e : vec F p = vec F (base (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) p.2.1.2.posDef
      (linX p.2.1.1 p.2.2.1 p.2.2.2)) := by rw [vec_base, vec]
    have h4 := hasDerivAt_inner_act T0 F (neg_mem_upq hZ) f (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) p.2.1.2.posDef
      (linX p.2.1.1 p.2.2.1 p.2.2.2)
    simp only [← h3, ← e, adjZ_neg hZ] at h4
    refine h4.congr_of_eventuallyEq (.of_forall fun t => ?_)
    have iso := (⟨(π (T0.expt (t • Z)) : F.H →ₗ[ℂ] F.H), h1 _⟩ : F.H →ₗᵢ[ℂ] F.H).inner_map_map (F.ι f)
      (π (T0.expt (t • -Z)) (vec F p))
    simp only [← iso]
    change _ = inner ℂ (π _ _) (π _ (π _ _))
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← expt_inv T0 hZ, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]

end GlobalTheory.OscGauss

end
