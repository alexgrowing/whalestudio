import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

def entryR {m n : ℕ} (τ : D.what₂.Tau) (a : Fin m) (b : Fin n) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))

theorem entryR_apply {m n : ℕ} (τ : D.what₂.Tau) (a : Fin m) (b : Fin n) (Z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    entryR τ a b Z = Z τ a b := rfl

def dSq {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℝ :=
  ∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (entryR τ a b)

theorem dSq_apply {m n : ℕ} (Z V : D.what₂.Tau → Fin m → Fin n → ℂ) :
    dSq Z V = ∑ τ, ∑ a, ∑ b, 2 * (V τ a b * starRingEnd ℂ (Z τ a b)).re := by
  simp [dSq, ContinuousLinearMap.sum_apply, entryR_apply, Complex.inner, two_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hasFDerivAt_sqSum {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    HasFDerivAt (fun Z : D.what₂.Tau → Fin m → Fin n → ℂ => sqSum Z) (dSq Z) Z := by
  unfold sqSum dSq
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun τ (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ∑ a, ∑ b, ‖Z τ a b‖ ^ 2)
    fun τ _ => ?_
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun a (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ∑ b, ‖Z τ a b‖ ^ 2)
    fun a _ => ?_
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun b (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ‖Z τ a b‖ ^ 2)
    fun b _ => ?_
  exact (entryR τ a b).hasFDerivAt.norm_sq

def frL {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) :
    (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℂ] (D.what₂.Tau → Fin m → Fin n → ℂ) :=
  let l : (D.what₂.Tau → Fin m → Fin n → ℂ) →ₗ[ℂ] (D.what₂.Tau → Fin m → Fin n → ℂ) :=
    { toFun := frPt B B'
      map_add' := fun x y => by
        funext τ
        show B' τ * Matrix.of (x τ + y τ) * (B τ)⁻¹ = B' τ * Matrix.of (x τ) * (B τ)⁻¹ + B' τ * Matrix.of (y τ) * (B τ)⁻¹
        rw [show Matrix.of (x τ + y τ) = Matrix.of (x τ) + Matrix.of (y τ) from rfl, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        funext τ
        show B' τ * Matrix.of (c • x τ) * (B τ)⁻¹ = c • (B' τ * Matrix.of (x τ) * (B τ)⁻¹)
        rw [show Matrix.of (c • x τ) = c • Matrix.of (x τ) from rfl, Matrix.mul_smul, Matrix.smul_mul] }
  ⟨l, LinearMap.continuous_of_finiteDimensional l⟩

theorem frL_apply {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : frL B B' Z = frPt B B' Z := rfl

def toCLin {m n : ℕ} (L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ)
    (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℂ] ℂ :=
  let l : (D.what₂.Tau → Fin m → Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := fun c v => by
        have e : c • v = c.re • v + c.im • (Complex.I • v) := by
          funext τ a b
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im c]
          ring
        rw [e, L.map_add, L.map_smul, L.map_smul, hL, RingHom.id_apply, Complex.real_smul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring }
  ⟨l, LinearMap.continuous_of_finiteDimensional l⟩

theorem toCLin_restrict {m n : ℕ} (L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ)
    (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) : (toCLin L hL).restrictScalars ℝ = L := by
  ext v; rfl

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

theorem realPlace_cmTrace_zero_element_eq_I_mul_abs (τ : D.what₂.Tau) : tauE D τ D.host.xi0 = ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I := by
  have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have him := Formalism.L2.Theta.xi_zero_im_pos D τ
  have hn := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq D (tauE D τ)
  have e : tauE D τ D.host.xi0 = (((tauE D τ D.host.xi0).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos him] at hn
  rw [e, hn]

theorem hAt_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (τ : D.what₂.Tau)
    (Z V : Fin T.rank → Fin S.rank → ℂ) :
    hAt S T τ (GlobalTheory.FockPos.frAt frT τ * Matrix.of Z * (GlobalTheory.FockPos.frAt frS τ)⁻¹)
      (GlobalTheory.FockPos.frAt frT τ * Matrix.of V * (GlobalTheory.FockPos.frAt frS τ)⁻¹) =
      ∑ a, ∑ b, starRingEnd ℂ (V a b) * Z a b := by
  set B := GlobalTheory.FockPos.frAt frS τ
  set B' := GlobalTheory.FockPos.frAt frT τ
  have h1 : Bᴴ * gramAt D S τ * B = 1 := GlobalTheory.FockPos.frAt_on frS hS τ
  have h2 : B'ᴴ * gramAt D T τ * B' = 1 := GlobalTheory.FockPos.frAt_on frT hT τ
  have hBd : IsUnit B.det := isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne frS τ)
  have hGi : (gramAt D S τ)⁻¹ = B * Bᴴ := by
    apply Matrix.inv_eq_right_inv
    have e1 : Bᴴ * (gramAt D S τ * B) = 1 := by rw [← Matrix.mul_assoc]; exact h1
    rw [← Matrix.mul_assoc]
    exact mul_eq_one_comm.1 e1
  have hBB : Bᴴ * (B⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hBd, Matrix.conjTranspose_one]
  have e : (gramAt D S τ)⁻¹ * (B' * Matrix.of V * B⁻¹)ᴴ * gramAt D T τ * (B' * Matrix.of Z * B⁻¹) =
      B * ((Matrix.of V)ᴴ * Matrix.of Z * B⁻¹) := by
    rw [hGi]
    calc B * Bᴴ * (B' * Matrix.of V * B⁻¹)ᴴ * gramAt D T τ * (B' * Matrix.of Z * B⁻¹)
        = B * ((Bᴴ * (B⁻¹)ᴴ) * (Matrix.of V)ᴴ * (B'ᴴ * gramAt D T τ * B') * Matrix.of Z * B⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B * ((Matrix.of V)ᴴ * Matrix.of Z * B⁻¹) := by
          rw [hBB, h2, Matrix.one_mul, Matrix.mul_one]
  unfold hAt
  rw [e, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_right _ _ hBd]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  exact Finset.sum_comm

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

theorem omO_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (Z V : RW T S) :
    omO S T (frPt (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) Z)
      (frPt (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) V) =
      ∑ τ, ∑ a, ∑ b, 2 * (((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I * (starRingEnd ℂ (V τ a b) * Z τ a b)).re := by
  rw [omO_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  unfold GlobalTheory.VacUnique.omAt
  rw [frPt, frPt, hAt_frame frS frT hS hT τ (Z τ) (V τ), realPlace_cmTrace_zero_element_eq_I_mul_abs]
  simp only [Finset.mul_sum, Complex.re_sum]

theorem differentiable_gZ_of_frames {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E)
    (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (hfock : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) :
    Differentiable ℂ (gZ σ S T (fun τ => (frS.1).map (tauE D τ)) (fun τ => (frT.1).map (tauE D τ)) f) := by
  obtain rfl := GlobalTheory.FockPos.cart_one frS hS hcS
  obtain rfl := GlobalTheory.FockPos.cart_one frT hT hcT
  obtain ⟨hd, hann⟩ := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T _ _ f hf hfock
  have hJ : ∀ z : RW T S, jO S T (fun _ => (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ))
      (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) z = Complex.I • z := fun z => by
    funext τ i k
    simp [jO_apply, cplxO, Matrix.mul_apply, Matrix.one_apply, Pi.mul_apply, Pi.one_apply]
    first
      | exact congrFun (congrFun (Matrix.one_mul (M := (z τ : Matrix (Fin T.rank) (Fin S.rank) ℂ))) i) k
      | (erw [Matrix.mul_apply]; simp [Matrix.one_apply])
      | (rw [Matrix.one_mul])
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hF
  set Φ := frL (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) with hΦ
  intro Z
  have h1 : HasFDerivAt (fun Z => F (Φ Z)) ((fderiv ℝ F (Φ Z)).comp (Φ.restrictScalars ℝ)) Z :=
    (hd (Φ Z)).hasFDerivAt.comp Z (Φ.restrictScalars ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun Z : RW T S => Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ))
      (Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ) •
        Complex.ofRealCLM.comp ((Real.pi * Formalism.L2.Pj.xiR D) • dSq Z)) Z :=
    (Complex.ofRealCLM.hasFDerivAt.comp Z ((hasFDerivAt_sqSum Z).const_mul (Real.pi * Formalism.L2.Pj.xiR D))).cexp
  have h3 := h1.mul h2
  refine (hasFDerivAt_of_restrictScalars ℝ h3 (toCLin_restrict _ ?_)).differentiableAt
  intro v
  have hω1 : omO S T (Φ Z) (Φ v) = -(Formalism.L2.Pj.xiR D * dSq Z (Complex.I • v)) := by
    rw [hΦ, frL_apply, frL_apply, omO_frame frS frT hS hT, dSq_apply]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hω2 : omO S T (Φ Z) (Complex.I • Φ v) = Formalism.L2.Pj.xiR D * dSq Z v := by
    rw [← map_smul, hΦ, frL_apply, frL_apply, omO_frame frS frT hS hT, dSq_apply]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have ha := hann (Φ Z) (Φ v)
  rw [hJ, hω1, hω2, show f (iotaW σ T S (Φ Z)) = F (Φ Z) from rfl] at ha
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast at ha ⊢
  generalize Complex.exp ((Real.pi : ℂ) * (Formalism.L2.Pj.xiR D : ℂ) * (sqSum Z : ℂ)) = E
  generalize (fderiv ℝ F (Φ Z)) (Complex.I • Φ v) = b at ha ⊢
  generalize (fderiv ℝ F (Φ Z)) (Φ v) = a at ha ⊢
  linear_combination (-Complex.I * E) * ha + (F (Φ Z) * E * Real.pi * Formalism.L2.Pj.xiR D * ((dSq Z (Complex.I • v) : ℝ) : ℂ) +
    E * b - Complex.I * F (Φ Z) * E * Real.pi * Formalism.L2.Pj.xiR D * ((dSq Z v : ℝ) : ℂ)) * Complex.I_sq

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

theorem differentiable_gZ_top : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → Differentiable ℂ (GlobalTheory.VacRealForm.gZ σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f) := by
  intro D T L sc G W U N σ hσ t j hj f hf
  exact differentiable_gZ_of_frames hσ hf.1 _ _ (N.fr (.top j)) (N.fr (.top (j + 1)))
    (N.fr_on (.top j) (show j ≤ D.R.m by omega)) (N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)) _ _
    (W.cart_is (.top j) (show j ≤ D.R.m by omega)) (W.cart_is (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)) f
    hf.2.theta hf.2.fock

end GlobalTheory.VacRealForm
