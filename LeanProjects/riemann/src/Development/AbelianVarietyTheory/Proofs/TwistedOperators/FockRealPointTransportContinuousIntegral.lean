import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransport

variable {D : D7}

def sg (b : Bool) : ℝ := if b then 1 else -1

theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

def cf (b b' : Bool) (c : ℂ) : ℂ := (c.re : ℂ) + ((sg b * sg b' * c.im : ℝ) : ℂ) * Complex.I

theorem cf_cf (b b' : Bool) (c : ℂ) : cf b b' (cf b b' c) = c := by
  have h : sg b * sg b' * (sg b * sg b') = 1 := by
    rw [mul_mul_mul_comm, sg_mul_self, sg_mul_self, one_mul]
  apply Complex.ext <;> simp [cf, h, ← mul_assoc]

theorem continuous_cf (b b' : Bool) : Continuous (cf b b') := by
  unfold cf; fun_prop

theorem jm_mul_single_mul_jm {m n : ℕ} (εB : Fin m → Bool) (εA : Fin n → Bool) (i : Fin m) (j : Fin n) :
    Formalism.REAL.Jm εB * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm εA =
      Matrix.single i j (((sg (εB i) * sg (εA j) : ℝ)) : ℂ) := by
  ext a b
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply, sg]
  by_cases ha : i = a <;> by_cases hb : j = b <;> subst_vars <;> simp_all <;> split_ifs <;> simp

variable {S T : HSp D}

theorem det_fr_unit {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) : IsUnit (A.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)

theorem unitMap_fr (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) :
    unitMap (A.onb τ) (B.onb τ) i j = (B.fr τ)⁻¹ * Matrix.single i j (1 : ℂ) * A.fr τ := by
  simp only [unitMap, GlobalTheory.ChainFr.Fr.onb, Matrix.nonsing_inv_nonsing_inv _ (det_fr_unit A τ)]

theorem cplxO_unitMap_fr (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (i : Fin T.rank)
    (j : Fin S.rank) :
    cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j) =
      (B.fr τ)⁻¹ * Matrix.single i j ((((sg (B.ε τ i) * sg (A.ε τ j) : ℝ)) : ℂ) * Complex.I) * A.fr τ := by
  rw [unitMap_fr]
  have e : B.cart τ * ((B.fr τ)⁻¹ * Matrix.single i j (1 : ℂ) * A.fr τ) * A.cart τ =
      (B.fr τ)⁻¹ * (Formalism.REAL.Jm (B.ε τ) * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
    simp only [GlobalTheory.ChainFr.Fr.cart, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit B τ),
      Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit A τ)]
  rw [cplxO, e, jm_mul_single_mul_jm, ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_comm]

theorem fockMat_eq (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (z : Fin T.rank → Fin S.rank → ℂ) :
    fockMat A B τ z = (B.fr τ)⁻¹ * Matrix.of (fun i j => cf (B.ε τ i) (A.ε τ j) (z i j)) * A.fr τ := by
  have ht : ∀ i j, (((z i j).re : ℂ) • unitMap (A.onb τ) (B.onb τ) i j +
      ((z i j).im : ℂ) • cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j)) =
      (B.fr τ)⁻¹ * Matrix.single i j (cf (B.ε τ i) (A.ε τ j) (z i j)) * A.fr τ := by
    intro i j
    rw [cplxO_unitMap_fr, unitMap_fr, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul,
      ← Matrix.add_mul, ← Matrix.mul_add, Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
    congr 3
    simp only [cf, smul_eq_mul, mul_one, Complex.ofReal_mul]
    ring
  rw [fockMat]
  simp only [ht]
  simp only [← Matrix.sum_mul, ← Matrix.mul_sum]
  congr 2
  conv_rhs => rw [Matrix.matrix_eq_sum_single (Matrix.of _)]
  simp only [Matrix.of_apply]

def fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X : Matrix (Fin T.rank) (Fin S.rank) ℂ) : Fin T.rank → Fin S.rank → ℂ :=
  fun i j => cf (B.ε τ i) (A.ε τ j) ((B.fr τ * X * (A.fr τ)⁻¹) i j)

theorem fockInvMat_fockMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (z : Fin T.rank → Fin S.rank → ℂ) : fockInvMat A B τ (fockMat A B τ z) = z := by
  funext i j
  rw [fockInvMat, fockMat_eq]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit B τ),
    Matrix.mul_nonsing_inv _ (det_fr_unit A τ), Matrix.mul_one, Matrix.of_apply, cf_cf]

theorem fockMat_fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X : Matrix (Fin T.rank) (Fin S.rank) ℂ) : fockMat A B τ (fockInvMat A B τ X) = X := by
  rw [fockMat_eq]
  have e : (Matrix.of fun i j => cf (B.ε τ i) (A.ε τ j) (fockInvMat A B τ X i j)) = B.fr τ * X * (A.fr τ)⁻¹ := by
    ext i j; simp only [Matrix.of_apply, fockInvMat, cf_cf]
  rw [e, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_fr_unit A τ), Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ (det_fr_unit B τ)]

theorem continuous_fockMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) :
    Continuous (fockMat A B τ) := by
  unfold fockMat; fun_prop

theorem continuous_fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) :
    Continuous (fockInvMat A B τ) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_cf _ _).comp
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)

def fockInv (θ : InfFam D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (w : WO S T) :
    VCx D.what₂.Tau S.rank T.rank :=
  fun τ => fockInvMat A B τ (GlobalTheory.FockCompare.piW θ T S w τ)

theorem fockInv_fockPt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    fockInv θ A B (fockPt σ A B z) = z := by
  funext τ
  have e : GlobalTheory.FockCompare.piW θ T S (fockPt σ A B z) τ = fockMat A B τ (z τ) := congrFun (h.pi_iota T S _) τ
  show fockInvMat A B τ (GlobalTheory.FockCompare.piW θ T S (fockPt σ A B z) τ) = z τ
  rw [e, fockInvMat_fockMat]

theorem fockPt_fockInv {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) {w : WO S T} (hw : w.map (finPart D) = 0) :
    fockPt σ A B (fockInv θ A B w) = w := by
  have e : (fun τ => fockMat A B τ (fockInv θ A B w τ)) = GlobalTheory.FockCompare.piW θ T S w :=
    funext fun τ => fockMat_fockInvMat A B τ _
  rw [fockPt, e]
  exact h.iota_pi hw

theorem fockPt_transport : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ →
    ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), Continuous (fockPt σ A B) ∧
      (∀ w : WO S T, w.map (finPart D) = 0 → ∃ z, fockPt σ A B z = w) ∧
      ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g → ∃ (m : Measure (WO S T)) (α : WO S T → ℂ),
        SFinite m ∧ Integrable α m ∧ ∀ H : WO S T → ℂ, ∫ w, α w * H w ∂m = ∫ z, g z * H (fockPt σ A B z) := by
  intro D θ σ h S T A B
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : T2Space (WO S T) := (GlobalTheory.MixModel.lattice_Mx D T.rank S.rank).2.2.2.1
  have hc : Continuous (fockPt σ A B) :=
    (h.continuous_iota T S).comp (continuous_pi fun τ => (continuous_fockMat A B τ).comp (continuous_apply τ))
  have hic : Continuous (fockInv θ A B) := continuous_pi fun τ =>
    (continuous_fockInvMat A B τ).comp ((continuous_apply τ).comp (GlobalTheory.FockCompare.continuous_pi' h.inf T S))
  have hl : Function.LeftInverse (fockInv θ A B) (fockPt σ A B) := fun z => fockInv_fockPt h A B z
  have hr : Set.range (fockPt σ A B) = {w | fockPt σ A B (fockInv θ A B w) = w} := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg (fockPt σ A B) (hl z)
    · intro hw
      exact ⟨_, hw⟩
  have hme : MeasurableEmbedding (fockPt σ A B) :=
    MeasurableEmbedding.of_measurable_inverse hc.measurable
      (by rw [hr]; exact (isClosed_eq (hc.comp hic) continuous_id).measurableSet) hic.measurable hl
  refine ⟨hc, fun w hw => ⟨_, fockPt_fockInv h A B hw⟩, fun g hg => ?_⟩
  haveI : SigmaFinite (volume : Measure (Fin S.rank → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin T.rank → Fin S.rank → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (VCx D.what₂.Tau S.rank T.rank)) := inferInstance
  refine ⟨Measure.map (fockPt σ A B) volume, g ∘ fockInv θ A B, MeasureTheory.Measure.instSFiniteMap _ _, ?_, fun H => ?_⟩
  · rw [hme.integrable_map_iff]
    have e : (g ∘ fockInv θ A B) ∘ fockPt σ A B = g := funext fun z => congrArg g (hl z)
    rw [e]; exact hg
  · rw [hme.integral_map]
    simp only [Function.comp_apply, hl _]

end GlobalTheory.FockTransport
