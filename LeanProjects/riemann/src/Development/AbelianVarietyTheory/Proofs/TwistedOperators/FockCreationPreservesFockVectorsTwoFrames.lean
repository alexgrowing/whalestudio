import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LowVanishFockOfLowVanish
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCreaDir

section Mat

variable {m n : ℕ}

theorem eq_sum_unitMap {Bm : Matrix (Fin m) (Fin m) ℂ} {Am : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit Bm.det)
    (hA : IsUnit Am.det) (z : Matrix (Fin m) (Fin n) ℂ) :
    z = ∑ i, ∑ j, (Bm⁻¹ * z * Am) i j • Formalism.IndefR.Datum.unitMap Am Bm i j := by
  have e : z = Bm * (Bm⁻¹ * z * Am) * Am⁻¹ := by
    rw [← Matrix.mul_assoc Bm, ← Matrix.mul_assoc Bm, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hA]
  have e2 := Matrix.matrix_eq_sum_single (Bm⁻¹ * z * Am)
  calc z = Bm * (∑ i, ∑ j, Matrix.single i j ((Bm⁻¹ * z * Am) i j)) * Am⁻¹ := by rw [← e2, ← e]
    _ = _ := by
      simp only [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have h : Matrix.single i j ((Bm⁻¹ * z * Am) i j) = ((Bm⁻¹ * z * Am) i j) • Matrix.single i j (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [h, Matrix.mul_smul, Matrix.smul_mul, Formalism.IndefR.Datum.unitMap]

theorem Jm_single_Jm (ε : Fin m → Bool) (δ : Fin n → Bool) (i : Fin m) (j : Fin n) :
    Formalism.REAL.Jm ε * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm δ =
      (if (ε i == δ j) then 1 else -1 : ℂ) • Matrix.single i j (1 : ℂ) := by
  ext p q
  rw [Formalism.REAL.Jm, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  by_cases h : i = p ∧ j = q
  · obtain ⟨rfl, rfl⟩ := h
    cases ε i <;> cases δ j <;> simp
  · simp [h]

end Mat

open GlobalTheory.ChainFr

variable {D : D7} {V W : HSp D}

theorem cplxO_unitMap_fr (A : Fr V) (B : Fr W) (τ : D.what₂.Tau) (i : Fin W.rank) (j : Fin V.rank) :
    cplxO (A.cart τ) (B.cart τ) (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) =
      ((if (B.ε τ i == A.ε τ j) then 1 else -1 : ℂ) * Complex.I) •
        Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := by
  have hA := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hB := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
  have h1 : B.cart τ * B.onb τ = B.onb τ * Formalism.REAL.Jm (B.ε τ) := by
    rw [Fr.cart, Fr.onb, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
  have h2 : (A.onb τ)⁻¹ * A.cart τ = Formalism.REAL.Jm (A.ε τ) * (A.onb τ)⁻¹ := by
    rw [Fr.cart, Fr.onb, Matrix.nonsing_inv_nonsing_inv _ hA]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  unfold cplxO Formalism.IndefR.Datum.unitMap
  rw [mul_comm _ Complex.I, ← smul_smul]
  congr 1
  calc B.cart τ * (B.onb τ * Matrix.single i j (1 : ℂ) * (A.onb τ)⁻¹) * A.cart τ
      = (B.cart τ * B.onb τ) * Matrix.single i j (1 : ℂ) * ((A.onb τ)⁻¹ * A.cart τ) := by
        simp only [Matrix.mul_assoc]
    _ = B.onb τ * (Formalism.REAL.Jm (B.ε τ) * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm (A.ε τ)) * (A.onb τ)⁻¹ := by
        rw [h1, h2]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Jm_single_Jm, Matrix.mul_smul, Matrix.smul_mul]

theorem fockScale_ne_zero (D : D7) (τ : D.what₂.Tau) : ((fockScale D τ : ℝ) : ℂ) ≠ 0 := by
  have h0 : 0 < ‖tauE D τ D.host.xi0‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := Formalism.L2.Theta.xi_zero_im_pos D τ
    rw [h] at this
    simp at this
  have : 0 < fockScale D τ := by
    unfold fockScale
    have := Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) h0)
    positivity
  exact_mod_cast this.ne'

end GlobalTheory.FockCreaDir

open GlobalTheory.FockCreaDir in

theorem GlobalTheory.FockCreaDir.crea_ptF : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (P : PolF D W.rank V.rank), ∃ Q : PolF D W.rank V.rank, crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f Q := by
  intro D V W A B θ ψ hψ hθ f hf τ z P
  have hS := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  have hadd : ∀ g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → IsThetaFunO ψ V W (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ v g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W
      (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v g) :=
    fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ v Q,
      pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v
        (pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f Q) := fun v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ V W) hadd hsm hth ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hg : IsThetaFunO ψ V W (GlobalTheory.ChainFr.ptF ψ θ A B f P) :=
    GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ V W) hadd hsm hth hf P
  have hdA : IsUnit (A.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  have hdB : IsUnit (B.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  obtain ⟨c, rfl⟩ : ∃ c : Fin W.rank → Fin V.rank → ℂ,
      z = ∑ i, ∑ j, c i j • Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := ⟨_, eq_sum_unitMap hdB hdA z⟩
  refine ⟨((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) •
    (MvPolynomial.X (τ, i, j) * P), ?_⟩
  have h1 : ∀ (y : Matrix (Fin W.rank) (Fin V.rank) ℂ) g,
      crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g =
        ((fockScale D τ : ℝ) : ℂ) • Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g := fun y g => by
    rw [Formalism.IndefR.Datum.aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero D τ), one_smul]
  rw [h1]
  have h2 : GlobalTheory.ChainFr.ptF ψ θ A B f (((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
      (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) • (MvPolynomial.X (τ, i, j) * P)) =
      ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) •
        Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ))
          (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) (GlobalTheory.ChainFr.ptF ψ θ A B f P) := by
    unfold GlobalTheory.ChainFr.ptF pureTensorO
    simp only [map_smul, map_sum, hX]
    rfl
  rw [h2]
  congr 1
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg (B.ε τ i == A.ε τ j) _ (cplxO_unitMap_fr A B τ i j)
