import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamF
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumReImAddSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem fmR_coordX_self {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank) :
    fmR A B (Formalism.L2.Ker.coordX l) l.1 = unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  rw [Finset.sum_eq_single l.2.1, Finset.sum_eq_single l.2.2]
  · simp; rfl
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; simp [hi]
  · simp

theorem fmR_coordX_ne {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (τ' : D.what₂.Tau) (h : τ' ≠ l.1) : fmR A B (Formalism.L2.Ker.coordX l) τ' = 0 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp [h]; rfl

theorem fmR_I_coordX_self {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank) :
    fmR A B (I • Formalism.L2.Ker.coordX l) l.1 =
      cplxO (A.cart l.1) (B.cart l.1) (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2) := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  rw [Finset.sum_eq_single l.2.1, Finset.sum_eq_single l.2.2]
  · simp; rfl
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; simp [hi]
  · simp

theorem fmR_I_coordX_ne {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (τ' : D.what₂.Tau) (h : τ' ≠ l.1) : fmR A B (I • Formalism.L2.Ker.coordX l) τ' = 0 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp [h]; rfl

theorem gq_add_smul {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) (z e : VCx ι a b) (t : ℝ) :
    gq c (z + t • e) = gq c z + t * gD c z e + t ^ 2 * gq c e := by
  have key : ∀ (k : ℝ) (p q : ℂ), k * ‖p + t • q‖ ^ 2 =
      k * ‖p‖ ^ 2 + t * (2 * (k * (p * conj q).re)) + t ^ 2 * (k * ‖q‖ ^ 2) := by
    intro k p q
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  unfold gq gD
  simp only [Pi.add_apply, Pi.smul_apply, key, Finset.sum_add_distrib, Finset.mul_sum]

theorem heisO_eq_exp_rd (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D}
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (w : VCx D.what₂.Tau S.rank T.rank) :
    heisO ψ S T (fockPt σ A B w) h x = Complex.exp (-((gq (fw D) w : ℂ) / 2)) * rd ψ σ A B h x w := by
  unfold rd
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf
  simp

theorem heis_dRho_fock_eval (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D)
    (hψ : IsStdChar D ψ (-1)) (hC : GlobalTheory.FockCompare.Chart θ σ) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S)
    (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (z e : VCx D.what₂.Tau S.rank T.rank) (τ : D.what₂.Tau)
    (v : Matrix (Fin T.rank) (Fin S.rank) ℂ) (hv : fmR A B e τ = v) (h0 : ∀ τ', τ' ≠ τ → fmR A B e τ' = 0)
    (hd : DifferentiableAt ℝ (rd ψ σ A B h x) z) :
    heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ v h) x =
      Complex.exp (-((gq (fw D) z : ℂ) / 2)) *
        ((-((Real.pi : ℂ) * I) * (omF A B z e : ℂ) - (gD (fw D) z e : ℂ) / 2) * rd ψ σ A B h x z +
          fderiv ℝ (rd ψ σ A B h x) z e) := by
  rw [heis_dRho_fock D ψ θ σ hψ hC S T A B h x z e τ v hv h0]
  have hfun : (fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * I) * ((t * omF A B z e : ℝ) : ℂ)) *
      heisO ψ S T (fockPt σ A B (z + t • e)) h x) = fun t : ℝ =>
      Complex.exp (-((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) - ((gq (fw D) z : ℂ) +
        (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2) * rd ψ σ A B h x (z + t • e) := by
    funext t
    rw [heisO_eq_exp_rd, gq_add_smul, ← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hfun]
  have hline : HasDerivAt (fun t : ℝ => z + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
  have hRd : HasDerivAt (fun t : ℝ => rd ψ σ A B h x (z + t • e)) (fderiv ℝ (rd ψ σ A B h x) z e) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact this
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hP : HasDerivAt (fun t : ℝ => -((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) - ((gq (fw D) z : ℂ) +
        (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2)
      (-((Real.pi : ℂ) * I) * (omF A B z e : ℂ) - (gD (fw D) z e : ℂ) / 2) 0 := by
    have h1 := (hid.mul_const (omF A B z e : ℂ)).const_mul (-((Real.pi : ℂ) * I))
    have h2 := ((hid.mul_const (gD (fw D) z e : ℂ)).const_add (gq (fw D) z : ℂ)).add
      ((hid.pow 2).mul_const (gq (fw D) e : ℂ))
    have h3 := h1.sub (h2.div_const 2)
    convert h3 using 1
    all_goals first | rfl | (funext t; rfl) | simp
  have hD : HasDerivAt (fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) -
      ((gq (fw D) z : ℂ) + (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2) *
        rd ψ σ A B h x (z + t • e)) _ 0 := hP.cexp.mul hRd
  rw [hD.deriv]
  simp
  ring

theorem rd_aPlusAll : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (l : FVar D T.rank S.rank) (z : VCx D.what₂.Tau S.rank T.rank), DifferentiableAt ℝ (rd ψ σ A B h x) z → rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z = (2 / (fockScale D l.1 : ℂ)) * GlobalTheory.FockTransl.Jet.crOp A B l (rd ψ σ A B h x) z := by
  intro D ψ θ σ hψ hC S T A B h x l z hd
  have h1 := heis_dRho_fock_eval D ψ θ σ hψ hC S T A B h x z (Formalism.L2.Ker.coordX l) l.1 _
    (fmR_coordX_self A B l) (fmR_coordX_ne A B l) hd
  have h2 := heis_dRho_fock_eval D ψ θ σ hψ hC S T A B h x z (I • Formalism.L2.Ker.coordX l) l.1 _
    (fmR_I_coordX_self A B l) (fmR_I_coordX_ne A B l) hd
  have hlin : heisO ψ S T (fockPt σ A B z)
      (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x =
      (fockScale D l.1 : ℂ)⁻¹ *
        (heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ l.1
            (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2) h) x -
          I * heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ l.1
            (cplxO (A.cart l.1) (B.cart l.1) (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2)) h) x) := by
    simp only [aPlusAll, aPlus, crea, heisO, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hexp : (Real.exp (gq (fw D) z / 2) : ℂ) * Complex.exp (-((gq (fw D) z : ℂ) / 2)) = 1 := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    simp
  have hrd : rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z =
      (Real.exp (gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z)
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x := rfl
  rw [hrd, hlin, h1, h2]
  unfold crOp lamF
  linear_combination (↑(fockScale D l.1))⁻¹ *
    ((-((Real.pi : ℂ) * I) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ) - (gD (fw D) z (Formalism.L2.Ker.coordX l) : ℂ) / 2) *
        rd ψ σ A B h x z + fderiv ℝ (rd ψ σ A B h x) z (Formalism.L2.Ker.coordX l) -
      I * ((-((Real.pi : ℂ) * I) * (omF A B z (I • Formalism.L2.Ker.coordX l) : ℂ) -
        (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ) / 2) * rd ψ σ A B h x z +
        fderiv ℝ (rd ψ σ A B h x) z (I • Formalism.L2.Ker.coordX l))) * hexp +
    (↑(fockScale D l.1))⁻¹ * (Real.pi : ℂ) * (omF A B z (I • Formalism.L2.Ker.coordX l) : ℂ) * rd ψ σ A B h x z * I_sq

end GlobalTheory.FockTransl.Jet

end
