import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SgRevNeZero
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

open Formalism.L2.KerInert.SharpPolyP

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

def zA {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  if IsOddPos (pos.symm τ).2 then (f τ).adjugate.transpose.submatrix id Fin.rev else f τ

def adjPol {n : ℕ} (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) : MvPolynomial (GL3Theta.FrV D n) ℂ :=
  MvPolynomial.aeval (fun k : GL3Theta.FrV D n => if IsOddPos (pos.symm k.1).2 then
    (Matrix.of fun a b : Fin n => (MvPolynomial.X (k.1, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)).adjugate (Fin.rev k.2.2) k.2.1
    else MvPolynomial.X k) Q

theorem eval_adj {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (i j : Fin n) :
    MvPolynomial.eval (pt x) ((Matrix.of fun a b : Fin n => (MvPolynomial.X (τ, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)).adjugate i j)
      = (x τ).adjugate i j := by
  have h := congrArg (fun M => M i j) (RingHom.map_adjugate (MvPolynomial.eval (pt x))
    (Matrix.of fun a b : Fin n => (MvPolynomial.X (τ, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)))
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h
  rw [h]
  congr 1
  ext a b
  simp

theorem eval_adjPol {n : ℕ} (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (pt x) (adjPol X D pos Q) = MvPolynomial.eval (pt (zA X D pos x)) Q := by
  unfold adjPol
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X q k hq =>
    rw [map_mul, map_mul, hq, map_mul]
    congr 1
    rw [MvPolynomial.aeval_X, MvPolynomial.eval_X]
    show _ = zA X D pos x k.1 k.2.1 k.2.2
    unfold zA
    split_ifs with h
    · rw [eval_adj]; rfl
    · rw [MvPolynomial.eval_X]

def dg {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun _ => if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1

theorem zT_eq_mul {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos x = fun τ => zA X D pos x τ * dg X D pos x τ := by
  funext τ
  unfold zT zA dg
  split_ifs with h
  · ext i j
    simp [Matrix.mul_diagonal, Matrix.inv_def, Ring.inverse_eq_inv', mul_comm]
  · simp

theorem dg_bor {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hx : ∀ τ, (x τ).det ≠ 0) :
    IsBor (dg X D pos x) := by
  intro τ
  refine ⟨fun r s hsr => ?_, fun r => ?_⟩
  · unfold dg
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hsr)
  · unfold dg
    rw [Matrix.diagonal_apply_eq]
    split_ifs
    · exact inv_ne_zero (hx τ)
    · exact one_ne_zero

theorem eval_zT {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (hQ : Q ∈ WtPol ℂ ν)
    (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hx : ∀ τ, (x τ).det ≠ 0) :
    MvPolynomial.eval (pt (zT X D pos x)) Q =
      (∏ τ, ∏ r, (if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1) ^ ν τ r) *
        MvPolynomial.eval (pt x) (adjPol X D pos Q) := by
  rw [eval_adjPol, zT_eq_mul, ← sp_eval_colSub (dg X D pos x) (zA X D pos x) Q, hQ _ (dg_bor X D pos x hx),
    MvPolynomial.smul_eval]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun r _ => ?_
  unfold dg
  rw [Matrix.diagonal_apply_eq]

theorem twF_mul_det_poly : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}, 0 < n → ∀ (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ (K : D.what₂.Tau → ℕ) (P : MvPolynomial (GL3Theta.FrV D n) ℂ), ∀ x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (x τ).det ≠ 0) → MvPolynomial.eval (fun k : GL3Theta.FrV D n => x k.1 k.2.1 k.2.2) P = twF X D pos c Q x * ∏ τ, (x τ).det ^ K τ := by
  intro p _ X D pos n hn ν c hc Q hQ
  have hc0 : ∀ τ, 0 ≤ c τ := fun τ => le_trans (Int.natCast_nonneg _) (hc τ ⟨0, hn⟩)
  refine ⟨fun τ => if IsOddPos (pos.symm τ).2 then ∑ r, ν τ r else 0,
    (∏ τ, if IsOddPos (pos.symm τ).2 then
        MvPolynomial.C ((sgRev n ^ (c τ).toNat)⁻¹) * frDet ℂ n τ ^ (c τ).toNat else 1) * adjPol X D pos Q, ?_⟩
  intro x hx
  change MvPolynomial.eval (pt x) _ = _
  have key : ∀ τ, MvPolynomial.eval (pt x) (if IsOddPos (pos.symm τ).2 then
        MvPolynomial.C ((sgRev n ^ (c τ).toNat)⁻¹) * frDet ℂ n τ ^ (c τ).toNat else 1) =
      (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ).det ^ (-(c τ)) else 1) *
        (∏ r, (if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1) ^ ν τ r) *
        (x τ).det ^ (if IsOddPos (pos.symm τ).2 then ∑ r, ν τ r else 0) := by
    intro τ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, c τ = m := ⟨(c τ).toNat, (Int.toNat_of_nonneg (hc0 τ)).symm⟩
    have hd := hx τ
    rw [det_zT]
    split_ifs with h
    · rw [map_mul, map_pow, MvPolynomial.eval_C, sp_eval_frDet, hm, Int.toNat_natCast, zpow_neg, zpow_natCast,
        Finset.prod_pow_eq_pow_sum, mul_assoc, ← mul_pow, inv_mul_cancel₀ hd, one_pow, mul_one, mul_pow, mul_inv,
        inv_pow, inv_inv]
    · simp
  unfold twF
  rw [map_mul, map_prod, Finset.prod_congr rfl (fun τ _ => key τ), Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  change _ = _ * MvPolynomial.eval (pt (zT X D pos x)) Q * _
  rw [eval_zT X D pos ν Q hQ x hx]
  ring

end GlobalTheory.TwV.DelA
