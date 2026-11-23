import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder Kronecker

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_kron_pos {m n : ℕ} {P : Matrix (Fin m) (Fin m) ℂ} {Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) (x : Matrix (Fin m) (Fin n) ℂ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (x i j) * P i k * Q j l * x k l := by
  have h := (hP.kronecker hQ).dotProduct_mulVec_pos (x := fun p : Fin m × Fin n => x p.1 p.2)
    (fun h0 => hx (by ext i j; exact congrFun h0 (i, j)))
  convert h using 1
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, Finset.mul_sum, kroneckerMap_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
  rw [Complex.star_def]; ring

theorem IsCart.adj_mul {n : ℕ} {G t : Matrix (Fin n) (Fin n) ℂ} (h : IsCart G t) :
    (t.map (starRingEnd ℂ))ᵀ * G = G * t := by
  have e : (t.map (starRingEnd ℂ))ᵀ = tᴴ := by ext i j; rfl
  rw [e]
  calc tᴴ * G = tᴴ * G * (t * t) := by rw [h.1, Matrix.mul_one]
    _ = G * t := by rw [← Matrix.mul_assoc, h.2.1]

theorem hC_actC_pos {D : D7} (V W : HSp D) (τ : D.what₂.Tau) (t : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (t' : Matrix (Fin W.rank) (Fin W.rank) ℂ) (h : IsCart (gramAt D V τ) t) (h' : IsCart (gramAt D W τ) t')
    (x : WC V W) (hx : x ≠ 0) : 0 < hC V W τ x (actC V W t t' x) := by
  unfold hC actC
  split_ifs with hr
  · have p := sum_kron_pos h.2.2.transpose h'.2.2 x hx
    simp only [Matrix.transpose_apply] at p
    rw [GlobalTheory.DualPairCheck.sum_small] at p ⊢
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    convert p using 2
    rw [← h.adj_mul]
    simp only [Matrix.mul_assoc]
  · have p := sum_kron_pos h.2.2 h'.2.2.transpose x hx
    simp only [Matrix.transpose_apply] at p
    rw [GlobalTheory.DualPairCheck.sum_large] at p ⊢
    convert p using 2
    rw [← h'.adj_mul]
    simp only [Matrix.mul_assoc]

theorem symplC_jAt_neg : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V)
    (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') →
    ∀ x : WC V W, x ≠ 0 → 0 < -symplC V W τ (jAt V W τ s s' x) x := by
  intro D V W τ s s' h h' x hx
  have p := hC_actC_pos V W τ _ _ h h' x hx
  have q := xi_zero_im_pos D τ
  unfold symplC jAt
  rw [hC_smul_right]
  obtain ⟨p1, p2⟩ := Complex.pos_iff.1 p
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, ← p2]
  nlinarith [mul_pos p1 q]

end GlobalTheory.FockCompare
