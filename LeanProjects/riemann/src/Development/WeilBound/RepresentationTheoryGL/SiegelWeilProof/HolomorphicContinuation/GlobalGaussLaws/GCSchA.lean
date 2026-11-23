import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzCexpNegForm
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussA
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.InvNormSmulMemSphere

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GCSchH

variable {m n : ℕ}

theorem trace_gramB (Z : Matrix (Fin n) (Fin n) ℂ) (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (Z * gramB ε b u).trace = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a) ⬝ᵥ (Zᵀ *ᵥ u a) := by
  set S := Finset.univ.filter (fun a => ε a = b)
  have hG : ∀ i j, gramB ε b u j i = ∑ a ∈ S, star (u a j) * u a i := fun i j => GaussH.gramB_apply ε b u j i
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hG, Finset.mul_sum, dotProduct, mulVec,
    Matrix.transpose_apply, Pi.star_apply]
  calc _ = ∑ i, ∑ a ∈ S, ∑ j, Z i j * (star (u a j) * u a i) := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a ∈ S, ∑ i, ∑ j, Z i j * (star (u a j) * u a i) := Finset.sum_comm
    _ = ∑ a ∈ S, ∑ j, ∑ i, Z i j * (star (u a j) * u a i) := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem im_quad (W : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    (star y ⬝ᵥ (W *ᵥ y)).im = (star y ⬝ᵥ (((-(Complex.I / 2)) • (W - Wᴴ)) *ᵥ y)).re := by
  have hs : star (star y ⬝ᵥ (W *ᵥ y)) = star y ⬝ᵥ (Wᴴ *ᵥ y) := by
    rw [Matrix.star_dotProduct, Matrix.star_mulVec, star_star, ← Matrix.dotProduct_mulVec]
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub, ← hs]
  set s := star y ⬝ᵥ (W *ᵥ y)
  simp only [smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

theorem coercive_of_pos {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (h : ∀ x, x ≠ 0 → 0 < (Q x x).re) : ∃ κ, 0 < κ ∧ ∀ x, κ * ‖x‖ ^ 2 ≤ (Q x x).re :=
  _root_.UpperTheory.Reformulated.B.P6.r24a.PositivityTheory.Rg.Sw.Glob.GCSchH.coercive_of_pos Q h

end PositivityTheory.Rg.Sw.Glob.GCSchH
