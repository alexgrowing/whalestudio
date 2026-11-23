import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section aux

variable {P : M.Par}

theorem nf_evQ_toSm_le (u : MA.Qp P.r P.TT → ℂ) (q : MA.Qp P.r P.TT) : ‖MA.evQ P (MA.toSm P u) q‖ ≤ ‖u q‖ := by
  unfold MA.evQ MA.toSm
  split_ifs with h
  · exact le_rfl
  · simp

theorem nf_wq_eq (k r : ℕ) (T T' : ℝ) (x : (Fin r → ℂ) × ℂ) (hx : T * T' ≤ Complex.normSq x.2) :
    MA.wq k x (T * T') = (∏ l : Fin r, Complex.normSq (x.1 l)) * bcWeight k r T T' x := by
  unfold MA.wq bcWeight
  rw [if_pos hx, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  have hl : MA.Mdim k r l - 1 = (Formalism.QuantumDeterminants.Mdim k r l - 2) + 1 := by
    have := l.2
    unfold MA.Mdim Formalism.QuantumDeterminants.Mdim
    omega
  rw [hl, pow_mul, ← Complex.normSq_eq_norm_sq, pow_succ, mul_comm]

end aux

theorem trace_norm_bound_constant_one : NFTrNormKB := by
  intro Wp Wq _ _ _ _ _ _ P p e he
  refine ⟨1, fun H c q hq hloc hG => ?_⟩
  have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
  have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  have hon : Orthonormal ℂ (fun ρ => B.hsVec (e ρ q.1.2)) := by
    rw [orthonormal_iff_ite]
    convert (he.2 q.1.2 hζ).2.1
  have hw0 : 0 ≤ MA.wq P.k q.1 P.TT := by
    unfold MA.wq
    exact mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (Complex.normSq_nonneg _) _)
      (pow_nonneg (sub_nonneg.2 hζ.le) _)
  have hterm : ∀ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2 ≤
      MA.wq P.k q.1 P.TT *
        ‖inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1)))‖ ^ 2 := by
    intro ρ
    have h1 := nf_evQ_toSm_le (P := P) (fun q : MA.Qp P.r P.TT =>
      ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1)))) q
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (le_of_eq ?_)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hw0]
  have hsum : ∑ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2 ≤
      MA.wq P.k q.1 P.TT * ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1))‖ ^ 2 := by
    refine (Finset.sum_le_sum fun ρ _ => hterm ρ).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hon.sum_inner_products_le _) hw0
  have hwq : MA.wq P.k q.1 P.TT =
      (∏ l : Fin P.r, Complex.normSq (q.1.1 l)) * bcWeight P.k P.r P.T P.T' q.1 :=
    nf_wq_eq P.k P.r P.T P.T' q.1 hζ.le
  have hEw0 : 0 ≤ TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) := by
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p H hloc]
    positivity
  have hpt := pt_le p H c
  rw [hT, hT', ENNReal.ofReal_le_ofReal_iff hEw0] at hpt
  have hkey : bcWeight P.k P.r P.T P.T' q.1 * ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1))‖ ^ 2 ≤
      TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) := by
    unfold B.gq
    rw [hq]
    exact hpt
  have hprod : ∏ l : Fin P.r, Complex.normSq (q.1.1 l) = ∏ l : Fin P.r, Complex.normSq (c l.castSucc) := by
    rw [hq]
  calc ∑ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2
      ≤ (∏ l : Fin P.r, Complex.normSq (q.1.1 l)) *
          (bcWeight P.k P.r P.T P.T' q.1 * ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1))‖ ^ 2) := by
        rw [← mul_assoc, ← hwq]
        exact hsum
    _ ≤ (∏ l : Fin P.r, Complex.normSq (q.1.1 l)) * TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) :=
        mul_le_mul_of_nonneg_left hkey (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _)
    _ = 1 * (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) *
          TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) := by
        rw [hprod, one_mul]

end

end Formalism.FourierDecayAlt.P.CutBP
