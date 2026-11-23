import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaWeightRowInd

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section LC

variable {K σ ρ : Type} [Field K]

private theorem coeff_lcoef_eq (L : MvPolynomial ρ K →ₗ[K] K) (f : MvPolynomial σ (MvPolynomial ρ K))
    (w : σ →₀ ℕ) : coeff w (lcoef L f) = L (coeff w f) :=
  coeff_sum_monomial_linear L f w

theorem qa_lcoef_monomial (L : MvPolynomial ρ K →ₗ[K] K) (u : σ →₀ ℕ) (b : MvPolynomial ρ K) :
    lcoef L (monomial u b) = monomial u (L b) := by
  classical
  ext w
  rw [coeff_lcoef_eq, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem qa_lcoef_C (L : MvPolynomial ρ K →ₗ[K] K) (b : MvPolynomial ρ K) :
    lcoef L (C b : MvPolynomial σ (MvPolynomial ρ K)) = C (L b) := by
  classical
  ext w
  rw [coeff_lcoef_eq, coeff_C, coeff_C]
  split_ifs <;> simp

theorem qa_lcoef_mapC_mul (L : MvPolynomial ρ K →ₗ[K] K) (G : MvPolynomial σ K)
    (h : MvPolynomial σ (MvPolynomial ρ K)) : lcoef L (map C G * h) = G * lcoef L h := by
  classical
  ext w
  rw [coeff_lcoef_eq, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_lcoef_eq, MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem qa_eval_lcoef (L : MvPolynomial ρ K →ₗ[K] K) (x : σ → K) (h : MvPolynomial σ (MvPolynomial ρ K)) :
    eval x (lcoef L h) = L (eval (fun i => C (x i)) h) := by
  classical
  rw [show lcoef L h = ∑ u ∈ h.support, monomial u (L (coeff u h)) from rfl, map_sum]
  conv_rhs => rw [h.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [eval_monomial, eval_monomial]
  rw [show (u.prod fun n e => (C (x n) : MvPolynomial ρ K) ^ e) = C (u.prod fun n e => x n ^ e) by
    simp [Finsupp.prod, map_prod, map_pow]]
  rw [mul_comm (coeff u h), MvPolynomial.C_mul', map_smul, smul_eq_mul, mul_comm]

theorem qa_lcoef_rowAct {k n : ℕ} (L : MvPolynomial ρ K →ₗ[K] K) (g : Matrix (Fin k) (Fin k) K)
    (h : MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)) :
    lcoef L (rowAct (MvPolynomial ρ K) (g.map C) h) = rowAct K g (lcoef L h) := by
  classical
  have key : ∀ P : MvPolynomial (Fin k × Fin n) K,
      rowAct (MvPolynomial ρ K) (g.map C) (map C P) = map C (rowAct K g P) := by
    intro P
    have e := MvPolynomial.ringHom_ext
      (f := ((rowAct (MvPolynomial ρ K) (n := n) (g.map C)).toRingHom.comp (map C) :
        MvPolynomial (Fin k × Fin n) K →+* MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)))
      (g := ((map C).comp (rowAct K (n := n) g).toRingHom :
        MvPolynomial (Fin k × Fin n) K →+* MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)))
      (fun a => by simp [rowAct]) (fun i => by simp [rowAct, Matrix.map_apply, map_sum])
    simpa using RingHom.congr_fun e P
  conv_lhs => rw [h.as_sum]
  conv_rhs => rw [h.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hm : (monomial u (coeff u h) : MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)) =
      map C (monomial u 1) * C (coeff u h) := by
    rw [map_monomial, map_one, mul_comm, C_mul_monomial, mul_one]
  have hr1 : rowAct (MvPolynomial ρ K) (n := n) (g.map C) (C (coeff u h)) = C (coeff u h) := by simp [rowAct]
  have hr2 : rowAct K (n := n) g (C (L (coeff u h))) = C (L (coeff u h)) := by simp [rowAct]
  rw [hm, map_mul, key, hr1, qa_lcoef_mapC_mul, qa_lcoef_mapC_mul, qa_lcoef_C, map_mul, hr2]

end LC

section S2

variable {K : Type} [Field K] {r : ℕ}

theorem qa_blockEmb_C {S : Type} {k n : ℕ} (b : S) (a : K) : blockEmb K (k := k) (n := n) b (C a) = C a := by
  simp [blockEmb]

theorem qa_blockEmb_X {S : Type} {k n : ℕ} (b : S) (x : Fin k × Fin n) : blockEmb K b (X x) = X (b, x) := by
  simp [blockEmb]

theorem block_substitution_C (a : K) : sub2 K r (C a) = C (C a) := by
  simp [sub2]

theorem block_substitution_X (b : Bool) (x : Fin (r + 1 + 1) × Fin (r + 1 + 1)) :
    sub2 K r (X (b, x)) = map (blockEmb K (k := r) (n := r) b).toRingHom (subY K r (X x)) := by
  simp [sub2]

theorem block_substitution_blockEmb (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    sub2 K r (blockEmb K b v) = map (blockEmb K (k := r) (n := r) b).toRingHom (subY K r v) := by
  induction v using MvPolynomial.induction_on
  next a =>
    rw [qa_blockEmb_C, block_substitution_C]
    simp [subY, qa_blockEmb_C]
  next p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add, map_add]
  next p x hp =>
    rw [map_mul, map_mul, hp, qa_blockEmb_X, block_substitution_X, map_mul, map_mul]

theorem qa_blockEmb_comp_C (b : Bool) :
    ((blockEmb K (k := r) (n := r) b).toRingHom).comp C = (C : K →+* MvPolynomial (Bool × (Fin r × Fin r)) K) := RingHom.ext fun a => by simp [qa_blockEmb_C]

theorem qa_lamOf_apply (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (x : MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K) : lamOf K r L x = lcoef L (sub2 K r x) := rfl

theorem qa_eval_map_block (b : Bool)
    (h : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K)) :
    eval (fun i => (C (idPoint K (r + 1 + 1) (r + 1 + 1) i) : MvPolynomial (Bool × (Fin r × Fin r)) K))
        (map (blockEmb K (k := r) (n := r) b).toRingHom h) =
      blockEmb K b (eval (idPoint (MvPolynomial (Fin r × Fin r) K) (r + 1 + 1) (r + 1 + 1)) h) := by
  rw [MvPolynomial.eval_map]
  show _ = (blockEmb K (k := r) (n := r) b).toRingHom
    (MvPolynomial.eval₂ (RingHom.id _) (idPoint (MvPolynomial (Fin r × Fin r) K) (r + 1 + 1) (r + 1 + 1)) h)
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext i
  simp only [idPoint, Function.comp_apply]
  split_ifs <;> simp

end S2

theorem lamCoeffP : LamCoeffP := by
  classical
  intro K _ r L v t u
  rw [qa_lamOf_apply, map_mul, block_substitution_blockEmb, block_substitution_blockEmb, coeff_lcoef_eq, coeff_mul, map_sum]
  simp only [coeff_map]
  rfl

theorem lamMulP : LamMulP := by
  classical
  intro K _ r Q L F s t hF
  rw [qa_lamOf_apply, map_mul (blockEmb K true) F s, map_mul (sub2 K r), map_mul (sub2 K r),
    block_substitution_blockEmb, block_substitution_blockEmb, block_substitution_blockEmb, hF,
    map_mul (map (blockEmb K (k := r) (n := r) true).toRingHom), map_C, MvPolynomial.map_map,
    qa_blockEmb_comp_C, ← qa_lcoef_mapC_mul]
  congr 1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

theorem lamEvalP : LamEvalP := by
  classical
  intro K _ r L v t
  rw [qa_lamOf_apply, map_mul, block_substitution_blockEmb, block_substitution_blockEmb, qa_eval_lcoef, map_mul,
    qa_eval_map_block, qa_eval_map_block]
  rfl

theorem lamEquivP : LamEquivP := by
  intro K _ r L g v t
  have hcomm : ∀ (b : Bool) (P : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K)),
      map (blockEmb K (k := r) (n := r) b).toRingHom
          (rowAct (MvPolynomial (Fin r × Fin r) K) (n := r + 1 + 1) (g.map C) P) =
        rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)
          (map (blockEmb K (k := r) (n := r) b).toRingHom P) := by
    intro b P
    have e := MvPolynomial.ringHom_ext
      (f := ((map (blockEmb K (k := r) (n := r) b).toRingHom).comp
          (rowAct (MvPolynomial (Fin r × Fin r) K) (n := r + 1 + 1) (g.map C)).toRingHom :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K) →+*
          MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)))
      (g := ((rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)).toRingHom.comp
          (map (blockEmb K (k := r) (n := r) b).toRingHom) :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K) →+*
          MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)))
      (fun c => by simp [rowAct]) (fun i => by simp [rowAct, Matrix.map_apply, map_sum, qa_blockEmb_C])
    simpa using RingHom.congr_fun e P
  rw [qa_lamOf_apply, qa_lamOf_apply, map_mul (sub2 K r), map_mul (sub2 K r), block_substitution_blockEmb,
    block_substitution_blockEmb, block_substitution_blockEmb, block_substitution_blockEmb, qa_subY_rowAct, qa_subY_rowAct, hcomm, hcomm,
    ← map_mul (rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)), qa_lcoef_rowAct]

end Formalism.MainNotions.flipOneThree.Pf

end
