import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.FormalGroupSystem Matrix

variable (p : ℕ) [hp : Fact p.Prime]

def sig2 : WW p →+* WW p := (sigW p).comp (sigW p)

theorem frobenius_sq_iterate (i : ℕ) (x : WW p) : (sig2 p)^[i] x = (sigW p)^[2 * i] x := by
  have h : ⇑(sig2 p) = (⇑(sigW p))^[2] := by
    funext y
    rfl
  rw [h, ← Function.iterate_mul]

theorem sigW_teich (y : kb p) : sigW p (WittVector.teichmuller p y) = WittVector.teichmuller p (y ^ p) := by
  show WittVector.frobenius (WittVector.teichmuller p y) = _
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

theorem frobenius_sq_iterate_teichmuller (y : kb p) (i : ℕ) :
    (sig2 p)^[i] (WittVector.teichmuller p y) = WittVector.teichmuller p (y ^ (p ^ (2 * i))) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    show sigW p (sigW p (WittVector.teichmuller p _)) = _
    rw [sigW_teich, sigW_teich, ← pow_mul, ← pow_mul]
    congr 2
    ring

theorem one_lt_q (m : ℕ) : 1 < p ^ (2 * (m + 1)) := by
  exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)

theorem exists_theta (m : ℕ) : ∃ θ : kb p, IsPrimitiveRoot θ (p ^ (2 * (m + 1)) - 1) := by
  have h1 : 1 ≤ p ^ (2 * (m + 1)) := (one_lt_q p m).le
  have : NeZero (((p ^ (2 * (m + 1)) - 1 : ℕ)) : ZMod p) := ⟨by
    rw [Nat.cast_sub h1, Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega), Nat.cast_one,
      zero_sub]
    exact neg_ne_zero.mpr one_ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (kb p) _

theorem pow_lt_q (m i : ℕ) (hi : i ≤ m) : p ^ (2 * i) < p ^ (2 * (m + 1)) - 1 := by
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpos : 0 < p ^ (2 * i) := pow_pos (by omega) _
  have hle : p ^ (2 * i) * (p * p) ≤ p ^ (2 * (m + 1)) := by
    calc p ^ (2 * i) * (p * p) = p ^ (2 * i + 2) := by ring
      _ ≤ p ^ (2 * (m + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : p ^ (2 * i) * 4 ≤ p ^ (2 * i) * (p * p) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h2)
  generalize p ^ (2 * i) = A at *
  generalize p ^ (2 * (m + 1)) = Q at *
  generalize p * p = P at *
  omega

theorem core (m : ℕ) : ∃ om omS : Fin (m + 1) → WW p,
    (∀ r, (sig2 p)^[m + 1] (om r) = om r) ∧ (∀ r, (sig2 p)^[m + 1] (omS r) = omS r) ∧
    ∀ r r', ∑ i : Fin (m + 1), (sig2 p)^[i.val] (om r * omS r') = if r = r' then 1 else 0 := by
  obtain ⟨θ, hθ⟩ := exists_theta p m
  have hper : (sig2 p)^[m + 1] (WittVector.teichmuller p θ) = WittVector.teichmuller p θ := by
    rw [frobenius_sq_iterate_teichmuller]
    congr 1
    have h1 : 1 ≤ p ^ (2 * (m + 1)) := (one_lt_q p m).le
    have hq : p ^ (2 * (m + 1)) = (p ^ (2 * (m + 1)) - 1) + 1 := by omega
    rw [hq, pow_succ, hθ.pow_eq_one, one_mul]
  have hper' : Function.IsPeriodicPt (sig2 p) (m + 1) (WittVector.teichmuller p θ) := hper
  obtain ⟨v, hv⟩ : ∃ v : Fin (m + 1) → WW p,
      v = fun i => (sig2 p)^[i.val] (WittVector.teichmuller p θ) := ⟨_, rfl⟩
  have hvi : ∀ i, v i = (sig2 p)^[i.val] (WittVector.teichmuller p θ) := fun i => by rw [hv]
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Fin (m + 1), g = fun k => ⟨k % (m + 1), Nat.mod_lt _ (by omega)⟩ :=
    ⟨_, rfl⟩
  have hgv : ∀ k, (g k).val = k % (m + 1) := fun k => by rw [hg]
  have hg1 : ∀ k, g (k + 1) = g k + 1 := by
    intro k
    rw [Fin.ext_iff, Fin.val_add, Fin.val_one', hgv, hgv, Nat.add_mod]
  have hgi : ∀ i : Fin (m + 1), g i.val = i := fun i => by
    rw [Fin.ext_iff, hgv, Nat.mod_eq_of_lt i.isLt]
  have hvk : ∀ k : ℕ, v (g k) = (sig2 p)^[k] (WittVector.teichmuller p θ) := by
    intro k
    rw [hvi, hgv, hper'.iterate_mod_apply]
  have hshift : ∀ i : Fin (m + 1), sig2 p (v i) = v (i + 1) := by
    intro i
    have h := hvk (i.val + 1)
    rw [hg1, hgi, Function.iterate_succ_apply', ← hvi] at h
    exact h.symm
  have hdet : IsUnit (Matrix.vandermonde v).det := by
    rw [Matrix.det_vandermonde]
    refine Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => ?_)
    refine Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isUnit_one (fun j hj => ?_)
    have hij : i < j := Finset.mem_Ioi.mp hj
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [hvi, hvi, frobenius_sq_iterate_teichmuller, frobenius_sq_iterate_teichmuller, ← WittVector.constantCoeff_apply, map_sub]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [sub_ne_zero]
    intro h
    have hj' : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
    have hi' : i.val ≤ m := Nat.lt_succ_iff.mp i.isLt
    have e1 := hθ.pow_inj (pow_lt_q p m j.val hj') (pow_lt_q p m i.val hi') h
    have e2 := Nat.pow_right_injective (Fact.out : p.Prime).two_le e1
    have e3 : i.val < j.val := hij
    omega
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin (m + 1)) (Fin (m + 1)) (WW p),
      (Matrix.vandermonde v)ᵀ * B = 1 :=
    ⟨_, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hdet)⟩
  have hB' : B * (Matrix.vandermonde v)ᵀ = 1 := mul_eq_one_comm.mp hB
  have hBe : ∀ r s : Fin (m + 1),
      ∑ i : Fin (m + 1), v i ^ (r : ℕ) * B i s = if r = s then 1 else 0 := by
    intro r s
    have h := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) (WW p) => M r s) hB
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.vandermonde_apply] at h
    exact h
  obtain ⟨C, hCd⟩ : ∃ C : Matrix (Fin (m + 1)) (Fin (m + 1)) (WW p),
      C = Matrix.of fun i s => sig2 p (B (i - 1) s) := ⟨_, rfl⟩
  have hC : (Matrix.vandermonde v)ᵀ * C = 1 := by
    refine Matrix.ext fun r s => ?_
    rw [Matrix.mul_apply, Matrix.one_apply, hCd]
    simp only [Matrix.transpose_apply, Matrix.vandermonde_apply, Matrix.of_apply]
    rw [← Equiv.sum_comp (Equiv.addRight (1 : Fin (m + 1)))]
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    calc ∑ j : Fin (m + 1), v (j + 1) ^ (r : ℕ) * sig2 p (B j s)
        = sig2 p (∑ j : Fin (m + 1), v j ^ (r : ℕ) * B j s) := by
          rw [map_sum]
          simp only [map_mul, map_pow, hshift]
      _ = sig2 p (if r = s then 1 else 0) := by rw [hBe]
      _ = if r = s then 1 else 0 := by split_ifs <;> simp
  have hCB : C = B := by
    calc C = (B * (Matrix.vandermonde v)ᵀ) * C := by rw [hB', Matrix.one_mul]
      _ = B * ((Matrix.vandermonde v)ᵀ * C) := Matrix.mul_assoc _ _ _
      _ = B := by rw [hC, Matrix.mul_one]
  have hBshift : ∀ i s, sig2 p (B i s) = B (i + 1) s := by
    intro i s
    have h := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) (WW p) => M (i + 1) s) hCB
    simp only [hCd, Matrix.of_apply, add_sub_cancel_right] at h
    exact h
  have hBk : ∀ (k : ℕ) (s : Fin (m + 1)), (sig2 p)^[k] (B 0 s) = B (g k) s := by
    intro k s
    induction k with
    | zero =>
      rw [Function.iterate_zero_apply]
      congr 1
      rw [Fin.ext_iff, hgv, Nat.zero_mod]
      rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hBshift, hg1]
  refine ⟨fun r => (WittVector.teichmuller p θ) ^ (r : ℕ), fun r => B 0 r, ?_, ?_, ?_⟩
  · intro r
    rw [← RingHom.coe_pow, map_pow, RingHom.coe_pow, hper]
  · intro r
    rw [hBk]
    congr 1
    rw [Fin.ext_iff, hgv, Nat.mod_self]
    rfl
  · intro r r'
    rw [← hBe r r']
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← RingHom.coe_pow, map_mul, map_pow, RingHom.coe_pow, hBk, hgi, hvi]

theorem core' (ν : ℕ) (hν : 0 < ν) : ∃ om omS : Fin ν → WW p,
    (∀ r, (sig2 p)^[ν] (om r) = om r) ∧ (∀ r, (sig2 p)^[ν] (omS r) = omS r) ∧
    ∀ r r', ∑ i : Fin ν, (sig2 p)^[i.val] (om r * omS r') = if r = r' then 1 else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  exact core p m

theorem nonempty_omBasis (n' : ℕ) (he : Even n') (h2 : 2 ≤ n') : Nonempty (OmBasis p n') := by
  obtain ⟨om, omS, h1, h2, h3⟩ := core' p (n' / 2) (by omega)
  have hn : 2 * (n' / 2) = n' := Nat.two_mul_div_two_of_even he
  refine ⟨⟨om, omS, fun r => ?_, fun r => ?_, fun r r' => ?_⟩⟩
  · have h := h1 r
    rwa [frobenius_sq_iterate, hn] at h
  · have h := h2 r
    rwa [frobenius_sq_iterate, hn] at h
  · simpa only [frobenius_sq_iterate] using h3 r r'

def omOf (n' : ℕ) (he : Even n') (h2 : 2 ≤ n') : OmBasis p n' := Classical.choice (nonempty_omBasis p n' he h2)

end Formalism.L2.G.Pend
