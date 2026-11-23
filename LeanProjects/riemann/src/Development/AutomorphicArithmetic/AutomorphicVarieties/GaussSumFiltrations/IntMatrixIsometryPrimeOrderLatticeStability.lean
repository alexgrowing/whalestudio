import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.IsoP

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem pow_eq_one {p : ℕ} {S : Matrix κ κ ℤ} (h : ∑ i ∈ Finset.range p, S ^ i = 0) : S ^ p = 1 := by
  have := geom_sum_mul S p
  rw [h, zero_mul] at this
  exact (sub_eq_zero.mp this.symm)

theorem map_pow_eq (S : Matrix κ κ ℤ) (n : ℕ) : (S.map (Int.cast : ℤ → F)) ^ n = (S ^ n).map (Int.cast : ℤ → F) := by
  show ((Int.castRingHom F).mapMatrix S) ^ n = (Int.castRingHom F).mapMatrix (S ^ n)
  rw [map_pow]

theorem iter_eq (A : Matrix κ κ F) (n : ℕ) (x : κ → F) : (fun x => A *ᵥ x)^[n] x = (A ^ n) *ᵥ x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', Matrix.mulVec_mulVec]

theorem mem_LL (x : κ → F) : x ∈ LL F κ ↔ ∀ i, x i ∈ integralClosure ℤ F := by
  simp [LL, AddSubgroup.mem_pi]

theorem mulVec_LL (M : Matrix κ κ ℤ) {x : κ → F} (hx : x ∈ LL F κ) : (M.map (Int.cast : ℤ → F)) *ᵥ x ∈ LL F κ := by
  rw [mem_LL] at hx ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (hx j)

theorem mulVec_aL (M : Matrix κ κ ℤ) (a : F) {x : κ → F} (hx : x ∈ aL κ a) : (M.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a := by
  simp only [aL, AddSubgroup.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨_, mulVec_LL M hy, ?_⟩
  simp [Matrix.mulVec_smul]

theorem pow_mulVec_fix (A : Matrix κ κ F) {x : κ → F} (hx : A *ᵥ x = x) (n : ℕ) : (A ^ n) *ᵥ x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hx, ih]

theorem prime_not_dvd_of_neg_one_pow_mul_modEq_one {p : ℕ} (hp : p.Prime) {t : ℕ} {k : ℕ} (h : (-1) ^ k * (t : ℤ) ≡ 1 [ZMOD p]) : ¬ (p : ℤ) ∣ t := by
  intro hd
  have h2 := Int.modEq_iff_dvd.mp h
  have h3 : (p : ℤ) ∣ 1 := by
    have h4 := dvd_add h2 (dvd_mul_of_dvd_right hd ((-1) ^ k))
    simpa using h4
  have h5 : p ∣ 1 := by exact_mod_cast h3
  exact hp.not_dvd_one h5

private theorem sum_pow_map_intCast_eq_zero {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {p : ℕ} {S : Matrix κ κ ℤ} (cyc : ∑ i ∈ Finset.range p, S ^ i = 0) :
    ∑ i ∈ Finset.range p, (S.map (Int.cast : ℤ → F)) ^ i = 0 := by
  simp only [map_pow_eq]
  have e := congrArg (Int.castRingHom F).mapMatrix cyc
  rw [map_sum, map_zero] at e
  exact e

theorem isometry_order_p : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → (∀ x y : κ → F, BF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) ((S.map (Int.cast : ℤ → F)) *ᵥ y) = BF G x y ∧ QF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) = QF G x) ∧ (∀ x : κ → F, (fun x => (S.map (Int.cast : ℤ → F)) *ᵥ x)^[p] x = x ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x = x → x = 0) ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ dualL F G ↔ x ∈ dualL F G) ∧ ∀ a : F, ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a ↔ x ∈ aL κ a)) ∧ (∀ (N : ℕ) (x : κ → F), 0 < N → N.Coprime p → x ∈ aL κ (N : F)⁻¹ → (S.map (Int.cast : ℤ → F)) *ᵥ x - x ∈ aL κ (N : F) → x ∈ aL κ (N : F)) ∧ ¬ (p : ℤ) ∣ t := by
  intro F _ _ p hp κ _ _ G S t hL
  obtain ⟨_, _, iso, cyc, _, cong⟩ := hL
  have hφ : ∀ M : Matrix κ κ ℤ, M.map (Int.cast : ℤ → F) = (Int.castRingHom F).mapMatrix M := fun _ => rfl
  have hsum0 := sum_pow_map_intCast_eq_zero (F := F) cyc
  set S' : Matrix κ κ F := S.map (Int.cast : ℤ → F) with hS'
  have hpow : S' ^ p = 1 := by
    rw [hS', map_pow_eq, pow_eq_one cyc]
    simp
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  have hinv : ∀ y : κ → F, S' *ᵥ ((S ^ (p - 1)).map (Int.cast : ℤ → F) *ᵥ y) = y := by
    intro y
    rw [← map_pow_eq, Matrix.mulVec_mulVec, ← pow_succ', hp1, hpow, Matrix.one_mulVec]
  have hinv' : ∀ y : κ → F, (S ^ (p - 1)).map (Int.cast : ℤ → F) *ᵥ (S' *ᵥ y) = y := by
    intro y
    rw [← map_pow_eq, Matrix.mulVec_mulVec, ← pow_succ, hp1, hpow, Matrix.one_mulVec]
  have hsum : ∑ i ∈ Finset.range p, S' ^ i = 0 := hsum0
  have hBF : ∀ x y : κ → F, BF G (S' *ᵥ x) (S' *ᵥ y) = BF G x y := by
    intro x y
    have key : S'ᵀ * G.map (Int.cast : ℤ → F) * S' = G.map (Int.cast : ℤ → F) := by
      rw [hS', ← Matrix.transpose_map]
      simp only [hφ]
      rw [← map_mul, ← map_mul, iso]
    unfold BF
    rw [← Matrix.vecMul_transpose S' x, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, key]
  have memD : ∀ y : κ → F, y ∈ dualL F G ↔ ∀ l ∈ LL F κ, ∃ n : ℤ, Algebra.trace ℚ F (BF G y l) = n :=
    fun _ => Iff.rfl
  refine ⟨fun x y => ⟨hBF x y, ?_⟩, fun x => ⟨?_, ?_, ?_, ?_⟩, ?_, prime_not_dvd_of_neg_one_pow_mul_modEq_one hp cong⟩
  · unfold QF
    rw [hBF]
  · rw [iter_eq, hpow, Matrix.one_mulVec]
  · intro hx
    have e : ∑ i ∈ Finset.range p, S' ^ i *ᵥ x = 0 := by
      rw [← Matrix.sum_mulVec, hsum, Matrix.zero_mulVec]
    simp only [pow_mulVec_fix S' hx, Finset.sum_const, Finset.card_range] at e
    rw [← Nat.cast_smul_eq_nsmul F] at e
    have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    exact (smul_eq_zero.mp e).resolve_left hp0
  · rw [memD, memD]
    constructor
    · intro h l hl
      have h' := h _ (mulVec_LL S hl)
      rwa [hBF] at h'
    · intro h l hl
      have h' := h _ (mulVec_LL (S ^ (p - 1)) hl)
      rwa [← hBF, hinv] at h'
  · intro a
    constructor
    · intro h
      have h' := mulVec_aL (S ^ (p - 1)) a h
      rwa [hinv'] at h'
    · intro h
      exact mulVec_aL S a h
  · intro N x hN hcop hx hz
    have hstep : ∀ i : ℕ, S' ^ i *ᵥ x - x ∈ aL κ (N : F) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have e : S' ^ (i + 1) *ᵥ x - x = S' *ᵥ (S' ^ i *ᵥ x - x) + (S' *ᵥ x - x) := by
          rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
          abel
        rw [e]
        exact add_mem (mulVec_aL S _ ih) hz
    have hpx : (p : F) • x ∈ aL κ (N : F) := by
      have h0 : ∑ i ∈ Finset.range p, (S' ^ i *ᵥ x - x) = -((p : F) • x) := by
        rw [Finset.sum_sub_distrib, ← Matrix.sum_mulVec, hsum, Matrix.zero_mulVec, Finset.sum_const,
          Finset.card_range, zero_sub, Nat.cast_smul_eq_nsmul]
      have hs := AddSubgroup.sum_mem (aL κ (N : F)) (t := Finset.range p) (fun i _ => hstep i)
      rw [h0] at hs
      exact neg_mem_iff.mp hs
    have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hNx : (N : F) ^ 2 • x ∈ aL κ (N : F) := by
      simp only [aL, AddSubgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, hy, ?_⟩
      simp only [DistribMulAction.toAddMonoidHom_apply, smul_smul]
      rw [pow_two, mul_assoc, mul_inv_cancel₀ hN0, mul_one]
    obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) ((N : ℤ) ^ 2) := by
      have hc : Nat.Coprime p (N ^ 2) := Nat.Coprime.pow_right 2 hcop.symm
      exact_mod_cast Nat.isCoprime_iff_coprime.mpr hc
    have hx' : x = u • ((p : F) • x) + v • ((N : F) ^ 2 • x) := by
      rw [← Int.cast_smul_eq_zsmul F, ← Int.cast_smul_eq_zsmul F, smul_smul, smul_smul, ← add_smul]
      have e : (u : F) * p + (v : F) * (N : F) ^ 2 = 1 := by exact_mod_cast huv
      rw [e, one_smul]
    rw [hx']
    exact add_mem (zsmul_mem hpx u) (zsmul_mem hNx v)

end GlobalTheory.HilbertThetaSeries.IsoP

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intMatrix_isometry_prime_order_lattice_stability : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → (∀ x y : κ → F, BF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) ((S.map (Int.cast : ℤ → F)) *ᵥ y) = BF G x y ∧ QF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) = QF G x) ∧ (∀ x : κ → F, (fun x => (S.map (Int.cast : ℤ → F)) *ᵥ x)^[p] x = x ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x = x → x = 0) ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ dualL F G ↔ x ∈ dualL F G) ∧ ∀ a : F, ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a ↔ x ∈ aL κ a)) ∧ (∀ (N : ℕ) (x : κ → F), 0 < N → N.Coprime p → x ∈ aL κ (N : F)⁻¹ → (S.map (Int.cast : ℤ → F)) *ᵥ x - x ∈ aL κ (N : F) → x ∈ aL κ (N : F)) ∧ ¬ (p : ℤ) ∣ t := by
  first | exact @GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p | exact GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p | (intros; apply GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p <;> assumption)
