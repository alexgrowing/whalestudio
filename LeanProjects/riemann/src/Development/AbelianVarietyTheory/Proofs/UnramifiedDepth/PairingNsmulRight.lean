import Mathlib
import ReciprocityTheory.DualLattices.EvenTwoEvaluationSign
import ReciprocityTheory.DualLattices.IsPairingValueAddRight

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

noncomputable section

namespace GlobalTheory

namespace SignChar

variable {R₀ : Type} [CommRing R₀]

section Pairing

variable (B : BX R₀) {R : LAlg R₀}

lemma pairing_zero_left (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h2 := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h2
  have h3 : z * z = z := B.pairing_unique N 0 y _ _ h2 hz
  have h4 : z = 1 := mul_eq_left.1 h3
  rwa [h4] at hz

lemma pairing_zero_right (N : ℕ) (x : B.G R) (hx : N • x = 0) : B.IsPairing N x 0 1 := by
  have h := B.pairing_sw N 0 x 1 (pairing_zero_left B N x hx)
  rwa [inv_one] at h

lemma pairing_nsmul_left (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (n : ℕ) : B.IsPairing N (n • x) y (z ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact pairing_zero_left B N y h.2.1
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_left N _ _ _ _ _ ih h

lemma pairing_nsmul_right (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (n : ℕ) : B.IsPairing N x (n • y) (z ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact pairing_zero_right B N x h.1
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_right N _ _ _ _ _ ih h

lemma pairing_sum_left {ι : Type} (s : Finset ι) (N : ℕ) (x : ι → B.G R) (y : B.G R)
    (z : ι → (R : Type)ˣ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (z i)) :
    B.IsPairing N (∑ i ∈ s, x i) y (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact pairing_zero_left B N y hy
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_left N _ _ _ _ _ (h a) ih

lemma pairing_sum_right {ι : Type} (s : Finset ι) (N : ℕ) (x : B.G R) (y : ι → B.G R)
    (z : ι → (R : Type)ˣ) (hx : N • x = 0) (h : ∀ i, B.IsPairing N x (y i) (z i)) :
    B.IsPairing N x (∑ i ∈ s, y i) (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact pairing_zero_right B N x hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_right N _ _ _ _ _ (h a) ih

end Pairing

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

lemma ptMap_spec (D : Dat p g B Tw Dt Oe σ cp) (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = LHom.id Tw.O ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = ptOf B D.L.τ t := by
  have h := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))
  exact ⟨h.1, h.2.1⟩

lemma toZMod_eq_of_q (a : ℤ_[p]) (k : ℕ)
    (h : (Tw.q 0).1 (algebraMap ℤ_[p] (Tw.O : Type) a) = k) :
    PadicInt.toZMod a = (k : ZMod p) := by
  have h1 : ¬ IsUnit (a - k) := by
    intro hu
    have h2 := (hu.map (algebraMap ℤ_[p] (Tw.O : Type))).map (Tw.q 0).1
    rw [map_sub, map_sub, h, map_natCast, map_natCast, sub_self] at h2
    exact not_isUnit_zero h2
  have h3 : a - k ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod]
    exact h1
  rw [RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h3
  exact h3

lemma pairing_ptOf (D : Dat p g B Tw Dt Oe σ cp) (s t : TT p g) :
    ∃ n : ℕ, (n : ZMod p) = PadicInt.toZMod (pair p g D.H.E s t) ∧
      B.IsPairing p (ptOf B D.L.τ (red p g s)) (ptOf B D.L.τ (red p g t)) (Tw.ζ 0 ^ n) := by
  choose k hk hpair using fun i j => D.L.E_spec i j 0
  simp only [zero_add, pow_one] at hpair
  refine ⟨∑ i, (∑ j, k i j * (red p g t j).val) * (red p g s i).val, ?_, ?_⟩
  · simp only [pair, dotProduct, mulVec, map_sum, map_mul, Nat.cast_sum, Nat.cast_mul,
      ZMod.natCast_zmod_val, red]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [toZMod_eq_of_q _ _ (hk i j)]
  · rw [← Finset.prod_pow_eq_pow_sum]
    refine pairing_sum_left B _ p _ _ _ (D.pt_p _) fun i => ?_
    rw [pow_mul]
    refine pairing_nsmul_left B p _ _ _ ?_ _
    rw [← Finset.prod_pow_eq_pow_sum]
    refine pairing_sum_right B _ p _ _ _ (hpair i i).1 fun j => ?_
    rw [pow_mul]
    exact pairing_nsmul_right B p _ _ _ (hpair i j) _

end SignChar

theorem signChar_mem_evImg :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvenTwoEvaluationSign D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ _ _ hp s
  have hex : ∀ i, ∃ z, B.IsPairing p (B.map (D.fin.sO i) (ptOf B D.L.τ (red p g s)))
      (D.fin.y i) z := fun i =>
    B.pairing_exists p _ _ (by rw [← map_nsmul, D.pt_p, map_zero]) (D.fin.y_p i)
  choose e he using hex
  refine ⟨D.evAll C fun i => (e i : (D.fin.AAx i : Type)), Submodule.subset_span ⟨_, rfl⟩,
    fun t => ?_⟩
  obtain ⟨h1, h2⟩ := SignChar.ptMap_spec D (red p g t)
  have h3 := B.pairing_map (D.ptMap (red p g t)) p _ _ _ (he (D.ptIdx (red p g t)))
  rw [← B.map_comp, h1, B.map_id, h2] at h3
  obtain ⟨n, hn, h4⟩ := SignChar.pairing_ptOf D s t
  have h5 := congrArg Units.val (B.pairing_unique p _ _ _ _ h3 h4)
  rw [Units.val_pow_eq_pow_val, D.zeta0 hp, Units.coe_map] at h5
  have h6 : (D.ptMap (red p g t)).1 (e (D.ptIdx (red p g t)) : (D.fin.AAx _ : Type)) =
      (-1) ^ n := h5
  have h7 : (PadicInt.toZMod (pair p g D.H.E s t)).val % 2 = n % 2 := by
    rw [← hn, ZMod.val_natCast, ← hp, Nat.mod_mod]
  unfold Dat.evAll
  rw [h6, map_pow, map_neg, map_one, neg_one_pow_eq_pow_mod_two n, ← h7,
    ← neg_one_pow_eq_pow_mod_two]

end GlobalTheory
