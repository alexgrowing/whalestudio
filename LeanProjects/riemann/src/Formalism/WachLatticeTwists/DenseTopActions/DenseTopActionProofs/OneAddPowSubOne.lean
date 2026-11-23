import Formalism.WachLatticeTwists.DenseTopActions.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JW

open Matrix Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem one_add_pow_sub_one' {R : Type} [CommRing R] (x : R) (n : ℕ) :
    (1 + x) ^ n - 1 = x * ∑ k ∈ Finset.range n, ((n.choose (k + 1) : ℕ) : R) * x ^ k := by
  rw [add_comm, add_pow, Finset.sum_range_succ', Finset.mul_sum]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem xi : StatXi := by
  intro O A _ _ _ S ι As _ jS πs hπ
  have hx : ∀ i, jS (xOf S.ℓ S.s πs) i = S.X := by
    intro i
    change ((Pi.evalRingHom (fun _ => A) i).comp jS) (xOf S.ℓ S.s πs) = S.X
    rw [S.X_eq, xOf, map_sub, map_pow, map_add, map_one]
    simp [hπ, HidaSetting.ε]
  refine ⟨hx, ?_, ?_, ?_⟩
  · intro i
    have h1 : jS (xiOf S.ℓ S.s πs) i
        = ∑ k ∈ Finset.range S.ℓ, ((S.ℓ.choose (k + 1) : ℕ) : A) * (jS (xOf S.ℓ S.s πs) i) ^ k := by
      change ((Pi.evalRingHom (fun _ => A) i).comp jS) (xiOf S.ℓ S.s πs) = _
      simp only [xiOf, map_sum, map_mul, map_natCast, map_pow]
      rfl
    rw [h1, hx]
    rfl
  · obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow (1 + πs) 1 (S.ℓ ^ (S.s - 1))
    refine ⟨t, ?_⟩
    rw [xOf]
    simpa using ht
  · exact one_add_pow_sub_one' _ _

theorem mul_comm_of_regular {R : Type} [CommRing R] {r : ℕ} (Cm P : Matrix (Fin r) (Fin r) R) (c : R)
    (hc : ∀ a, c * a = 0 → a = 0) (h : Cm * P = c • (1 : Matrix (Fin r) (Fin r) R)) :
    P * Cm = c • (1 : Matrix (Fin r) (Fin r) R) := by
  have hdet : Cm.det * P.det = c ^ r := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hE : (P * Cm - c • (1 : Matrix (Fin r) (Fin r) R)) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self]
  have hE2 : P.det • (P * Cm - c • (1 : Matrix (Fin r) (Fin r) R)) = 0 := by
    have := congrArg (fun M => M * P.adjugate) hE
    simp only [Matrix.zero_mul, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
      Matrix.mul_one] at this
    exact this
  have hE3 : (c ^ r) • (P * Cm - c • (1 : Matrix (Fin r) (Fin r) R)) = 0 := by
    rw [← hdet, mul_smul, hE2, smul_zero]
  have hpow : ∀ (n : ℕ) (a : R), c ^ n * a = 0 → a = 0 := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih => intro a ha; exact hc a (ih _ (by rw [← mul_assoc, ← pow_succ]; exact ha))
  have : P * Cm - c • (1 : Matrix (Fin r) (Fin r) R) = 0 := by
    ext i j
    have := congrFun (congrFun hE3 i) j
    exact hpow r _ (by simpa using this)
  exact sub_eq_zero.mp this

section lc

variable {A : Type} [CommRing A] {ι : Type} {D : Type} [AddCommGroup D] [Module A D]
  {As : Type} [CommRing As]

def lc (jS : As →+* (ι → A)) {r : ℕ} (b : Fin r → ι → D) (c : Fin r → As) : ι → D :=
  ∑ k, jS (c k) • b k

theorem lc_vecMul (jS : As →+* (ι → A)) {r : ℕ} (b : Fin r → ι → D) (v : Fin r → As)
    (Mx : Matrix (Fin r) (Fin r) As) :
    lc jS b (v ᵥ* Mx) = lc jS (fun l => lc jS b (Mx l)) v := by
  simp only [lc, Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum,
    mul_smul]
  exact Finset.sum_comm

theorem lc_smul_family (jS : As →+* (ι → A)) {r : ℕ} (b : Fin r → ι → D) (v : Fin r → As)
    (a : ι → A) : lc jS (fun l => a • b l) v = a • lc jS b v := by
  simp only [lc, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

theorem lc_single (jS : As →+* (ι → A)) {r : ℕ} (b : Fin r → ι → D) (k : Fin r) (a : As) :
    lc jS b (Pi.single k a) = jS a • b k := by
  classical
  rw [lc, Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp

theorem lc_add (jS : As →+* (ι → A)) {r : ℕ} (b : Fin r → ι → D) (c c' : Fin r → As) :
    lc jS b (c + c') = lc jS b c + lc jS b c' := by
  simp [lc, add_smul, Finset.sum_add_distrib]

theorem lc_sub (jS : As →+* (ι → A)) {r : ℕ} (b : Fin r → ι → D) (c c' : Fin r → As) :
    lc jS b (c - c') = lc jS b c - lc jS b c' := by
  simp [lc, sub_smul, Finset.sum_sub_distrib]

theorem lc_smul (jS : As →+* (ι → A)) {r : ℕ} (b : Fin r → ι → D) (a : As) (c : Fin r → As) :
    lc jS b (a • c) = jS a • lc jS b c := by
  simp [lc, mul_smul, Finset.smul_sum]

end lc

section named

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
  {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {W : NData S ι pr D} {ℓ : ℕ} [Fact ℓ.Prime] {As AA WC : Type} [CommRing As] [CommRing AA] [CommRing WC]
  [Algebra ℤ_[ℓ] WC] {jS : As →+* (ι → A)} {jA : As →+* AA} {io : AA →+* WC} {φ : WC →+* WC}
  {Gg : Type} [Group Gg] {H : Subgroup Gg} {act : Gg →* (WC ≃+* WC)} {r : ℕ}
  {ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]}

theorem BasisN.uniq {b : Fin r → ι → D} (hb : BasisN W jS b) {c c' : Fin r → As}
    (h : lc jS b c = lc jS b c') : c = c' := by
  have := hb.ind (c - c') (by
    have := lc_sub jS b c c'
    rw [h, sub_self] at this
    exact this)
  exact sub_eq_zero.mp this

theorem BasisN.coords {b : Fin r → ι → D} (hb : BasisN W jS b) (y : Fin r → ι → D)
    (hy : ∀ k, InN W (y k)) : ∃ Mx : Matrix (Fin r) (Fin r) As, ∀ k, y k = lc jS b (Mx k) := by
  choose c hc using fun k => hb.span (y k) (hy k)
  exact ⟨Matrix.of c, hc⟩

theorem cmp_lc (C : Cmp W jS jA io φ H act ρ) (b : Fin r → ι → D) (c : Fin r → As) :
    C.cmp (lc jS b c) = (fun l => io (jA (c l))) ᵥ* xMat C b := by
  rw [lc, map_sum]
  ext j
  simp [C.smul, Matrix.vecMul, dotProduct, xMat, Finset.sum_apply]

theorem mat_of_coords (C : Cmp W jS jA io φ H act ρ) (b y : Fin r → ι → D)
    (Mx : Matrix (Fin r) (Fin r) As) (h : ∀ k, y k = lc jS b (Mx k)) :
    (Matrix.of fun k j => C.cmp (y k) j) = (Mx.map jA).map io * xMat C b := by
  ext k j
  rw [Matrix.of_apply, h, cmp_lc, Matrix.mul_apply_eq_vecMul]
  rfl

theorem inN_smul (a : ι → A) {x : ι → D} (hx : InN W x) : InN W (a • x) :=
  fun i => (W.N i).smul_mem (a i) (hx i)

end named

end Formalism.RepresentationBoundsCohomology.JW
