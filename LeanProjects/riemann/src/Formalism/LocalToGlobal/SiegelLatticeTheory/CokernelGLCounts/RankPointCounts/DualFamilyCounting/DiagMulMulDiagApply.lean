import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OneAddFormEqIff

open Matrix Formalism.HermitianLattices.Ext.L3

namespace Formalism.L2.SG.Pf.discriminantGroupCounts

section Diag

variable {A : Type*} [CommRing A] [StarRing A]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {d : m → A}

theorem diag_mul_mul_diag_apply (d : m → A) (T : Matrix m m A) (i j : m) :
    (diagonal d * T * diagonal d) i j = d i * T i j * d j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

def tSet (d : m → A) : Set (Matrix m m A) :=
  {T | Tᴴ = T ∧ diagonal d * T * diagonal d = 0}

def entD (d : m → A) : AddSubgroup (Matrix m m A) where
  carrier := {Y | ∀ i j, d i * Y i j * d j = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun ha hb i j => by
    rw [Matrix.add_apply, mul_add, add_mul, ha i j, hb i j, add_zero]
  neg_mem' := fun ha i j => by
    rw [Matrix.neg_apply, mul_neg, neg_mul, ha i j, neg_zero]

def hermD (d : m → A) : AddSubgroup (Matrix m m A) where
  carrier := {S | Sᴴ = S ∧ ∀ i j, d i * S i j * d j = 0}
  zero_mem' := ⟨conjTranspose_zero, fun _ _ => by simp⟩
  add_mem' := fun ha hb => ⟨by rw [conjTranspose_add, ha.1, hb.1], (entD d).add_mem ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨by rw [conjTranspose_neg, ha.1], (entD d).neg_mem ha.2⟩

theorem mem_tSet_iff (d : m → A) (T : Matrix m m A) : T ∈ tSet d ↔ T ∈ hermD d := by
  show (Tᴴ = T ∧ diagonal d * T * diagonal d = 0) ↔ (Tᴴ = T ∧ ∀ i j, d i * T i j * d j = 0)
  refine and_congr_right fun _ => ?_
  constructor
  · intro h i j
    rw [← diag_mul_mul_diag_apply d T i j, h, Matrix.zero_apply]
  · intro h
    ext i j
    rw [diag_mul_mul_diag_apply, h i j, Matrix.zero_apply]

theorem star_entry (hd : ∀ i, star (d i) = d i) {a : A} {i j : m} (h : d i * a * d j = 0) :
    d j * star a * d i = 0 := by
  have h' := congrArg star h
  simpa [star_mul, hd, mul_assoc] using h'

theorem card_entD [Finite A] (d : m → A) :
    Nat.card (entD d) = ∏ i, ∏ j, Nat.card {a : A // d i * a * d j = 0} := by
  classical
  let e : (entD d) ≃ ((i : m) → (j : m) → {a : A // d i * a * d j = 0}) :=
    { toFun := fun Y i j => ⟨Y.1 i j, (show ∀ i j, d i * Y.1 i j * d j = 0 from Y.2) i j⟩
      invFun := fun f => ⟨fun i j => (f i j).1,
        (show ∀ i j, d i * (f i j).1 * d j = 0 from fun i j => (f i j).2)⟩
      left_inv := fun Y => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr e, Nat.card_pi]
  simp only [Nat.card_pi]

def trD (d : m → A) : entD d →+ Matrix m m A :=
  AddMonoidHom.mk' (fun Y => Y.1 + Y.1ᴴ) (fun a b => by
    simp only [AddSubgroup.coe_add, conjTranspose_add]; abel)

theorem range_trD (hd : ∀ i, star (d i) = d i) {θ e : A} (he : (θ - star θ) * e = 1) :
    (trD d).range = hermD d := by
  have hu : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star, neg_sub]
  have hse : star e = -e := by
    have h1 : star e * star (θ - star θ) = 1 := by rw [← star_mul, he, star_one]
    rw [hu] at h1
    calc star e = star e * ((θ - star θ) * e) := by rw [he, mul_one]
      _ = (star e * (θ - star θ)) * e := by ring
      _ = -e := by
        rw [show star e * (θ - star θ) = -1 by linear_combination -h1]
        ring
  ext S
  rw [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨Y, rfl⟩
    have hY : ∀ i j, d i * Y.1 i j * d j = 0 := Y.2
    show (Y.1 + Y.1ᴴ)ᴴ = Y.1 + Y.1ᴴ ∧ ∀ i j, d i * (Y.1 + Y.1ᴴ) i j * d j = 0
    refine ⟨?_, fun i j => ?_⟩
    · rw [conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    · rw [Matrix.add_apply, Matrix.conjTranspose_apply, mul_add, add_mul, hY i j,
        star_entry hd (hY j i), add_zero]
  · intro hS'
    obtain ⟨hS, hS0⟩ : Sᴴ = S ∧ ∀ i j, d i * S i j * d j = 0 := hS'
    refine ⟨⟨(θ * e) • S, ?_⟩, ?_⟩
    · show ∀ i j, d i * ((θ * e) • S) i j * d j = 0
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul]
      calc d i * (θ * e * S i j) * d j = θ * e * (d i * S i j * d j) := by ring
        _ = 0 := by rw [hS0 i j, mul_zero]
    · show (θ * e) • S + ((θ * e) • S)ᴴ = S
      ext i j
      have hSij : star (S j i) = S i j := by rw [← Matrix.conjTranspose_apply, hS]
      simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
        star_mul, hSij, hse]
      linear_combination (S i j) * he

theorem card_hermD_sq [Finite A] (hd : ∀ i, star (d i) = d i) {θ e : A}
    (he : (θ - star θ) * e = 1) : Nat.card (hermD d) ^ 2 = Nat.card (entD d) := by
  classical
  have hrange := range_trD (d := d) hd he
  have hu : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star, neg_sub]
  have hse : star e = -e := by
    have h1 : star e * star (θ - star θ) = 1 := by rw [← star_mul, he, star_one]
    rw [hu] at h1
    calc star e = star e * ((θ - star θ) * e) := by rw [he, mul_one]
      _ = (star e * (θ - star θ)) * e := by ring
      _ = -e := by
        rw [show star e * (θ - star θ) = -1 by linear_combination -h1]
        ring
  have hk : Nat.card (trD d).ker = Nat.card (hermD d) := by
    symm
    refine Nat.card_congr
      { toFun := fun S => ⟨⟨(θ - star θ) • S.1, ?_⟩, ?_⟩
        invFun := fun Y => ⟨e • Y.1.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · obtain ⟨_, hS0⟩ : S.1ᴴ = S.1 ∧ ∀ i j, d i * S.1 i j * d j = 0 := S.2
      show ∀ i j, d i * ((θ - star θ) • S.1) i j * d j = 0
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul]
      calc d i * ((θ - star θ) * S.1 i j) * d j = (θ - star θ) * (d i * S.1 i j * d j) := by ring
        _ = 0 := by rw [hS0 i j, mul_zero]
    · obtain ⟨hS, _⟩ : S.1ᴴ = S.1 ∧ ∀ i j, d i * S.1 i j * d j = 0 := S.2
      show (θ - star θ) • S.1 + ((θ - star θ) • S.1)ᴴ = 0
      ext i j
      have hSij : star (S.1 j i) = S.1 i j := by rw [← Matrix.conjTranspose_apply, hS]
      simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
        star_mul, hSij, hu, Matrix.zero_apply]
      ring
    · have hY0 : Y.1.1 + Y.1.1ᴴ = 0 := Y.2
      have hY : ∀ i j, d i * Y.1.1 i j * d j = 0 := Y.1.2
      show (e • Y.1.1)ᴴ = e • Y.1.1 ∧ ∀ i j, d i * (e • Y.1.1) i j * d j = 0
      refine ⟨?_, fun i j => ?_⟩
      · ext i j
        have h0 := congrFun (congrFun hY0 i) j
        simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] at h0
        simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul, hse]
        linear_combination (-e) * h0
      · rw [Matrix.smul_apply, smul_eq_mul]
        calc d i * (e * Y.1.1 i j) * d j = e * (d i * Y.1.1 i j * d j) := by ring
          _ = 0 := by rw [hY i j, mul_zero]
    · intro S
      apply Subtype.ext
      show e • (θ - star θ) • S.1 = S.1
      rw [smul_smul, mul_comm, he, one_smul]
    · intro Y
      apply Subtype.ext
      apply Subtype.ext
      show (θ - star θ) • e • Y.1.1 = Y.1.1
      rw [smul_smul, he, one_smul]
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (trD d).ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (trD d)).toEquiv, hrange, hk, sq]

theorem card_ker_mulDiag [Finite A] (d : m → A) :
    Nat.card (AddMonoidHom.mulRight (diagonal d)).ker =
      ∏ _i : m, ∏ j : m, Nat.card {a : A // a * d j = 0} := by
  classical
  let e : (AddMonoidHom.mulRight (diagonal d)).ker ≃ ((i : m) → (j : m) → {a : A // a * d j = 0}) :=
    { toFun := fun Y i j => ⟨Y.1 i j, by
        have h : Y.1 * diagonal d = 0 := Y.2
        have h' := congrFun (congrFun h i) j
        rwa [Matrix.mul_diagonal, Matrix.zero_apply] at h'⟩
      invFun := fun f => ⟨Matrix.of fun i j => (f i j).1, by
        show Matrix.of (fun i j => (f i j).1) * diagonal d = 0
        ext i j
        simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.zero_apply]
        exact (f i j).2⟩
      left_inv := fun Y => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr e, Nat.card_pi]
  simp only [Nat.card_pi]

theorem card_ker_eq_card_hermD [Finite A] (hd : ∀ i, star (d i) = d i) {θ e : A}
    (he : (θ - star θ) * e = 1)
    (hsq : ∀ i j, Nat.card {a : A // d i * a * d j = 0} =
      Nat.card {a : A // a * d i = 0} * Nat.card {a : A // a * d j = 0}) :
    Nat.card (AddMonoidHom.mulRight (diagonal d)).ker = Nat.card (hermD d) := by
  have h1 := card_hermD_sq (d := d) hd he
  rw [card_entD] at h1
  have h2 := card_ker_mulDiag (A := A) d
  have h3 : Nat.card (AddMonoidHom.mulRight (diagonal d)).ker ^ 2 = Nat.card (hermD d) ^ 2 := by
    rw [h1, h2]
    simp only [hsq, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]
    ring
  exact Nat.pow_left_injective (by norm_num) h3

theorem card_kerX_eq [Finite A] (hd : ∀ i, star (d i) = d i) {θ e : A}
    (he : (θ - star θ) * e = 1)
    (hsq : ∀ i j, Nat.card {a : A // d i * a * d j = 0} =
      Nat.card {a : A // a * d i = 0} * Nat.card {a : A // a * d j = 0}) (N : ℕ)
    (hN : ∀ T ∈ tSet d, Nat.card {Y : Matrix m m A // phiH (diagonal d) Y = T} = N) :
    Nat.card {X : Matrix m m A // Xᴴ * diagonal d * X = diagonal d ∧ ∃ Y, X = 1 + Y * diagonal d} =
      N := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  unfold phiH at hN
  have hHs : (diagonal d)ᴴ = diagonal d := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact hd i
  have key : ∀ Y : Matrix m m A, (1 + Y * diagonal d)ᴴ * diagonal d * (1 + Y * diagonal d) =
      diagonal d + diagonal d * (Y + Yᴴ + Yᴴ * diagonal d * Y) * diagonal d := by
    intro Y
    simp only [conjTranspose_add, conjTranspose_one, conjTranspose_mul, hHs]
    noncomm_ring
  have herm : ∀ Y : Matrix m m A,
      (Y + Yᴴ + Yᴴ * diagonal d * Y)ᴴ = Y + Yᴴ + Yᴴ * diagonal d * Y := by
    intro Y
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, hHs]
    noncomm_ring
  have cond : ∀ Y : Matrix m m A,
      (1 + Y * diagonal d)ᴴ * diagonal d * (1 + Y * diagonal d) = diagonal d ↔
        (Y + Yᴴ + Yᴴ * diagonal d * Y) ∈ tSet d := by
    intro Y
    rw [key]
    simp only [tSet, Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨herm Y, ?_⟩
      have h' := congrArg (fun Z => Z - diagonal d) h
      simpa using h'
    · rintro ⟨-, h⟩
      rw [h, add_zero]
  let YS := {Y : Matrix m m A // Y + Yᴴ + Yᴴ * diagonal d * Y ∈ tSet d}
  let XS := {X : Matrix m m A // Xᴴ * diagonal d * X = diagonal d ∧ ∃ Y, X = 1 + Y * diagonal d}
  let KS := (AddMonoidHom.mulRight (diagonal d)).ker
  let Φ : YS → XS := fun Y => ⟨1 + Y.1 * diagonal d, (cond Y.1).2 Y.2, Y.1, rfl⟩
  let sec : XS → YS := fun X => ⟨Classical.choose X.2.2, (cond _).1 (by
    rw [← Classical.choose_spec X.2.2]
    exact X.2.1)⟩
  have hsec : ∀ X : XS, X.1 = 1 + (sec X).1 * diagonal d := fun X => Classical.choose_spec X.2.2
  have hΦ : ∀ (X : XS) (k : KS) (h : ((sec X).1 + k.1) + ((sec X).1 + k.1)ᴴ +
      ((sec X).1 + k.1)ᴴ * diagonal d * ((sec X).1 + k.1) ∈ tSet d), Φ ⟨(sec X).1 + k.1, h⟩ = X := by
    intro X k h
    apply Subtype.ext
    have hk : k.1 * diagonal d = 0 := k.2
    show 1 + ((sec X).1 + k.1) * diagonal d = X.1
    rw [add_mul, hk, add_zero, hsec X]
  let e : YS ≃ XS × KS :=
    { toFun := fun Y => (Φ Y, ⟨Y.1 - (sec (Φ Y)).1, by
        show (Y.1 - (sec (Φ Y)).1) * diagonal d = 0
        have h1 := hsec (Φ Y)
        have h2 : (Φ Y).1 = 1 + Y.1 * diagonal d := rfl
        rw [h2] at h1
        rw [sub_mul]
        have h3 := add_left_cancel h1
        rw [h3, sub_self]⟩)
      invFun := fun p => ⟨(sec p.1).1 + p.2.1, (cond _).1 (by
        have hk : p.2.1 * diagonal d = 0 := p.2.2
        rw [add_mul, hk, add_zero, ← hsec p.1]
        exact p.1.2.1)⟩
      left_inv := fun Y => by
        apply Subtype.ext
        show (sec (Φ Y)).1 + (Y.1 - (sec (Φ Y)).1) = Y.1
        abel
      right_inv := fun p => by
        obtain ⟨X, k⟩ := p
        have hX := hΦ X k
        refine Prod.ext (hX _) ?_
        apply Subtype.ext
        show (sec X).1 + k.1 - (sec (Φ ⟨(sec X).1 + k.1, _⟩)).1 = k.1
        rw [hX]
        abel }
  have hY : Nat.card YS = Nat.card XS * Nat.card KS := by
    rw [Nat.card_congr e, Nat.card_prod]
  let g : YS → tSet d := fun Y => ⟨_, Y.2⟩
  have hfib : ∀ T : tSet d, Nat.card {Y : YS // g Y = T} = N := by
    intro T
    rw [← hN T.1 T.2]
    exact Nat.card_congr
      { toFun := fun Y => ⟨Y.1.1, congrArg Subtype.val Y.2⟩
        invFun := fun Y => ⟨⟨Y.1, by rw [Y.2]; exact T.2⟩, Subtype.ext Y.2⟩
        left_inv := fun Y => rfl
        right_inv := fun Y => rfl }
  have hY2 : Nat.card YS = Nat.card (tSet d) * N := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
    simp only [hfib, Finset.sum_const, smul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card]
  have hT : Nat.card (tSet d) = Nat.card KS := by
    rw [card_ker_eq_card_hermD hd he hsq]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun T => mem_tSet_iff d T))
  have hpos : 0 < Nat.card KS := Nat.card_pos
  rw [hY2, hT, mul_comm (Nat.card KS) N] at hY
  exact (Nat.eq_of_mul_eq_mul_right hpos hY).symm

end Diag

end Formalism.L2.SG.Pf.discriminantGroupCounts
