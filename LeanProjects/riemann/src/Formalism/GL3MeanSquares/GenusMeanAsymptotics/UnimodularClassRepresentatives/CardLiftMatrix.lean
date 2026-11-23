import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFiberMulCardRange

namespace Formalism.HermitianLattices.Ext.L3.HermitianSublattices

open Matrix

section Abstract

variable {A Z : Type*} [AddCommGroup A] [AddCommGroup Z]

theorem exists_shift (B : AddSubgroup A) (Z' : AddSubgroup Z) (g : A → Z) (p : A → Prop)
    (hφ : ∀ a, p a → g a ∈ Z' → ∃ φ : B →+ Z, (∀ b : B, g (a + b) = g a + φ b) ∧
      ∀ z ∈ Z', ∃ b, φ b = z) (z : Z) (hz : z ∈ Z') :
    ∃ β : A → A, (∀ a, β a ∈ B) ∧ (∀ a, ∀ b ∈ B, β (a + b) = β a) ∧
      ∀ a, p a → g a ∈ Z' → g (a + β a) = g a + z ∧ g (a - β a) = g a - z := by
  classical
  have key : ∀ a', p a' → g a' ∈ Z' → ∀ φ : B →+ Z, (∀ b : B, g (a' + b) = g a' + φ b) →
      ∀ b0 : B, φ b0 = z → ∀ a : A, (a' : A ⧸ B) = a →
      g (a + b0) = g a + z ∧ g (a - b0) = g a - z := by
    intro a' _ _ φ hφ1 b0 hb0 a haa
    have hc : -a' + a ∈ B := QuotientAddGroup.eq.mp haa
    obtain ⟨c, hcdef⟩ : ∃ c : B, (c : A) = -a' + a := ⟨⟨_, hc⟩, rfl⟩
    have ha : a = a' + (c : A) := by rw [hcdef]; abel
    have hga : g a = g a' + φ c := by rw [← hφ1 c, ← ha]
    constructor
    · rw [show a + (b0 : A) = a' + ((c + b0 : B) : A) by rw [AddSubgroup.coe_add, ha]; abel,
        hφ1, map_add, hb0, hga, add_assoc]
    · rw [show a - (b0 : A) = a' + ((c - b0 : B) : A) by rw [AddSubgroup.coe_sub, ha]; abel,
        hφ1, map_sub, hb0, hga, add_sub_assoc]
  let good : A ⧸ B → Prop := fun x => ∃ a' : A, (a' : A ⧸ B) = x ∧ p a' ∧ g a' ∈ Z'
  let β' : A ⧸ B → A := fun x =>
    if h : good x then
      ((((hφ h.choose h.choose_spec.2.1 h.choose_spec.2.2).choose_spec.2 z hz).choose : B) : A)
    else 0
  refine ⟨fun a => β' (a : A ⧸ B), fun a => ?_, fun a b hb => ?_, fun a hpa hga => ?_⟩
  · simp only [β']
    split_ifs
    · exact SetLike.coe_mem _
    · exact B.zero_mem
  · have hq : ((a + b : A) : A ⧸ B) = (a : A ⧸ B) := by
      rw [QuotientAddGroup.eq]
      have h' : -(a + b) + a = -b := by abel
      rw [h']
      exact B.neg_mem hb
    show β' _ = β' _
    rw [hq]
  · have h : good (a : A ⧸ B) := ⟨a, rfl, hpa, hga⟩
    simp only [β', dif_pos h]
    exact key _ h.choose_spec.2.1 h.choose_spec.2.2 _
      (hφ _ h.choose_spec.2.1 h.choose_spec.2.2).choose_spec.1 _
      ((hφ _ h.choose_spec.2.1 h.choose_spec.2.2).choose_spec.2 z hz).choose_spec a
      h.choose_spec.1

theorem card_uniform [Finite A] (B : AddSubgroup A) (Z' : AddSubgroup Z) (g : A → Z) (p : A → Prop)
    (hp : ∀ a, ∀ b ∈ B, (p (a + b) ↔ p a))
    (hφ : ∀ a, p a → g a ∈ Z' → ∃ φ : B →+ Z, (∀ b : B, g (a + b) = g a + φ b) ∧
      ∀ z ∈ Z', ∃ b, φ b = z) :
    Nat.card {a // p a ∧ g a ∈ Z'} = Nat.card {a // p a ∧ g a = 0} * Nat.card Z' := by
  classical
  have hβ : ∀ z : Z', ∃ β : A → A, (∀ a, β a ∈ B) ∧ (∀ a, ∀ b ∈ B, β (a + b) = β a) ∧
      ∀ a, p a → g a ∈ Z' → g (a + β a) = g a + z ∧ g (a - β a) = g a - z :=
    fun z => exists_shift B Z' g p hφ z z.2
  choose β hβB hβc hβg using hβ
  let e : {a // p a ∧ g a = 0} × Z' ≃ {a // p a ∧ g a ∈ Z'} :=
  { toFun := fun x => ⟨x.1.1 + β x.2 x.1.1, by
      obtain ⟨⟨a, hpa, hga⟩, z⟩ := x
      have h0 : g a ∈ Z' := hga ▸ Z'.zero_mem
      refine ⟨(hp a _ (hβB z a)).mpr hpa, ?_⟩
      rw [(hβg z a hpa h0).1, hga, zero_add]
      exact z.2⟩
    invFun := fun t => (⟨t.1 - β ⟨g t.1, t.2.2⟩ t.1, by
      obtain ⟨t, hpt, hgt⟩ := t
      refine ⟨?_, ?_⟩
      · rw [sub_eq_add_neg]
        exact (hp t _ (B.neg_mem (hβB _ t))).mpr hpt
      · rw [(hβg ⟨g t, hgt⟩ t hpt hgt).2]
        exact sub_self _⟩, ⟨g t.1, t.2.2⟩)
    left_inv := by
      rintro ⟨⟨a, hpa, hga⟩, z⟩
      have h0 : g a ∈ Z' := hga ▸ Z'.zero_mem
      have hg : g (a + β z a) = z := by rw [(hβg z a hpa h0).1, hga, zero_add]
      have hw : (⟨g (a + β z a), hg ▸ z.2⟩ : Z') = z := Subtype.ext hg
      refine Prod.ext (Subtype.ext ?_) hw
      show a + β z a - β ⟨g (a + β z a), _⟩ (a + β z a) = a
      rw [hw, hβc z a _ (hβB z a), add_sub_cancel_right]
    right_inv := by
      rintro ⟨t, hpt, hgt⟩
      apply Subtype.ext
      show t - β ⟨g t, hgt⟩ t + β ⟨g t, hgt⟩ (t - β ⟨g t, hgt⟩ t) = t
      rw [sub_eq_add_neg, hβc _ t _ (B.neg_mem (hβB _ t))]
      abel }
  rw [← Nat.card_congr e, Nat.card_prod]

theorem card_preimage [Finite A] (f : A →+ Z) (hf : Function.Surjective f) (T : Z → Prop) :
    Nat.card {a // T (f a)} = Nat.card f.ker * Nat.card {z // T z} := by
  classical
  choose s hs using hf
  let e : {a // T (f a)} ≃ f.ker × {z // T z} :=
  { toFun := fun a => (⟨a.1 - s (f a.1), by rw [AddMonoidHom.mem_ker, map_sub, hs, sub_self]⟩,
      ⟨f a.1, a.2⟩)
    invFun := fun x => ⟨x.1.1 + s x.2.1, by
      rw [map_add, AddMonoidHom.mem_ker.mp x.1.2, hs, zero_add]
      exact x.2.2⟩
    left_inv := fun a => by
      apply Subtype.ext
      show a.1 - s (f a.1) + s (f a.1) = a.1
      exact sub_add_cancel _ _
    right_inv := by
      rintro ⟨⟨k, hk⟩, ⟨z, hz⟩⟩
      have hfk : f (k + s z) = z := by rw [map_add, AddMonoidHom.mem_ker.mp hk, hs, zero_add]
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show k + s z - s (f (k + s z)) = k
        rw [hfk, add_sub_cancel_right]
      · show f (k + s z) = z
        exact hfk }
  rw [Nat.card_congr e, Nat.card_prod]

end Abstract

section Mat

variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]

def entSub (m r : Type*) (J : Ideal A) : AddSubgroup (Matrix m r A) where
  carrier := {Y | ∀ i j, Y i j ∈ J}
  zero_mem' := fun _ _ => J.zero_mem
  add_mem' := fun ha hb i j => J.add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => J.neg_mem (ha i j)

def hermSub (r : Type*) (J : Ideal A) : AddSubgroup (Matrix r r A) where
  carrier := {S | Sᴴ = S ∧ ∀ i j, S i j ∈ J}
  zero_mem' := ⟨conjTranspose_zero, fun _ _ => J.zero_mem⟩
  add_mem' := fun ha hb => ⟨by rw [conjTranspose_add, ha.1, hb.1],
    fun i j => J.add_mem (ha.2 i j) (hb.2 i j)⟩
  neg_mem' := fun ha => ⟨by rw [conjTranspose_neg, ha.1], fun i j => J.neg_mem (ha.2 i j)⟩

theorem mem_entSub {J : Ideal A} {Y : Matrix m r A} : Y ∈ entSub m r J ↔ ∀ i j, Y i j ∈ J := Iff.rfl

theorem mem_hermSub {J : Ideal A} {S : Matrix r r A} :
    S ∈ hermSub r J ↔ Sᴴ = S ∧ ∀ i j, S i j ∈ J := Iff.rfl

theorem card_entSub (J : Ideal A) :
    Nat.card (entSub m r J) = Nat.card J ^ (Fintype.card m * Fintype.card r) := by
  classical
  let e : entSub m r J ≃ (m → r → J) :=
  { toFun := fun Y i j => ⟨Y.1 i j, mem_entSub.mp Y.2 i j⟩
    invFun := fun Y => ⟨fun i j => (Y i j : A), mem_entSub.mpr fun i j => (Y i j).2⟩
    left_inv := fun Y => rfl
    right_inv := fun Y => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := m),
    Nat.card_eq_fintype_card (α := r), ← pow_mul, mul_comm]

theorem star_inv_eq_neg {θ e : A} (he : (θ - star θ) * e = 1) : star e = -e := by
  have h1 : star ((θ - star θ) * e) = 1 := by rw [he, star_one]
  rw [star_mul', star_sub, star_star] at h1
  calc star e = star e * ((θ - star θ) * e) := by rw [he, mul_one]
    _ = -(((star θ - θ) * star e) * e) := by ring
    _ = -e := by rw [h1, one_mul]

def trH (r : Type*) (J : Ideal A) : entSub r r J →+ Matrix r r A :=
  AddMonoidHom.mk' (fun Y => Y.1 + Y.1ᴴ) (fun a b => by
    simp only [AddSubgroup.coe_add, conjTranspose_add]; abel)

theorem range_trH {J : Ideal A} (hJ : ∀ a ∈ J, star a ∈ J) {θ e : A}
    (he : (θ - star θ) * e = 1) : (trH r J).range = hermSub r J := by
  ext S
  rw [AddMonoidHom.mem_range, mem_hermSub]
  constructor
  · rintro ⟨Y, rfl⟩
    have hY := mem_entSub.mp Y.2
    refine ⟨?_, fun i j => ?_⟩
    · show (Y.1 + Y.1ᴴ)ᴴ = Y.1 + Y.1ᴴ
      rw [conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    · show (Y.1 + Y.1ᴴ) i j ∈ J
      rw [Matrix.add_apply, Matrix.conjTranspose_apply]
      exact J.add_mem (hY i j) (hJ _ (hY j i))
  · rintro ⟨hS, hSJ⟩
    have hse := star_inv_eq_neg he
    have hS' : ∀ i j, star (S j i) = S i j := fun i j => by rw [← Matrix.conjTranspose_apply, hS]
    refine ⟨⟨(θ * e) • S, mem_entSub.mpr fun i j => ?_⟩, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact J.mul_mem_left _ (hSJ i j)
    · show (θ * e) • S + ((θ * e) • S)ᴴ = S
      ext i j
      rw [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        star_mul', hS', star_mul', hse]
      linear_combination (S i j) * he

theorem card_hermSub_sq {J : Ideal A} (hJ : ∀ a ∈ J, star a ∈ J) {θ e : A}
    (he : (θ - star θ) * e = 1) : Nat.card (hermSub r J) ^ 2 = Nat.card (entSub r r J) := by
  classical
  have hse := star_inv_eq_neg he
  have hsu : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star, neg_sub]
  have hkerm : ∀ Y : (trH r J).ker, ∀ i j, star (Y.1.1 j i) = -(Y.1.1 i j) := by
    intro Y i j
    have h := congrFun (congrFun (AddMonoidHom.mem_ker.mp Y.2) i) j
    change (Y.1.1 + Y.1.1ᴴ) i j = (0 : Matrix r r A) i j at h
    rw [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] at h
    linear_combination h
  let e1 : (trH r J).ker ≃ hermSub r J :=
  { toFun := fun Y => ⟨(θ - star θ) • Y.1.1, mem_hermSub.mpr ⟨by
        ext i j
        rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul', hsu,
          hkerm]
        ring, fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul]
        exact J.mul_mem_left _ (mem_entSub.mp Y.1.2 i j)⟩⟩
    invFun := fun S => ⟨⟨e • S.1, mem_entSub.mpr fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul]
        exact J.mul_mem_left _ ((mem_hermSub.mp S.2).2 i j)⟩, by
        rw [AddMonoidHom.mem_ker]
        change e • S.1 + (e • S.1)ᴴ = 0
        have hS := (mem_hermSub.mp S.2).1
        have hS' : ∀ i j, star (S.1 j i) = S.1 i j := fun i j => by
          rw [← Matrix.conjTranspose_apply, hS]
        ext i j
        rw [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
          star_mul', hS', hse, Matrix.zero_apply]
        ring⟩
    left_inv := fun Y => by
      apply Subtype.ext
      apply Subtype.ext
      change e • (θ - star θ) • Y.1.1 = Y.1.1
      rw [smul_smul, mul_comm, he, one_smul]
    right_inv := fun S => by
      apply Subtype.ext
      change (θ - star θ) • e • S.1 = S.1
      rw [smul_smul, he, one_smul] }
  have hq := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (trH r J).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (trH r J)).toEquiv,
    range_trH hJ he, Nat.card_congr e1] at hq
  rw [hq, sq]

theorem quad_eq_zero {𝔟 : Ideal A} (h𝔟s : ∀ a ∈ 𝔟, star a ∈ 𝔟) (h𝔟2 : ∀ a ∈ 𝔟, ∀ b ∈ 𝔟, a * b = 0)
    (H : Matrix m m A) {Y : Matrix m r A} (hY : Y ∈ entSub m r 𝔟) : Yᴴ * H * Y = 0 := by
  have hY' := mem_entSub.mp hY
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Matrix.conjTranspose_apply, mul_comm (star _) (H k l), mul_assoc,
    h𝔟2 _ (h𝔟s _ (hY' k i)) _ (hY' l j), mul_zero]

theorem card_lift_matrix [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a)) (𝔟 : Ideal A) (h𝔟s : ∀ a ∈ 𝔟, star a ∈ 𝔟)
    (h𝔟2 : ∀ a ∈ 𝔟, ∀ b ∈ 𝔟, a * b = 0) (H : Matrix m m A) (hH : Hᴴ = H) (T : Matrix r r A)
    (hT : Tᴴ = T) (p' : Matrix m r A' → Prop)
    (hinv : ∀ X Y : Matrix m r A, Y ∈ entSub m r 𝔟 → (p' ((X + Y).map π) ↔ p' (X.map π)))
    (RC : ∀ X : Matrix m r A, p' (X.map π) → (∀ i j, (Xᴴ * H * X - T) i j ∈ RingHom.ker π) →
      ∀ S ∈ hermSub r (RingHom.ker π), ∃ Y ∈ entSub m r 𝔟, Xᴴ * H * Y + Yᴴ * H * X = S) :
    Nat.card {X : Matrix m r A // p' (X.map π) ∧ Xᴴ * H * X = T} *
        Nat.card (hermSub r (RingHom.ker π)) =
      Nat.card (entSub m r (RingHom.ker π)) *
        Nat.card {X' : Matrix m r A' // p' X' ∧ X'ᴴ * (H.map π) * X' = T.map π} := by
  classical
  haveI : Finite (Matrix m r A) := inferInstanceAs (Finite (m → r → A))
  let f : Matrix m r A →+ Matrix m r A' :=
    { toFun := fun X => X.map π
      map_zero' := by ext i j; simp
      map_add' := fun X Y => by ext i j; simp }
  have hfs : Function.Surjective f := fun X' =>
    ⟨X'.map (Function.surjInv hπ), by
      ext i j
      show π (Function.surjInv hπ (X' i j)) = X' i j
      exact Function.surjInv_eq hπ (X' i j)⟩
  have hkerf : f.ker = entSub m r (RingHom.ker π) := by
    ext X
    rw [AddMonoidHom.mem_ker, mem_entSub]
    constructor
    · intro h i j
      have h' := congrFun (congrFun h i) j
      rw [RingHom.mem_ker]
      exact h'
    · intro h
      ext i j
      exact RingHom.mem_ker.mp (h i j)
  have hmap : ∀ X : Matrix m r A, (Xᴴ * H * X).map π = (X.map π)ᴴ * H.map π * X.map π := by
    intro X
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map (⇑π) hπs]
  have hiff : ∀ X : Matrix m r A,
      (p' (X.map π) ∧ Xᴴ * H * X - T ∈ hermSub r (RingHom.ker π)) ↔
        (p' (f X) ∧ (f X)ᴴ * H.map π * f X = T.map π) := by
    intro X
    rw [mem_hermSub]
    have hh : (Xᴴ * H * X - T)ᴴ = Xᴴ * H * X - T := by
      rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH,
        hT, Matrix.mul_assoc]
    have hf : f X = X.map π := rfl
    rw [hf, ← hmap]
    constructor
    · rintro ⟨hp, -, hk⟩
      refine ⟨hp, ?_⟩
      ext i j
      have h' := hk i j
      rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero] at h'
      simp only [Matrix.map_apply]
      exact h'
    · rintro ⟨hp, he'⟩
      refine ⟨hp, hh, fun i j => ?_⟩
      have h' := congrFun (congrFun he' i) j
      rw [Matrix.map_apply, Matrix.map_apply] at h'
      rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, h', sub_self]
  have hφ : ∀ X : Matrix m r A, p' (X.map π) → Xᴴ * H * X - T ∈ hermSub r (RingHom.ker π) →
      ∃ φ : entSub m r 𝔟 →+ Matrix r r A,
        (∀ Y : entSub m r 𝔟, (X + (Y : Matrix m r A))ᴴ * H * (X + (Y : Matrix m r A)) - T =
          Xᴴ * H * X - T + φ Y) ∧
          ∀ S ∈ hermSub r (RingHom.ker π), ∃ Y, φ Y = S := by
    intro X hp hg
    refine ⟨AddMonoidHom.mk' (fun Y => Xᴴ * H * Y.1 + Y.1ᴴ * H * X) (fun Y Z => by
      simp only [AddSubgroup.coe_add, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      abel), fun Y => ?_, fun S hS => ?_⟩
    · have hq := quad_eq_zero h𝔟s h𝔟2 H Y.2
      show _ = _ + (Xᴴ * H * Y.1 + Y.1ᴴ * H * X)
      simp only [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
      rw [hq]
      abel
    · have hk := (mem_hermSub.mp hg).2
      obtain ⟨Y, hY, hYS⟩ := RC X hp (fun i j => by
        have h' := hk i j
        rwa [Matrix.sub_apply] at h' ⊢) S hS
      exact ⟨⟨Y, hY⟩, hYS⟩
  have hu := card_uniform (entSub m r 𝔟) (hermSub r (RingHom.ker π))
    (fun X => Xᴴ * H * X - T) (fun X => p' (X.map π)) (fun X Y hY => hinv X Y hY) hφ
  have hpre := card_preimage f hfs (fun X' => p' X' ∧ X'ᴴ * H.map π * X' = T.map π)
  beta_reduce at hu hpre
  have e1 : Nat.card {X : Matrix m r A // p' (X.map π) ∧ Xᴴ * H * X = T} =
      Nat.card {a : Matrix m r A // p' (a.map π) ∧ aᴴ * H * a - T = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun X => by rw [sub_eq_zero])
  have e2 : Nat.card {a : Matrix m r A //
        p' (a.map π) ∧ aᴴ * H * a - T ∈ hermSub r (RingHom.ker π)} =
      Nat.card {a : Matrix m r A // p' (f a) ∧ (f a)ᴴ * H.map π * f a = T.map π} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [e1, ← hu, e2, hpre, hkerf]

end Mat

end Formalism.HermitianLattices.Ext.L3.HermitianSublattices
