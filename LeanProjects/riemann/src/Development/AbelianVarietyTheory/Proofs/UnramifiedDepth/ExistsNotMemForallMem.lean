import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEig

noncomputable section

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Matrix

namespace GlobalTheory.PlaceProj

section Val

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_neg {a : C} (ha : V.MM a) : V.MM (-a) := by
  unfold VF.MM at *; rwa [V.v.map_neg]

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]; exact mm_add ha (mm_neg hb)

theorem mm_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM VF.Ge at *
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left (by simpa using ha))

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem ge_of_mm {a : C} (ha : V.MM a) : V.Ge 0 a := by
  unfold VF.MM VF.Ge at *; simpa using ha.le

theorem mm_of_ge_one {a : C} (ha : V.Ge 1 a) : V.MM a := by
  unfold VF.MM VF.Ge at *
  exact lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)) ha

theorem mm_l : V.MM (V.l : C) := mm_of_ge_one VF.ge_l

theorem mm_l_mul {a : C} (ha : V.Ge 0 a) : V.MM ((V.l : C) * a) := by
  rw [mul_comm]; exact mm_mul ha mm_l

theorem not_mm_one : ¬ V.MM (1 : C) := by simp [VF.MM]

theorem v_eq_zero_of_not_mm {a : C} (ha : V.Ge 0 a) (h : ¬ V.MM a) : V.v a = 0 := by
  unfold VF.MM VF.Ge at *
  exact le_antisymm (not_lt.1 h) (by simpa using ha)

theorem not_mm_of_v {a : C} (h : V.v a = 0) : ¬ V.MM a := by
  unfold VF.MM; rw [h]; exact lt_irrefl _

theorem v_eq_zero_of_mm_sub_one {a : C} (h : V.MM (a - 1)) : V.v a = 0 := by
  apply v_eq_zero_of_not_mm
  · simpa using (ge_of_mm h).add VF.Ge.one
  · intro h'
    apply not_mm_one (V := V)
    simpa using mm_sub h' h

theorem v_eq_zero_of_mm_add_one {a : C} (h : V.MM (a + 1)) : V.v a = 0 := by
  rw [← V.v.map_neg]
  apply v_eq_zero_of_mm_sub_one
  have := mm_neg h
  convert this using 1; ring

theorem ge_of_unit_mul {w : ℝ} {u a : C} (hu : V.v u = 0) (h : V.Ge w (u * a)) : V.Ge w a := by
  unfold VF.Ge at *
  rwa [V.v.map_mul, hu, zero_add] at h

theorem mm_of_unit_mul {u a : C} (hu : V.v u = 0) (h : V.MM (u * a)) : V.MM a := by
  unfold VF.MM at *
  rwa [V.v.map_mul, hu, zero_add] at h

theorem mm_pow_sub {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (h : V.MM (a - b)) (n : ℕ) :
    V.MM (a ^ n - b ^ n) := by
  induction n with
  | zero => simpa using mm_zero
  | succ n ih =>
    have := mm_add (mm_mul ha ih) (mm_mul (hb.pow n) h)
    convert this using 1; ring

theorem eq_zero_of_forall_ge {x : C} (h : ∀ N : ℕ, V.Ge N x) : x = 0 := by
  rw [← V.v.top_iff]
  unfold VF.Ge at h
  induction hv : V.v x using WithTop.recTopCoe with
  | top => rfl
  | coe t =>
    exfalso
    obtain ⟨N, hN⟩ := exists_nat_gt t
    have := h N
    rw [hv] at this
    have h2 : (N : ℝ) ≤ t := by exact_mod_cast this
    linarith

theorem exists_ge (x : C) : ∃ w : ℝ, V.Ge w x := by
  unfold VF.Ge
  induction hv : V.v x using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

theorem exists_ge_vec {n : Type} [Fintype n] (v : n → C) : ∃ w : ℝ, ∀ i, V.Ge w (v i) := by
  choose w hw using fun i => exists_ge (V := V) (v i)
  obtain ⟨b, hb⟩ := (Set.finite_range w).bddBelow
  exact ⟨b, fun i => (hw i).mono (hb ⟨i, rfl⟩)⟩

theorem ge_l_pow (n : ℕ) : V.Ge n ((V.l : C) ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one
  | succ n ih => rw [pow_succ]; push_cast; exact ih.mul VF.ge_l

theorem mulVec_ge {n : Type} [Fintype n] {X : Matrix n n C} (hX : ∀ i j, V.Ge 0 (X i j)) {w : ℝ} {v : n → C}
    (hv : ∀ i, V.Ge w (v i)) (i : n) : V.Ge w ((X *ᵥ v) i) :=
  VF.Ge.sum fun j _ => (hX i j).mul_int (hv j)

theorem twisted_der_eq_zero {O : Type} [CommRing O] (χ e : O →+* C) (hχ : ∀ x, V.Ge 0 (χ x))
    (he : ∀ x, V.Ge 0 (e x)) (hce : ∀ x, V.MM (χ x - e x)) (ε : O) (hε : ∃ y, ε * ε - ε = (V.l : O) * y)
    (hε1 : V.MM (e ε - 1)) (k : ℕ) (hk : k ≠ 0) (hfr : ∀ x, ∃ y, ε * (x ^ V.l ^ k - x) = (V.l : O) * y)
    (D : O →+ C) (hD : ∀ x y, D (x * y) = χ x * D y + D x * e y) (w : ℝ) (hw : ∀ x, V.Ge w (D x)) (x : O) :
    D x = 0 := by
  have hl : ∀ y, D ((V.l : O) * y) = (V.l : C) * D y := fun y => by
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  have hχ1 : V.MM (χ ε - 1) := by simpa using mm_add (hce ε) hε1
  have hpow : ∀ x (n : ℕ), ∃ S, D (x ^ (n + 1)) = S * D x ∧ V.MM (S - ((n + 1 : ℕ) : C) * e x ^ n) := by
    intro x n
    induction n with
    | zero => exact ⟨1, by simp, by simpa using mm_zero⟩
    | succ n ih =>
      obtain ⟨S, h1, h2⟩ := ih
      refine ⟨χ x * S + e x ^ (n + 1), ?_, ?_⟩
      · rw [pow_succ' x (n + 1), hD, h1, map_pow]; ring
      · have := mm_add (mm_mul (hχ x) h2) (mm_mul ((VF.ge_natCast (n + 1)).mul_int ((he x).pow n)) (hce x))
        convert this using 1; push_cast; ring
  have step : ∀ w : ℝ, (∀ x, V.Ge w (D x)) → ∀ x, V.Ge (1 + w) (D x) := by
    intro w hw x
    have h1 : V.Ge (1 + w) (D ε) := by
      obtain ⟨y, hy⟩ := hε
      have h := congrArg D hy
      rw [map_sub, hD, hl] at h
      apply ge_of_unit_mul (u := χ ε + e ε - 1)
      · apply v_eq_zero_of_mm_sub_one
        convert mm_add hχ1 hε1 using 1; ring
      · convert (hw y).l_mul using 1
        rw [← h]; ring
    obtain ⟨y, hy⟩ := hfr x
    have h := congrArg D hy
    rw [hD, hl] at h
    have h2 : V.Ge (1 + w) (D (x ^ V.l ^ k - x)) := by
      apply ge_of_unit_mul (v_eq_zero_of_mm_sub_one hχ1)
      convert ((hw y).l_mul).sub ((he (x ^ V.l ^ k - x)).mul_int h1) using 1
      rw [← h]; ring
    obtain ⟨m, hm⟩ : ∃ m, V.l ^ k = m + 1 := ⟨V.l ^ k - 1, by
      have := pow_pos V.l_prime.pos k; omega⟩
    obtain ⟨S, hS1, hS2⟩ := hpow x m
    rw [map_sub, hm, hS1] at h2
    have hS : V.MM S := by
      rw [← hm] at hS2
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have := mm_add hS2 (mm_l_mul (((VF.ge_natCast V.l).pow k').mul_int ((he x).pow m)))
      convert this using 1; push_cast; rw [pow_succ]; ring
    apply ge_of_unit_mul (u := S - 1)
    · apply v_eq_zero_of_mm_add_one; simpa using hS
    · convert h2 using 1; ring
  have hall : ∀ n : ℕ, ∀ x, V.Ge (n + w) (D x) := by
    intro n
    induction n with
    | zero => simpa using hw
    | succ n ih => intro x; convert step _ ih x using 1; push_cast; ring
  apply eq_zero_of_forall_ge (V := V)
  intro N
  obtain ⟨n, hn⟩ := exists_nat_ge (N - w)
  exact (hall n x).mono (by linarith)

end Val

theorem exists_not_mem_forall_mem {C E ι : Type} [Field C] [AddCommGroup E] [Module C E] [FiniteDimensional C E]
    (N : ι → Module.End C E) (hc : ∀ i j, Commute (N i) (N j)) (W K : Submodule C E)
    (hW : ∀ i, ∀ v ∈ W, N i v ∈ W) (hn : ∀ i, ∀ v ∈ W, ∃ k : ℕ, (N i ^ k) v = 0) (hWK : ¬ W ≤ K) :
    ∃ v ∈ W, v ∉ K ∧ ∀ i, N i v ∈ K := by
  obtain ⟨Z, ⟨hZW, hZi, hZK⟩, hmin⟩ := (IsArtinian.set_has_minimal (R := C) (M := E)
    {Z | Z ≤ W ∧ (∀ i, ∀ v ∈ Z, N i v ∈ Z) ∧ ¬ Z ≤ K} ⟨W, le_rfl, hW, hWK⟩)
  obtain ⟨v, hvZ, hvK⟩ := SetLike.not_le_iff_exists.1 hZK
  refine ⟨v, hZW hvZ, hvK, fun i => ?_⟩
  by_contra hi
  have hle : Z.map (N i) ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩; exact hZi i z hz
  have heq : Z.map (N i) = Z := by
    by_contra hne
    refine hmin (Z.map (N i)) ⟨hle.trans hZW, ?_, fun h => hi (h ⟨v, hvZ, rfl⟩)⟩ (lt_of_le_of_ne hle hne)
    rintro j _ ⟨z, hz, rfl⟩
    refine ⟨N j z, hZi j z hz, ?_⟩
    exact LinearMap.congr_fun (hc i j).eq z
  have hsurj : Function.Surjective ((N i).restrict (hZi i)) := by
    rintro ⟨z, hz⟩
    rw [← heq] at hz
    obtain ⟨z', hz', h⟩ := hz
    exact ⟨⟨z', hz'⟩, Subtype.ext h⟩
  have hinj := LinearMap.injective_iff_surjective.2 hsurj
  obtain ⟨k, hk⟩ := hn i v (hZW hvZ)
  have h0 : (((N i).restrict (hZi i)) ^ k) ⟨v, hvZ⟩ = 0 := by
    rw [Module.End.pow_restrict]
    exact Subtype.ext hk
  have hinj' : Function.Injective (((N i).restrict (hZi i)) ^ k) := by
    rw [Module.End.coe_pow]; exact hinj.iterate k
  have := hinj' (h0.trans (map_zero _).symm)
  apply hvK
  have hv0 : v = 0 := congrArg Subtype.val this
  rw [hv0]; exact K.zero_mem

theorem card_hom_le {M k ι : Type} [CommRing M] [CommRing k] [IsDomain k] [Finite ι] (l d : ℕ) (hl : l.Prime)
    (hd : d ≠ 0) [CharP k l] (j : M →+* k) (hj : Function.Injective j) (hq : ∀ x, j x ^ l ^ d = j x)
    (f : ι → M →+* k) (hf : Function.Injective f) : Nat.card ι ≤ d := by
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : CharP M l := j.charP hj l
  letI : Algebra (ZMod l) M := ZMod.algebra M l
  letI : Algebra (ZMod l) k := ZMod.algebra k l
  have hq1 : 1 < l ^ d := Nat.one_lt_pow hd hl.one_lt
  obtain ⟨q, hqd⟩ : ∃ q, q = l ^ d := ⟨_, rfl⟩
  rw [← hqd] at hq hq1
  have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial k).natDegree = q := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hq1]
  have hp : (Polynomial.X ^ q - Polynomial.X : Polynomial k) ≠ 0 := by
    intro h; rw [h] at hdeg; simp at hdeg; omega
  let r : M → (Polynomial.X ^ q - Polynomial.X : Polynomial k).roots.toFinset := fun m => ⟨j m, by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    simp [hq]⟩
  have hr : Function.Injective r := fun a b h => hj (congrArg Subtype.val h)
  haveI : Finite M := Finite.of_injective r hr
  have hcard : Nat.card M ≤ q := by
    refine (Nat.card_le_card_of_injective r hr).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans hdeg.le)
  have hfr : Module.finrank (ZMod l) M ≤ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod, hqd] at hcard
    exact (Nat.pow_le_pow_iff_right hl.one_lt).1 hcard
  let F : ι → M →ₐ[ZMod l] k := fun o =>
    { f o with
      commutes' := fun c => RingHom.congr_fun (Subsingleton.elim
        ((f o).comp (algebraMap (ZMod l) M)) (algebraMap (ZMod l) k)) c }
  have hF : Function.Injective F := by
    intro a b h
    apply hf
    ext x
    exact AlgHom.congr_fun h x
  haveI : Finite (M →ₐ[ZMod l] k) := inferInstance
  exact (Nat.card_le_card_of_injective F hF).trans ((card_algHom_le_finrank (ZMod l) M k).trans hfr)

theorem hom_eq_of_ker {O k ι : Type} [CommRing O] [CommRing k] [IsDomain k] [Finite ι] (l : ℕ) (hl : l.Prime)
    [CharP k l] (e : ι → O →+* k) (he : Function.Injective e) (i0 : ι)
    (hq : ∀ x, e i0 x ^ l ^ Nat.card ι = e i0 x) (hk : ∀ i x, e i0 x = 0 → e i x = 0)
    (ψ : O →+* k) (hψ : ∀ x, e i0 x = 0 → ψ x = 0) : ∃ i, ψ = e i := by
  classical
  by_contra hne
  push_neg at hne
  haveI : Nonempty ι := ⟨i0⟩
  let f : Option ι → O →+* k := fun o => o.elim ψ e
  have hf : Function.Injective f := by
    rintro (_ | a) (_ | b) h
    · rfl
    · exact absurd h (hne b)
    · exact absurd h.symm (hne a)
    · exact congrArg some (he h)
  have hfk : ∀ o, ∀ x ∈ RingHom.ker (e i0), f o x = 0 := by
    rintro (_ | a) x hx
    · exact hψ x hx
    · exact hk a x hx
  have := card_hom_le l (Nat.card ι) hl Nat.card_pos.ne' (RingHom.kerLift (e i0)) (RingHom.kerLift_injective _)
    (fun m => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [RingHom.kerLift_mk, hq])
    (fun o => Ideal.Quotient.lift _ (f o) (hfk o)) (fun a b h => hf (by
      ext x
      exact RingHom.congr_fun h (Ideal.Quotient.mk _ x)))
  rw [Finite.card_option] at this
  omega

section Place

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {d : ℕ} [NeZero d]

def intRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

def maxId (V : VF C) : Ideal (intRing V) where
  carrier := {x | V.MM x}
  add_mem' := fun ha hb => mm_add ha hb
  zero_mem' := mm_zero
  smul_mem' := fun c _ hx => mm_mul c.2 hx

instance maxId_isPrime (V : VF C) : (maxId V).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]; exact not_mm_one
  mem_or_mem' := by
    intro x y h
    by_cases hx : V.MM x
    · exact Or.inl hx
    · exact Or.inr (mm_of_unit_mul (v_eq_zero_of_not_mm x.2 hx) h)

def red (ψ : O →+* C) (hψ : ∀ x, V.Ge 0 (ψ x)) : O →+* intRing V ⧸ maxId V :=
  (Ideal.Quotient.mk _).comp (ψ.codRestrict (intRing V) hψ)

theorem red_eq {ψ φ : O →+* C} (hψ : ∀ x, V.Ge 0 (ψ x)) (hφ : ∀ x, V.Ge 0 (φ x)) (x y : O) :
    red ψ hψ x = red φ hφ y ↔ V.MM (ψ x - φ y) := Ideal.Quotient.eq

theorem red_eq_zero {ψ : O →+* C} (hψ : ∀ x, V.Ge 0 (ψ x)) (x : O) :
    red ψ hψ x = 0 ↔ V.MM (ψ x) := Ideal.Quotient.eq_zero_iff_mem

theorem frob_iter (em : ZMod d → O →+* C) (hint : ∀ a x, V.Ge 0 (em a x))
    (hfr : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) (a : ZMod d) (x : O) (k : ℕ) :
    V.MM (em (a + k) x - em a x ^ V.l ^ k) := by
  induction k with
  | zero => simpa using mm_zero
  | succ k ih =>
    have := mm_add (hfr (a + k) x) (mm_pow_sub (hint _ _) ((hint _ _).pow _) ih V.l)
    convert this using 1
    push_cast
    rw [pow_succ, pow_mul, add_assoc]; ring

theorem eq_em_of_not_mm (em : ZMod d → O →+* C) (hint : ∀ a x, V.Ge 0 (em a x))
    (hfr : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l))
    (hsep : ∀ a a', a ≠ a' → ∃ x, V.v (em a x - em a' x) = 0) (ε : O) (hε : ∃ y, ε * ε - ε = (V.l : O) * y)
    (hε1 : ∀ a, V.MM (em a ε - 1)) (hεP : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y)
    (ψ : O →+* C) (hψ : ∀ x, V.Ge 0 (ψ x)) (h : ¬ V.MM (ψ ε)) : ∃ a, ψ = em a := by
  have hu := v_eq_zero_of_not_mm (hψ ε) h
  have hq : ∀ a x, V.MM (em a (x ^ V.l ^ d - x)) := fun a x => by
    have := mm_neg (frob_iter em hint hfr a x d)
    simpa using this
  have hall : ∀ x, V.MM (em 0 x) → ∀ a, V.MM (em a x) := fun x hx a => by
    have h1 := frob_iter em hint hfr 0 x a.val
    rw [zero_add, ZMod.natCast_zmod_val] at h1
    obtain ⟨m, hm⟩ : ∃ m, V.l ^ a.val = m + 1 := ⟨V.l ^ a.val - 1, by
      have := pow_pos V.l_prime.pos a.val; omega⟩
    rw [hm] at h1
    have := mm_add h1 (mm_mul ((hint 0 x).pow m) hx)
    convert this using 1; ring
  haveI : CharP (intRing V ⧸ maxId V) V.l := by
    rw [CharP.charP_iff_prime_eq_zero V.l_prime]
    rw [← map_natCast (Ideal.Quotient.mk (maxId V)), Ideal.Quotient.eq_zero_iff_mem]
    show V.MM _
    simpa using mm_l
  obtain ⟨a, ha⟩ := hom_eq_of_ker V.l V.l_prime (fun a => red (em a) (hint a)) (fun a a' haa => by
      by_contra hne
      obtain ⟨x, hx⟩ := hsep a a' hne
      exact not_mm_of_v hx ((red_eq _ _ _ _).1 (RingHom.congr_fun haa x))) 0
    (fun x => by
      rw [Nat.card_zmod, ← map_pow, red_eq]
      simpa using hq 0 x)
    (fun a x hx => (red_eq_zero _ _).2 (hall x ((red_eq_zero _ _).1 hx) a)) (red ψ hψ)
    (fun x hx => by
      rw [red_eq_zero] at hx ⊢
      obtain ⟨y, hy⟩ := hεP x (hall x hx)
      apply mm_of_unit_mul hu
      rw [← map_mul, hy, map_mul, map_natCast]
      exact mm_l_mul (hψ y))
  refine ⟨a, RingHom.ext fun x => sub_eq_zero.1 ?_⟩
  have hc : ∀ x, V.MM (ψ x - em a x) := fun x => (red_eq _ _ _ _).1 (RingHom.congr_fun ha x)
  exact twisted_der_eq_zero ψ (em a) hψ (hint a) hc ε hε (hε1 a) d (NeZero.ne d)
    (fun x => hεP _ fun a => hq a x) (ψ.toAddMonoidHom - (em a).toAddMonoidHom)
    (fun x y => by simp; ring) 0 (fun x => ge_of_mm (hc x)) x

end Place

theorem exists_idem_seq {O : Type} [CommRing O] (l ε : O) (hε : ∃ y, ε * ε - ε = l * y) :
    ∃ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = l ^ n * y) ∧ (∀ n, ∃ y, a n * a n - a n = l ^ n * y) ∧
      ∀ n, ∃ y, a n - ε = l * y := by
  let a : ℕ → O := fun n => (fun t => 3 * t ^ 2 - 2 * t ^ 3)^[n] ε
  have hs : ∀ n, a (n + 1) = 3 * a n ^ 2 - 2 * a n ^ 3 := fun n => Function.iterate_succ_apply' _ _ _
  have h1 : ∀ n, ∃ y, a n * a n - a n = l ^ (n + 1) * y := by
    intro n
    induction n with
    | zero => simpa [a] using hε
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      refine ⟨l ^ n * y ^ 2 * (4 * a n ^ 2 - 4 * a n - 3), ?_⟩
      have : a (n + 1) * a (n + 1) - a (n + 1) = (a n * a n - a n) ^ 2 * (4 * a n ^ 2 - 4 * a n - 3) := by
        rw [hs]; ring
      rw [this, hy]; ring
  have h2 : ∀ n, ∃ y, a (n + 1) - a n = l ^ (n + 1) * y := fun n => by
    obtain ⟨y, hy⟩ := h1 n
    refine ⟨y * (1 - 2 * a n), ?_⟩
    rw [← mul_assoc, ← hy, hs]; ring
  refine ⟨a, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · obtain ⟨y, hy⟩ := h2 n
    exact ⟨l * y, by rw [hy]; ring⟩
  · obtain ⟨y, hy⟩ := h1 n
    exact ⟨l * y, by rw [hy]; ring⟩
  · induction n with
    | zero => exact ⟨0, by simp [a]⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z, hz⟩ := h2 n
      exact ⟨y + l ^ n * z, by linear_combination hy + hz⟩

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.LinEig in

theorem exists_linHom {C : Type} [Field C] {O : Type} [CommRing O] {dd : ℕ} (G : FGLaw C dd) (A : OAct O G) :
    ∃ ρ : O →+* Matrix (Fin dd) (Fin dd) C,
      (∀ a i j, ρ a i j = MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (A.act a i)) ∧
      ∀ a v, linAct (A.act a) v = ρ a *ᵥ v := by
  let f : O → Matrix (Fin dd) (Fin dd) C := fun a =>
    Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (A.act a i)
  have hadd : ∀ a b, f (a + b) = f a + f b := by
    intro a b
    ext i j
    simp only [f, Matrix.of_apply, Matrix.add_apply, A.add_act, FGLaw.add, addOf, ev]
    rw [coeff_single_subst' _ (by rintro ⟨k, l⟩; fin_cases k <;> simp [A.const])]
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, law_coeff]
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    ext i j
    simp only [f, Matrix.of_apply, Matrix.mul_apply, A.mul_act, comp1, ev]
    rw [coeff_single_subst' _ (by rintro ⟨k, l⟩; fin_cases k; simp [A.const])]
    simp [Fintype.sum_prod_type]
  have hone : f 1 = 1 := by
    ext i j
    simp only [f, Matrix.of_apply, A.one_act, pt, MvPowerSeries.coeff_X, Matrix.one_apply]
    simp [Finsupp.single_left_inj, eq_comm]
  exact ⟨RingHom.mk' ⟨⟨f, hone⟩, hmul⟩ hadd, fun _ _ _ => rfl, fun _ _ => rfl⟩

section Limit

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

def IsLim (V : VF C) (ρ : O →+* Matrix n n C) (a : ℕ → O) (M : Matrix n n C) : Prop :=
  ∀ (N : ℕ) (v : n → C) i, ∃ m0, ∀ m ≥ m0, V.Ge N ((M *ᵥ v) i - (ρ (a m) *ᵥ v) i)

variable {ρ : O →+* Matrix n n C} {a : ℕ → O} {M : Matrix n n C}

theorem IsLim.ev (h : IsLim V ρ a M) (N : ℕ) (v : n → C) :
    ∀ᶠ m in Filter.atTop, ∀ i, V.Ge N ((M *ᵥ v - ρ (a m) *ᵥ v) i) :=
  Filter.eventually_all.2 fun i => Filter.eventually_atTop.2 (h N v i)

theorem ev_ge (N : ℕ) (w : ℝ) : ∀ᶠ m : ℕ in Filter.atTop, (N : ℝ) ≤ m + w := by
  obtain ⟨m0, h⟩ := exists_nat_ge (N - w)
  filter_upwards [Filter.eventually_ge_atTop m0] with m hm
  have : (m0 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

theorem IsLim.eig (h : IsLim V ρ a M) (ψ : O → C) (c : C) (hc : ∀ m : ℕ, V.Ge m (ψ (a m) - c)) (v : n → C)
    (hv : ∀ x, ρ x *ᵥ v = ψ x • v) : M *ᵥ v = c • v := by
  funext i
  refine sub_eq_zero.1 (eq_zero_of_forall_ge (V := V) fun N => ?_)
  obtain ⟨w, hw⟩ := exists_ge (V := V) (v i)
  obtain ⟨m, h1, h2⟩ := ((h.ev N v).and (ev_ge N w)).exists
  have := (h1 i).add (((hc m).mul hw).mono h2)
  convert this using 1
  simp [hv]; ring

theorem IsLim.comm (h : IsLim V ρ a M) (hρ : ∀ x i j, V.Ge 0 (ρ x i j)) (x : O) (v : n → C) :
    M *ᵥ (ρ x *ᵥ v) = ρ x *ᵥ (M *ᵥ v) := by
  funext i
  refine sub_eq_zero.1 (eq_zero_of_forall_ge (V := V) fun N => ?_)
  obtain ⟨m, h1, h2⟩ := ((h.ev N v).and (h.ev N (ρ x *ᵥ v))).exists
  have := (h2 i).sub (mulVec_ge (hρ x) h1 i)
  convert this using 1
  have e : ρ (a m) *ᵥ (ρ x *ᵥ v) = ρ x *ᵥ (ρ (a m) *ᵥ v) := by
    rw [mulVec_mulVec, mulVec_mulVec, ← map_mul, ← map_mul, mul_comm]
  rw [mulVec_sub, e]
  simp only [Pi.sub_apply]; ring

theorem IsLim.idem (h : IsLim V ρ a M) (hρ : ∀ x i j, V.Ge 0 (ρ x i j))
    (ha : ∀ m, ∃ y, a m * a m - a m = (V.l : O) ^ m * y) (v : n → C) : M *ᵥ (M *ᵥ v) = M *ᵥ v := by
  funext i
  refine sub_eq_zero.1 (eq_zero_of_forall_ge (V := V) fun N => ?_)
  obtain ⟨w, hw⟩ := exists_ge_vec (V := V) v
  obtain ⟨m, ⟨h1, h2⟩, h3⟩ := (((h.ev N v).and (h.ev N (M *ᵥ v))).and (ev_ge N w)).exists
  obtain ⟨y, hy⟩ := ha m
  have e : ρ (a m) *ᵥ (ρ (a m) *ᵥ v) - ρ (a m) *ᵥ v = (V.l : C) ^ m • (ρ y *ᵥ v) := by
    rw [mulVec_mulVec, ← sub_mulVec, ← map_mul, ← map_sub, hy, ← smul_mulVec, ← Nat.cast_pow, ← Nat.cast_pow,
      ← nsmul_eq_mul, map_nsmul, Nat.cast_smul_eq_nsmul]
  have h4 := ((ge_l_pow m).mul (mulVec_ge (hρ y) hw i)).mono h3
  have := (((h2 i).add (mulVec_ge (hρ (a m)) h1 i)).add h4).sub (h1 i)
  convert this using 1
  have e' := congrFun e i
  rw [mulVec_sub]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e' ⊢
  linear_combination e'

theorem seq_one {ε : O} (ha : ∀ m, ∃ y, a m * a m - a m = (V.l : O) ^ m * y) (ha0 : ∀ m, ∃ y, a m - ε = (V.l : O) * y)
    (ψ : O →+* C) (hψ : ∀ x, V.Ge 0 (ψ x)) (h : V.MM (ψ ε - 1)) (m : ℕ) : V.Ge m (ψ (a m) - 1) := by
  obtain ⟨y, hy⟩ := ha m
  obtain ⟨z, hz⟩ := ha0 m
  have hy' := congrArg ψ hy
  have hz' := congrArg ψ hz
  simp only [map_sub, map_mul, map_pow, map_natCast] at hy' hz'
  apply ge_of_unit_mul (u := ψ (a m))
  · apply v_eq_zero_of_mm_sub_one
    convert mm_add h (mm_l_mul (hψ z)) using 1
    linear_combination hz'
  · have := (ge_l_pow m).mul (hψ y)
    rw [add_zero, ← hy'] at this
    convert this using 1; ring

theorem seq_zero {ε : O} (ha : ∀ m, ∃ y, a m * a m - a m = (V.l : O) ^ m * y) (ha0 : ∀ m, ∃ y, a m - ε = (V.l : O) * y)
    (ψ : O →+* C) (hψ : ∀ x, V.Ge 0 (ψ x)) (h : V.MM (ψ ε)) (m : ℕ) : V.Ge m (ψ (a m) - 0) := by
  obtain ⟨y, hy⟩ := ha m
  obtain ⟨z, hz⟩ := ha0 m
  have hy' := congrArg ψ hy
  have hz' := congrArg ψ hz
  simp only [map_sub, map_mul, map_pow, map_natCast] at hy' hz'
  apply ge_of_unit_mul (u := ψ (a m) - 1)
  · apply v_eq_zero_of_mm_add_one
    convert mm_add h (mm_l_mul (hψ z)) using 1
    linear_combination hz'
  · have := (ge_l_pow m).mul (hψ y)
    rw [add_zero, ← hy'] at this
    convert this using 1; ring

theorem exists_hom_of_eig (hρ : ∀ x i j, V.Ge 0 (ρ x i j)) (χ : O → C) (v : n → C) (hv0 : v ≠ 0)
    (hv : ∀ x, ρ x *ᵥ v = χ x • v) : ∃ ψ : O →+* C, (∀ x, ψ x = χ x) ∧ ∀ x, V.Ge 0 (ψ x) := by
  have inj : ∀ {s t : C}, s • v = t • v → s = t := fun h => smul_left_injective C hv0 h
  have hone : χ 1 = 1 := inj (by rw [← hv, map_one, one_mulVec, one_smul])
  have hmul : ∀ x y, χ (x * y) = χ x * χ y := fun x y =>
    inj (by rw [← hv, map_mul, ← mulVec_mulVec, hv, mulVec_smul, hv, smul_smul, mul_comm])
  have hadd : ∀ x y, χ (x + y) = χ x + χ y := fun x y =>
    inj (by rw [← hv, map_add, add_mulVec, hv, hv, add_smul])
  refine ⟨RingHom.mk' ⟨⟨χ, hone⟩, hmul⟩ hadd, fun _ => rfl, fun x => ?_⟩
  show V.Ge 0 (χ x)
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hv0
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => V.v (v i)) ⟨i0, Finset.mem_univ _⟩
  have hne : V.v (v i) ≠ ⊤ := by
    intro h
    have := hi i0 (Finset.mem_univ _)
    rw [h, top_le_iff, V.v.top_iff] at this
    exact hi0 this
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
  have h1 : V.Ge t ((ρ x *ᵥ v) i) :=
    mulVec_ge (hρ x) (fun j => by unfold VF.Ge; rw [ht]; exact hi j (Finset.mem_univ _)) i
  rw [hv] at h1
  unfold VF.Ge at h1 ⊢
  rw [Pi.smul_apply, smul_eq_mul, V.v.map_mul, ← ht] at h1
  induction hc : V.v (χ x) using WithTop.recTopCoe with
  | top => exact le_top
  | coe s =>
    rw [hc] at h1
    have h2 : t ≤ s + t := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ s := by linarith
    exact_mod_cast h3

theorem IsLim.range [IsAlgClosed C] {d : ℕ} [NeZero d] (h : IsLim V ρ a M) (hρ : ∀ x i j, V.Ge 0 (ρ x i j))
    (em : ZMod d → O →+* C) (hint : ∀ a x, V.Ge 0 (em a x))
    (hfr : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l))
    (hsep : ∀ a a', a ≠ a' → ∃ x, V.v (em a x - em a' x) = 0) (ε : O) (hε : ∃ y, ε * ε - ε = (V.l : O) * y)
    (hε1 : ∀ a, V.MM (em a ε - 1)) (hεP : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y)
    (ha : ∀ m, ∃ y, a m * a m - a m = (V.l : O) ^ m * y) (ha0 : ∀ m, ∃ y, a m - ε = (V.l : O) * y)
    (U : Submodule C (n → C)) (hU : ∀ t v, (∀ x, ρ x *ᵥ v = em t x • v) → v ∈ U) (v : n → C) : M *ᵥ v ∈ U := by
  let f : O → Module.End C (n → C) := fun x => (ρ x).mulVecLin
  have hf : ∀ x v, f x v = ρ x *ᵥ v := fun _ _ => rfl
  have hcomm : ∀ x y, Commute (f x) (f y) := fun x y => LinearMap.ext fun v => by
    simp only [Module.End.mul_apply, hf]
    rw [mulVec_mulVec, mulVec_mulVec, ← map_mul, ← map_mul, mul_comm]
  have hM : ∀ x, Commute (f x) M.mulVecLin := fun x => LinearMap.ext fun v => (h.comm hρ x v).symm
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun x y _ => hcomm x y) (fun x => Module.End.iSup_maxGenEigenspace_eq_top (f x))
  suffices hle : (⊤ : Submodule C (n → C)) ≤ U.comap M.mulVecLin from hle Submodule.mem_top
  rw [← htop]
  refine iSup_le fun χ u hu => ?_
  let W : Submodule C (n → C) := (⨅ x, (f x).maxGenEigenspace (χ x)) ⊓ LinearMap.eqLocus M.mulVecLin LinearMap.id
  have hMu : M *ᵥ u ∈ W := by
    refine ⟨?_, h.idem hρ ha u⟩
    rw [SetLike.mem_coe, Submodule.mem_iInf] at *
    exact fun x => Module.End.mapsTo_maxGenEigenspace_of_comm (hM x) (χ x) (hu x)
  show M *ᵥ u ∈ U
  let N : O → Module.End C (n → C) := fun x => f x - χ x • 1
  have hN : ∀ x v, N x v = ρ x *ᵥ v - χ x • v := fun _ _ => rfl
  have hNc : ∀ x y, Commute (N x) (N y) := fun x y =>
    ((hcomm x y).sub_right ((Commute.one_right _).smul_right _)).sub_left ((Commute.one_left _).smul_left _)
  have hNW : ∀ x, ∀ v ∈ W, N x v ∈ W := by
    intro x v hv
    refine W.sub_mem ⟨?_, ?_⟩ (W.smul_mem _ hv)
    · have h1 := hv.1
      rw [SetLike.mem_coe, Submodule.mem_iInf] at *
      exact fun y => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm y x) (χ y) (h1 y)
    · have h2 : M *ᵥ v = v := hv.2
      show M *ᵥ (ρ x *ᵥ v) = ρ x *ᵥ v
      rw [h.comm hρ, h2]
  have hNn : ∀ x, ∀ v ∈ W, ∃ k : ℕ, (N x ^ k) v = 0 := by
    intro x v hv
    have h1 := hv.1
    rw [SetLike.mem_coe, Submodule.mem_iInf] at h1
    exact (Module.End.mem_maxGenEigenspace _ _ _).1 (h1 x)
  by_cases hW : W ≤ ⊥
  · have : M *ᵥ u = 0 := hW hMu
    rw [this]; exact U.zero_mem
  obtain ⟨w, hwW, hw0, hw⟩ := exists_not_mem_forall_mem N hNc W ⊥ hNW hNn hW
  have hw' : ∀ x, ρ x *ᵥ w = χ x • w := fun x => sub_eq_zero.1 (hw x)
  obtain ⟨ψ, hψχ, hψ⟩ := exists_hom_of_eig hρ χ w hw0 hw'
  have hχ : χ = ψ := funext fun x => (hψχ x).symm
  have hmm : ¬ V.MM (ψ ε) := by
    intro hm
    have h1 := h.eig ψ 0 (seq_zero ha ha0 ψ hψ hm) w (fun x => by rw [hw', hψχ])
    have h2 : M *ᵥ w = w := hwW.2
    rw [h2, zero_smul] at h1
    exact hw0 h1
  obtain ⟨t, ht⟩ := eq_em_of_not_mm em hint hfr hsep ε hε hε1 hεP ψ hψ hmm
  have hχt : ∀ x, χ x = em t x := fun x => by rw [← hψχ, ht]
  let K : Submodule C (n → C) := ⨅ x, LinearMap.ker (N x)
  have hK : ∀ v, v ∈ K ↔ ∀ x, ρ x *ᵥ v = em t x • v := fun v => by
    simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, hN, sub_eq_zero, hχt]
  have hWK : W ≤ K := by
    by_contra hWK
    obtain ⟨z, -, hz0, hz⟩ := exists_not_mem_forall_mem N hNc W K hNW hNn hWK
    apply hz0
    rw [hK]
    intro x
    funext i
    obtain ⟨w, hw⟩ := exists_ge_vec (V := V) z
    let D : O →+ C := AddMonoidHom.mk' (fun x => (ρ x *ᵥ z) i - em t x * z i) (fun x y => by
      simp only [map_add, add_mulVec, Pi.add_apply]; ring)
    have hD : ∀ x, D x = (ρ x *ᵥ z) i - em t x * z i := fun _ => rfl
    refine sub_eq_zero.1 (twisted_der_eq_zero (em t) (em t) (hint t) (hint t) (fun x => by simpa using mm_zero) ε hε
      (hε1 t) d (NeZero.ne d) (fun x => hεP _ fun s => ?_) D (fun x y => ?_) w
      (fun x => (mulVec_ge (hρ x) hw i).sub ((hint t x).mul_int (hw i))) x)
    · simpa using mm_neg (frob_iter em hint hfr s x d)
    · have h1 := congrFun ((hK _).1 (hz y) x) i
      rw [hN, hχt, mulVec_sub, mulVec_smul, mulVec_mulVec, ← map_mul] at h1
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
      simp only [hD, map_mul (em t)]
      linear_combination h1
  exact hU t _ ((hK _).1 (hWK hMu))

end Limit

end GlobalTheory.PlaceProj
