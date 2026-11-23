import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef

noncomputable section

open Polynomial

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyRes

open RowTiePKey

section Res

variable {C : Type} [Field C] (V : VF C)

theorem valuation_nonneg_iff (a : C) : V.Ge 0 a ↔ 0 ≤ V.v a := by
  first
  | exact Iff.rfl
  | (simp only [VF.Ge]; done)
  | (unfold VF.Ge; done)
  | (simp [VF.Ge])

def Rv : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => (VF.Ge.mul ha hb).mono (by norm_num)
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

def mm : Ideal (Rv V) where
  carrier := {x | V.MM (x : C)}
  add_mem' := fun {a b} ha hb => by
    show V.MM ((a : C) + b)
    exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add _ _)
  zero_mem' := by
    show V.MM ((0 : Rv V) : C)
    simp [VF.MM]
  smul_mem' := fun c x hx => by
    show V.MM ((c : C) * x)
    have hx' : (0 : WithTop ℝ) < V.v x := hx
    have hc : (0 : WithTop ℝ) ≤ V.v c := (valuation_nonneg_iff V c).1 c.2
    show (0 : WithTop ℝ) < V.v ((c : C) * x)
    rw [AddValuation.map_mul]
    calc (0 : WithTop ℝ) < V.v x := hx'
      _ = 0 + V.v x := (zero_add _).symm
      _ ≤ V.v c + V.v x := add_le_add hc le_rfl

theorem mm_max : (mm V).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨?_, ?_⟩
  · intro h1
    have h1' : (0 : WithTop ℝ) < V.v ((1 : Rv V) : C) := h1
    simp at h1'
  · intro J x _ hx hxJ
    have hx' : ¬ (0 : WithTop ℝ) < V.v (x : C) := hx
    have hx0 : (x : C) ≠ 0 := by
      intro h0
      apply hx'
      rw [h0]
      simp
    have hvx : V.v (x : C) = 0 := le_antisymm (not_lt.1 hx') ((valuation_nonneg_iff V x).1 x.2)
    have hy : V.Ge 0 ((x : C)⁻¹) := (valuation_nonneg_iff V _).2 (by
      first
      | (rw [AddValuation.map_inv, hvx, neg_zero]; done)
      | (rw [AddValuation.map_inv, hvx, neg_zero]; exact le_rfl)
      | simp [AddValuation.map_inv, hvx])
    have h1 : (1 : Rv V) = ⟨(x : C)⁻¹, hy⟩ * x := Subtype.ext (by simp [hx0])
    rw [h1]
    exact J.mul_mem_left _ hxJ

instance : (mm V).IsMaximal := mm_max V

abbrev Kr := Rv V ⧸ mm V

noncomputable instance : Field (Kr V) := Ideal.Quotient.field (mm V)

theorem charP_Kr : CharP (Kr V) V.l := by
  rw [CharP.charP_iff_prime_eq_zero V.3]
  rw [← map_natCast (Ideal.Quotient.mk (mm V)) V.l, Ideal.Quotient.eq_zero_iff_mem]
  show (0 : WithTop ℝ) < V.v ((V.l : Rv V) : C)
  rw [SubringClass.coe_natCast, V.4]
  first
  | exact WithTop.coe_lt_coe.2 zero_lt_one
  | norm_num
  | simp

variable {V}

def red {O : Type} [CommRing O] (f : O →+* C) (hf : ∀ x, V.Ge 0 (f x)) : O →+* Kr V :=
  (Ideal.Quotient.mk (mm V)).comp (f.codRestrict (Rv V) hf)

theorem red_eq_iff {O : Type} [CommRing O] (f g : O →+* C) (hf : ∀ x, V.Ge 0 (f x)) (hg : ∀ x, V.Ge 0 (g x))
    (x y : O) : red f hf x = red g hg y ↔ V.MM (f x - g y) := by
  unfold red
  rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq]
  exact Iff.rfl

theorem red_zero_iff {O : Type} [CommRing O] (f : O →+* C) (hf : ∀ x, V.Ge 0 (f x)) (x : O) :
    red f hf x = 0 ↔ V.MM (f x) := by
  unfold red
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Iff.rfl

end Res

section Fin

variable {k : Type} [Field k]

theorem fixed_nat (p : ℕ) [hp : Fact p.Prime] [CharP k p] (a : k) (ha : a ^ p = a) : ∃ i : ℕ, a = i := by
  classical
  let φ : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  have hφ : Function.Injective φ := φ.injective
  have hp1 : 1 < p := hp.out.one_lt
  have hP : (X ^ p - X : k[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hp1
  have hroot : ∀ b : k, b ^ p = b → b ∈ (X ^ p - X : k[X]).roots.toFinset := by
    intro b hb
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    simp [hb]
  by_contra hne
  push_neg at hne
  have hnotin : a ∉ Finset.univ.image φ := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
    apply hne i.val
    rw [← hi]
    simp [φ]
  have hsub : insert a (Finset.univ.image φ) ⊆ (X ^ p - X : k[X]).roots.toFinset := by
    intro b hb
    rcases Finset.mem_insert.1 hb with hb | hb
    · rw [hb]; exact hroot _ ha
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hb
      rw [← hi]
      apply hroot
      rw [← map_pow, ZMod.pow_card]
  have h1 := Finset.card_le_card hsub
  have h3 : (insert a (Finset.univ.image φ)).card = p + 1 := by
    first
    | rw [Finset.card_insert_of_notMem hnotin, Finset.card_image_of_injective _ hφ, Finset.card_univ,
        ZMod.card]
    | rw [Finset.card_insert_of_not_mem hnotin, Finset.card_image_of_injective _ hφ, Finset.card_univ,
        ZMod.card]
  rw [h3] at h1
  have h2 : (X ^ p - X : k[X]).roots.toFinset.card ≤ p := by
    calc (X ^ p - X : k[X]).roots.toFinset.card ≤ Multiset.card (X ^ p - X : k[X]).roots :=
          Multiset.toFinset_card_le _
      _ ≤ (X ^ p - X : k[X]).natDegree := Polynomial.card_roots' _
      _ = p := FiniteField.X_pow_card_sub_X_natDegree_eq k hp1
  omega

theorem exists_lift (p : ℕ) [Fact p.Prime] [CharP k p] (Q : k[X]) (hQ : ∀ i, Q.coeff i ^ p = Q.coeff i) :
    ∃ μ : ℤ[X], μ.map (Int.castRingHom k) = Q := by
  classical
  choose f hf using fun i => fixed_nat p (Q.coeff i) (hQ i)
  refine ⟨∑ i ∈ Q.support, Polynomial.monomial i ((f i : ℕ) : ℤ), ?_⟩
  rw [Polynomial.map_sum]
  conv_rhs => rw [Q.as_sum_support]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_monomial, hf i]
  simp

def Hs {O : Type} [CommRing O] (f : O →+* k) (q : ℕ) (hq2 : 2 ≤ q) (hq : ∀ y, f y ^ q = f y) : Subgroup kˣ where
  carrier := {u | ∃ y, f y = (u : k)}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro u v ⟨y1, h1⟩ ⟨y2, h2⟩
    exact ⟨y1 * y2, by rw [map_mul, h1, h2, Units.val_mul]⟩
  inv_mem' := by
    rintro u ⟨y, h⟩
    refine ⟨y ^ (q - 2), ?_⟩
    have hu : (u : k) ^ q = u := by rw [← h]; exact hq y
    rw [map_pow, h]
    have hu1 : (u : k) ^ (q - 2) * u = 1 := by
      have h5 : (u : k) ^ (q - 2) * u * u = 1 * u := by
        rw [← pow_succ, ← pow_succ, show q - 2 + 1 + 1 = q by omega, hu, one_mul]
      exact mul_right_cancel₀ u.ne_zero h5
    exact Units.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hu1)

theorem core (p : ℕ) [hp : Fact p.Prime] [CharP k p] {O : Type} [CommRing O] {d : ℕ} [NeZero d]
    (e : ZMod d → (O →+* k)) (hfr : ∀ a x, e (a + 1) x = e a x ^ p) (χ : O →+* k)
    (hker : ∀ z, (∀ a, e a z = 0) → χ z = 0) : ∃ c, ∀ y, χ y = e c y := by
  classical
  have : ExpChar k p := ExpChar.prime hp.out
  have hpow : ∀ (j : ℕ) x, e (j : ZMod d) x = e 0 x ^ (p ^ j) := by
    intro j x
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.cast_succ, hfr, ih, ← pow_mul, pow_succ]
  have hall : ∀ a x, e a x = e 0 x ^ (p ^ a.val) := fun a x => by
    rw [← hpow, ZMod.natCast_zmod_val]
  have hkill : ∀ x, e 0 x = 0 → ∀ a, e a x = 0 := fun x h a => by
    rw [hall, h, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  have hq : ∀ x, e 0 x ^ (p ^ d) = e 0 x := fun x => by rw [← hpow, ZMod.natCast_self]
  have hq1 : 1 < p ^ d := Nat.one_lt_pow (NeZero.ne d) hp.out.one_lt

  have hpt : ∀ y, ∃ c, χ y = e c y := by
    intro y
    set Q : k[X] := ∏ c : ZMod d, (X - Polynomial.C (e c y)) with hQ
    have hfix : Q.map (frobenius k p) = Q := by
      rw [hQ, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, frobenius_def, ← hfr]
      exact Fintype.prod_equiv (Equiv.addRight 1) _ _ fun c => rfl
    have hcoef : ∀ i, Q.coeff i ^ p = Q.coeff i := fun i => by
      have h1 := congrArg (fun P => Polynomial.coeff P i) hfix
      simp only [coeff_map, frobenius_def] at h1
      exact h1
    obtain ⟨μ, hμ⟩ := exists_lift p Q hcoef
    have hev : ∀ g : O →+* k, g (μ.eval₂ (Int.castRingHom O) y) = Q.eval (g y) := fun g => by
      rw [hom_eval₂, RingHom.ext_int (g.comp (Int.castRingHom O)) (Int.castRingHom k), eval₂_eq_eval_map, hμ]
    have hz : χ (μ.eval₂ (Int.castRingHom O) y) = 0 := hker _ fun a => by
      rw [hev, hQ, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [eval_sub, eval_X, eval_C, sub_self])
    rw [hev, hQ, eval_prod, Finset.prod_eq_zero_iff] at hz
    obtain ⟨c, -, hc⟩ := hz
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hc
    exact ⟨c, hc⟩

  have hfin : Finite (Hs (e 0) (p ^ d) hq1 hq) := by
    have hQ0 : (X ^ (p ^ d) - X : k[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hq1
    have hF : Finite ↥(((X ^ (p ^ d) - X : k[X]).roots.toFinset : Set k)) := (Finset.finite_toSet _).to_subtype
    refine Finite.of_injective (β := ↥(((X ^ (p ^ d) - X : k[X]).roots.toFinset : Set k)))
      (fun u => ⟨((u : kˣ) : k), ?_⟩) ?_
    · obtain ⟨y, hy⟩ := u.2
      rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hQ0, IsRoot, eval_sub, eval_pow, eval_X, ← hy, hq, sub_self]
    · intro u v huv
      exact Subtype.ext (Units.ext (congrArg Subtype.val huv))
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Hs (e 0) (p ^ d) hq1 hq)
  obtain ⟨y0, hy0⟩ := g.2
  obtain ⟨c, hc⟩ := hpt y0
  refine ⟨c, fun y => ?_⟩
  by_cases hy : e 0 y = 0
  · rw [hker y (hkill y hy), hkill y hy c]
  · have hmem : Units.mk0 (e 0 y) hy ∈ Hs (e 0) (p ^ d) hq1 hq := ⟨y, by rw [Units.val_mk0]⟩
    have h1 := (mem_powers_iff_mem_zpowers).2 (hg ⟨_, hmem⟩)
    obtain ⟨m, hm⟩ := Submonoid.mem_powers_iff _ _ |>.1 h1
    have h2 : e 0 y0 ^ m = e 0 y := by
      have h3 := congrArg (fun s : Hs (e 0) (p ^ d) hq1 hq => ((s : kˣ) : k)) hm
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Units.val_mk0] at h3
      rw [hy0]
      exact h3
    have h4 : e 0 (y - y0 ^ m) = 0 := by rw [map_sub, map_pow, h2, sub_self]
    have h5 := hker _ (hkill _ h4)
    have h6 := hkill _ h4 c
    rw [map_sub, sub_eq_zero] at h5 h6
    rw [h5, h6, map_pow, map_pow, hc]

end Fin

theorem keyRes_holds : KeyResSt := by
  intro C _ _ V O _ n d _ K χ hχ hz
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  have : CharP (Kr V) V.l := charP_Kr V
  have hfr : ∀ a x, red (K.em (a + 1)) (K.em_int (a + 1)) x = red (K.em a) (K.em_int a) x ^ V.l := by
    intro a x
    rw [← map_pow, red_eq_iff, map_pow]
    exact K.em_frob a x
  have hker : ∀ z, (∀ a, red (K.em a) (K.em_int a) z = 0) → red χ hχ z = 0 := by
    intro z hzz
    rw [red_zero_iff]
    exact hz z fun a => (red_zero_iff _ _ _).1 (hzz a)
  obtain ⟨c, hc⟩ := core V.l (fun a => red (K.em a) (K.em_int a)) hfr (red χ hχ) hker
  exact ⟨c, fun y => (red_eq_iff _ _ _ _ _ _).1 (hc y)⟩

end RowTiePKeyRes

end Formalism.L2.FormalSeriesBounds
