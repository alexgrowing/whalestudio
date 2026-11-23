import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrR

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open ValuationFitting

section Val

variable {C : Type} [Field C] (V : VF C)

def bb : NNReal := ((V.l : ℕ) : NNReal)⁻¹

theorem bb_pos : 0 < bb V := by
  simp [bb, V.l_prime.pos]

theorem bb_lt : bb V < 1 := by
  have h : (1 : NNReal) < ((V.l : ℕ) : NNReal) := by exact_mod_cast V.l_prime.one_lt
  exact inv_lt_one_of_one_lt₀ h

variable {V}

theorem exists_real {x : C} (hx : x ≠ 0) : ∃ t : ℝ, V.v x = (t : WithTop ℝ) := by
  have h : V.v x ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h
  exact ⟨t, ht.symm⟩

variable (V)

def vmFun (x : C) : NNReal := if x = 0 then 0 else bb V ^ ((V.v x).untopD 0)

variable {V}

theorem vmFun_of {x : C} (hx : x ≠ 0) {t : ℝ} (ht : V.v x = (t : WithTop ℝ)) : vmFun V x = bb V ^ t := by
  simp [vmFun, hx, ht]

variable (V)

def vmOf : Valuation C NNReal where
  toFun := vmFun V
  map_zero' := by simp [vmFun]
  map_one' := by
    rw [vmFun_of one_ne_zero (t := 0) (by rw [V.v.map_one]; rfl), NNReal.rpow_zero]
  map_mul' := by
    intro x y
    by_cases hx : x = 0
    · simp [vmFun, hx]
    by_cases hy : y = 0
    · simp [vmFun, hy]
    obtain ⟨t, ht⟩ := exists_real (V := V) hx
    obtain ⟨s, hs⟩ := exists_real (V := V) hy
    rw [vmFun_of hx ht, vmFun_of hy hs, vmFun_of (mul_ne_zero hx hy) (t := t + s)
      (by rw [V.v.map_mul, ht, hs]; rfl), NNReal.rpow_add (bb_pos V).ne']
  map_add_le_max' := by
    intro x y
    by_cases hxy : x + y = 0
    · simp [vmFun, hxy]
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    obtain ⟨t, ht⟩ := exists_real (V := V) hx
    obtain ⟨s, hs⟩ := exists_real (V := V) hy
    obtain ⟨r, hr⟩ := exists_real (V := V) hxy
    rw [vmFun_of hx ht, vmFun_of hy hs, vmFun_of hxy hr]
    rcases V.v.map_add' x y with h | h
    · rw [ht, hr] at h
      exact le_max_of_le_left (NNReal.rpow_le_rpow_of_exponent_ge (bb_pos V) (bb_lt V).le (WithTop.coe_le_coe.mp h))
    · rw [hs, hr] at h
      exact le_max_of_le_right (NNReal.rpow_le_rpow_of_exponent_ge (bb_pos V) (bb_lt V).le (WithTop.coe_le_coe.mp h))

variable {V}

theorem vmOf_of {x : C} (hx : x ≠ 0) {t : ℝ} (ht : V.v x = (t : WithTop ℝ)) : vmOf V x = bb V ^ t := by
  show vmFun V x = _
  exact vmFun_of hx ht

theorem vmOf_l : vmOf V (V.l : C) = bb V := by
  have hl : (V.l : C) ≠ 0 := by
    intro h
    have h1 := V.v_l
    rw [h, AddValuation.map_zero] at h1
    simp at h1
  rw [vmOf_of hl (t := 1) (by rw [V.v_l]; rfl), NNReal.rpow_one]

theorem valTie_vmOf : ValTie V (vmOf V) := by
  intro x hx
  obtain ⟨t, ht⟩ := exists_real (V := V) hx
  refine ⟨t, ht, ?_⟩
  rw [vmOf_of hx ht, vmOf_l, NNReal.coe_rpow]

theorem integers_vmOf : (vmOf V).Integers V.RR where
  hom_inj := Subtype.coe_injective
  map_le_one := by
    intro x
    show vmOf V (x : C) ≤ 1
    by_cases hx : (x : C) = 0
    · rw [hx, map_zero]; exact zero_le_one
    obtain ⟨t, ht⟩ := exists_real (V := V) hx
    rw [vmOf_of hx ht]
    have h0 : V.Ge 0 (x : C) := x.2
    unfold VF.Ge at h0
    rw [ht] at h0
    exact NNReal.rpow_le_one (bb_lt V).le (WithTop.coe_le_coe.mp h0)
  exists_of_le_one := by
    intro r hr
    suffices h : V.Ge 0 r from ⟨⟨r, h⟩, rfl⟩
    by_cases hx : r = 0
    · rw [hx]; exact VF.Ge.zero 0
    obtain ⟨t, ht⟩ := exists_real (V := V) hx
    rw [vmOf_of hx ht] at hr
    unfold VF.Ge
    rw [ht]
    refine WithTop.coe_le_coe.mpr ?_
    by_contra hneg
    exact absurd hr (not_le.mpr (NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg (bb_pos V) (bb_lt V) (not_le.mp hneg)))

theorem not_isUnit_of_mm {x : V.RR} (hx : V.MM (x : C)) : ¬ IsUnit x := by
  intro hu
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have h1 : (x : C) * (y : C) = 1 := by
    have := congrArg Subtype.val hy
    simpa using this
  have h2 := congrArg V.v h1
  rw [AddValuation.map_mul, AddValuation.map_one] at h2
  have hy0 : (0 : WithTop ℝ) ≤ V.v (y : C) := y.2
  have hx0 : (0 : WithTop ℝ) < V.v (x : C) := hx
  have h3 : (0 : WithTop ℝ) < V.v (x : C) + V.v (y : C) := lt_of_lt_of_le hx0 (le_add_of_nonneg_right hy0)
  rw [h2] at h3
  exact lt_irrefl _ h3

theorem v_l_pow (n : ℕ) : V.v ((V.l : C) ^ n) = ((n : ℝ) : WithTop ℝ) := by
  rw [AddValuation.map_pow, V.v_l]
  simp

theorem mem_pow_iff (n : ℕ) (x : V.RR) :
    x ∈ (Ideal.span {((V.l : ℕ) : V.RR)} ^ n • ⊤ : Submodule V.RR V.RR) ↔ V.Ge n (x : C) := by
  have hl : (V.l : C) ≠ 0 := by
    intro h
    have h1 := V.v_l
    rw [h, AddValuation.map_zero] at h1
    simp at h1
  have hln : (V.l : C) ^ n ≠ 0 := pow_ne_zero _ hl
  rw [Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    show ((n : ℝ) : WithTop ℝ) ≤ V.v ((((((V.l : ℕ) : V.RR) ^ n * y : V.RR)) : C))
    push_cast
    rw [AddValuation.map_mul, v_l_pow]
    have hy : (0 : WithTop ℝ) ≤ V.v (y : C) := y.2
    exact le_add_of_nonneg_right hy
  · intro hx
    have hxy : (x : C) = (V.l : C) ^ n * ((x : C) / (V.l : C) ^ n) := by
      field_simp
    have h2 : V.v (x : C) = ((n : ℝ) : WithTop ℝ) + V.v ((x : C) / (V.l : C) ^ n) := by
      conv_lhs => rw [hxy]
      rw [AddValuation.map_mul, v_l_pow]
    have h3 : ((n : ℝ) : WithTop ℝ) + 0 ≤ ((n : ℝ) : WithTop ℝ) + V.v ((x : C) / (V.l : C) ^ n) := by
      rw [add_zero, ← h2]
      exact hx
    have hy : V.Ge 0 ((x : C) / (V.l : C) ^ n) := (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp h3
    refine ⟨⟨(x : C) / (V.l : C) ^ n, hy⟩, ?_⟩
    apply Subtype.ext
    show (x : C) = ((((V.l : ℕ) : V.RR) ^ n : V.RR) : C) * ((x : C) / (V.l : C) ^ n)
    push_cast
    exact hxy

theorem hausdorff_RR : IsHausdorff (Ideal.span {((V.l : ℕ) : V.RR)}) V.RR where
  haus' := by
    intro x hx
    apply Subtype.ext
    show (x : C) = 0
    by_contra h0
    obtain ⟨t, ht⟩ := exists_real (V := V) h0
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have h1 := hx n
    rw [SModEq.sub_mem, sub_zero, mem_pow_iff] at h1
    unfold VF.Ge at h1
    rw [ht] at h1
    exact absurd (WithTop.coe_le_coe.mp h1) (not_le.mpr hn)

theorem precomplete_RR
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) :
    IsPrecomplete (Ideal.span {((V.l : ℕ) : V.RR)}) V.RR where
  prec' := by
    intro f hf
    obtain ⟨x, hx⟩ := hc (fun n => (f n : C)) (fun n => by
      have h1 := hf (Nat.le_succ n)
      rw [SModEq.sub_mem, mem_pow_iff] at h1
      have h2 := h1.neg
      have e : -(((f n - f (n + 1) : V.RR)) : C) = (f (n + 1) : C) - (f n : C) := by
        push_cast
        ring
      rw [e] at h2
      exact h2)
    have hx0 : V.Ge 0 x := by
      have h1 : V.Ge 0 (x - (f 0 : C)) := by simpa using hx 0
      have h2 : V.Ge 0 ((f 0 : V.RR) : C) := (f 0).2
      have := h1.add h2
      simpa using this
    refine ⟨⟨x, hx0⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_pow_iff]
    have h2 := (hx n).neg
    have e : -(x - (f n : C)) = (((f n - (⟨x, hx0⟩ : V.RR) : V.RR)) : C) := by
      push_cast
      ring
    rw [e] at h2
    exact h2

end Val

section Zl

variable (l : ℕ) [Fact l.Prime] (S : Type) [CommRing S]

theorem ringChar_dvd_pow (n : ℕ) : ringChar (S ⧸ Ideal.span {(l : S)} ^ n) ∣ l ^ n := by
  apply ringChar.dvd
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (l : S)) n : (l : S) ^ n ∈ Ideal.span {(l : S)} ^ n)
  simpa using h

def zlStep (n : ℕ) : ℤ_[l] →+* S ⧸ Ideal.span {(l : S)} ^ n :=
  (ZMod.castHom (ringChar_dvd_pow l S n) (S ⧸ Ideal.span {(l : S)} ^ n)).comp (PadicInt.toZModPow n)

theorem zlStep_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(l : S)}) hle).comp (zlStep l S n) = zlStep l S m := by
  unfold zlStep
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact Subsingleton.elim _ _

def zlHom [IsAdicComplete (Ideal.span {(l : S)}) S] : ℤ_[l] →+* S :=
  IsAdicComplete.liftRingHom (Ideal.span {(l : S)}) (zlStep l S) (fun hle => zlStep_compat l S hle)

end Zl

theorem ringPkSt_holds : RingPkSt := by
  intro C _ _ V hc
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  have hl : (V.l : C) ≠ 0 := by
    intro h
    have h1 := V.v_l
    rw [h, AddValuation.map_zero] at h1
    simp at h1
  have hvl : V.MM ((((V.l : ℕ) : V.RR)) : C) := by
    show (0 : WithTop ℝ) < V.v ((((V.l : ℕ) : V.RR)) : C)
    push_cast
    rw [V.v_l]
    exact (WithTop.coe_lt_coe.mpr (zero_lt_one : (0 : ℝ) < 1))
  have hunit : ∀ x : V.RR, ¬ V.MM (x : C) → IsUnit x := by
    intro x hx
    have hx0 : (x : C) ≠ 0 := by
      intro h
      apply hx
      show (0 : WithTop ℝ) < V.v (x : C)
      rw [h, AddValuation.map_zero]
      exact WithTop.coe_lt_top 0
    have hv0 : V.v (x : C) = 0 := by
      have h1 : (0 : WithTop ℝ) ≤ V.v (x : C) := x.2
      have h2 : ¬ (0 : WithTop ℝ) < V.v (x : C) := hx
      exact le_antisymm (not_lt.mp h2) h1
    have hinv : V.Ge 0 ((x : C)⁻¹) := by
      show ((0 : ℝ) : WithTop ℝ) ≤ V.v ((x : C)⁻¹)
      have h3 : V.v ((x : C) * (x : C)⁻¹) = 0 := by
        rw [mul_inv_cancel₀ hx0, AddValuation.map_one]
      rw [AddValuation.map_mul, hv0, zero_add] at h3
      rw [h3]
      rfl
    refine isUnit_iff_exists_inv.mpr ⟨⟨(x : C)⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    show (x : C) * (x : C)⁻¹ = 1
    exact mul_inv_cancel₀ hx0
  have hloc : IsLocalRing V.RR := IsLocalRing.of_nonunits_add (fun a b ha hb => by
    have ha' : V.MM (a : C) := by
      by_contra h
      exact (mem_nonunits_iff.mp ha) (hunit a h)
    have hb' : V.MM (b : C) := by
      by_contra h
      exact (mem_nonunits_iff.mp hb) (hunit b h)
    exact mem_nonunits_iff.mpr (not_isUnit_of_mm (V := V) (x := a + b)
      (lt_of_lt_of_le (lt_min ha' hb') (V.v.map_add _ _))))
  haveI hcpl : IsAdicComplete (Ideal.span {((V.l : ℕ) : V.RR)}) V.RR :=
    { haus' := (hausdorff_RR (V := V)).haus', prec' := (precomplete_RR (V := V) hc).prec' }
  haveI := hloc
  exact ⟨{ vm := vmOf V
           tie := valTie_vmOf
           int := integers_vmOf
           pos := by
             rw [vmOf_l]
             exact_mod_cast bb_pos V
           lt := by
             rw [vmOf_l]
             exact_mod_cast bb_lt V
           nonunit := not_isUnit_of_mm (V := V) hvl
           cpl := hcpl
           loc := hloc
           alg := (zlHom V.l V.RR).toAlgebra
           mm := fun x hx => (IsLocalRing.mem_maximalIdeal x).mpr (mem_nonunits_iff.mpr (not_isUnit_of_mm hx)) }⟩

end UpFBr

end Formalism.L2.FormalSeriesBounds
