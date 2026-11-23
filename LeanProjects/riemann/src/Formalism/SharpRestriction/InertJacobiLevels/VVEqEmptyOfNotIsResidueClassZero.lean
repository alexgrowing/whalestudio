import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.DataForced

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain

section Places

variable (D : D7)

theorem natCast_mem_of_val_pos (w : D.what₂.places.Pl) (n : ℕ) (hn : n ≠ 0)
    (h : (0 : WithTop ℤ) < D.what₂.places.val w (n : D.what₂.LL)) :
    (n : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  by_contra hnm
  have hn0 : (n : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [D.val_eq w _ hn0] at h
  have hv : (D.plEq w).valuation D.what₂.LL (n : D.what₂.LL) = 1 := by
    have e : algebraMap (𝓞 D.what₂.LL) D.what₂.LL (n : 𝓞 D.what₂.LL) = (n : D.what₂.LL) := map_natCast _ n
    rw [← e, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm ((D.plEq w).intValuation_le_one _)
      (not_lt.mp (fun hlt => hnm (((D.plEq w).intValuation_lt_one_iff_mem _).1 hlt)))
  unfold vAdd at h
  rw [hv, WithZero.log_one, neg_zero] at h
  norm_num at h

theorem resChar_mem (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  exact natCast_mem_of_val_pos D w _ (D.what₂.places.resChar_prime w).ne_zero
    (by rw [D.what₂.places.val_resChar]; exact_mod_cast D.what₂.places.ramIdx_pos w)

theorem eq_resChar_of_mem (w : D.what₂.places.Pl) (p : ℕ) (hp : p.Prime)
    (h : (p : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) : D.what₂.places.resChar w = p := by
  by_contra hne
  have hl := resChar_mem D w
  have hcop : Nat.Coprime (D.what₂.places.resChar w) p :=
    (Nat.coprime_primes (D.what₂.places.resChar_prime w) hp).2 hne
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : ((u : 𝓞 D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) +
      (v : 𝓞 D.what₂.LL) * (p : 𝓞 D.what₂.LL)) ∈ (D.plEq w).asIdeal :=
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ h)
  have h2 : ((u : 𝓞 D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) +
      (v : 𝓞 D.what₂.LL) * (p : 𝓞 D.what₂.LL)) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) huv
    push_cast at this
    exact this
  rw [h2] at h1
  exact (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem resChar_conj (w : D.what₂.places.Pl) :
    D.what₂.places.resChar (D.what₂.places.conj w) = D.what₂.places.resChar w := by
  apply eq_resChar_of_mem D _ _ (D.what₂.places.resChar_prime w)
  apply natCast_mem_of_val_pos D _ _ (D.what₂.places.resChar_prime w).ne_zero
  rw [D.conj_val, star_natCast, D.what₂.places.val_resChar]
  exact_mod_cast D.what₂.places.ramIdx_pos w

theorem finite_resChar_le (B : ℝ) :
    {w : D.what₂.places.Pl | ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ B}.Finite := by
  have hM0 : ((Nat.factorial ⌊B⌋₊ : ℕ) : 𝓞 D.what₂.LL) ≠ 0 := by
    intro h0
    have := congrArg (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) h0
    rw [map_natCast, map_zero] at this
    exact Nat.factorial_ne_zero _ (by exact_mod_cast this)
  have hfin : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL) |
      v.asIdeal ∣ Ideal.span {((Nat.factorial ⌊B⌋₊ : ℕ) : 𝓞 D.what₂.LL)}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  refine (hfin.preimage D.plEq.injective.injOn).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hw ⊢
  rw [Ideal.dvd_span_singleton]
  have hl := resChar_mem D w
  have hle : D.what₂.places.resChar w ≤ ⌊B⌋₊ := Nat.le_floor hw
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (D.what₂.places.resChar_prime w).pos hle
  rw [hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hl

theorem finite_resChar_mem (S : Finset ℕ) : {w : D.what₂.places.Pl | D.what₂.places.resChar w ∈ S}.Finite := by
  refine (finite_resChar_le D ((S.sup id : ℕ) : ℝ)).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  exact_mod_cast Finset.le_sup (f := id) hw

theorem exists_place_over (p : ℕ) (hp : p.Prime) : ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w = p := by
  have hp0 : (p : 𝓞 D.what₂.LL) ≠ 0 := by
    intro h0
    have := congrArg (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) h0
    rw [map_natCast, map_zero] at this
    exact hp.ne_zero (by exact_mod_cast this)
  have hnu : ¬ IsUnit (p : 𝓞 D.what₂.LL) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ (S := 𝓞 D.what₂.LL))
    rw [show (p : 𝓞 D.what₂.LL) = algebraMap ℤ (𝓞 D.what₂.LL) (p : ℤ) by simp,
      Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff] at h1
    have := hp.one_lt
    rcases h1 with h1 | h1 <;> omega
  obtain ⟨M, hM, hpM⟩ := Ideal.exists_le_maximal (Ideal.span {(p : 𝓞 D.what₂.LL)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL) :=
    ⟨M, hM.isPrime, fun hb => hp0 ((Ideal.mem_bot).1 (hb ▸ hpM (Ideal.mem_span_singleton_self _)))⟩
  refine ⟨D.plEq.symm v, eq_resChar_of_mem D _ p hp ?_⟩
  rw [Equiv.apply_symm_apply]
  exact hpM (Ideal.mem_span_singleton_self _)

end Places

section Base

variable {N : ℕ} [NeZero N]

theorem val_orbit (h t : ZMod N) (i : ℕ) : (t + i • h).val = (t.val + i * h.val) % N := by
  rw [show t + i • h = ((t.val + i * h.val : ℕ) : ZMod N) by
    simp [nsmul_eq_mul, ZMod.natCast_zmod_val], ZMod.val_natCast]

def bsVal (N h t : ℕ) : ℕ := sInf {v | ∃ i : ℕ, (t + i * h) % N = v}

theorem bsVal_mem (N h t : ℕ) : ∃ i : ℕ, (t + i * h) % N = bsVal N h t := by
  unfold bsVal
  exact Nat.sInf_mem (s := {v | ∃ i : ℕ, (t + i * h) % N = v}) ⟨(t + 0 * h) % N, 0, rfl⟩

def bsC (h t : ZMod N) : ZMod N := (bsVal N h.val t.val : ℕ)

theorem bsC_val (h t : ZMod N) : (bsC h t).val = bsVal N h.val t.val := by
  unfold bsC
  rw [ZMod.val_natCast]
  obtain ⟨i, hi⟩ := bsVal_mem N h.val t.val
  rw [← hi, Nat.mod_mod]

theorem bsC_eq (h t : ZMod N) : ∃ i : ℕ, bsC h t = t + i • h := by
  obtain ⟨i, hi⟩ := bsVal_mem N h.val t.val
  refine ⟨i, ?_⟩
  unfold bsC
  rw [← hi, ZMod.natCast_mod]
  simp [nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem card_nsmul_zmod (h : ZMod N) : N • h = 0 := by
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem bsC_orb (h t : ZMod N) : ∃ i : ℕ, bsC h t + i • h = t := by
  obtain ⟨i, hi⟩ := bsC_eq h t
  refine ⟨(N - 1) * i, ?_⟩
  rw [hi]
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_sub hN, ZMod.natCast_self, Nat.cast_one]
  ring

theorem bsC_step (h t : ZMod N) : bsC h (t + h) = bsC h t := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  unfold bsC
  congr 1
  unfold bsVal
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, ← val_orbit]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i + 1, ?_⟩
    rw [add_nsmul, one_nsmul, add_comm (i • h) h, ← add_assoc]
  · rintro ⟨i, rfl⟩
    refine ⟨i + (N - 1), ?_⟩
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_sub hN, ZMod.natCast_self, Nat.cast_one]
    ring

end Base

theorem scale_b'_nonneg (sc : Scale) : 0 ≤ sc.b' := by
  have hx : 0 < sc.x := by linarith [sc.one_lt_alt]
  have hb : 0 < sc.b := Real.exp_pos _
  have hX : 0 < sc.X' := Real.exp_pos _
  exact div_nonneg (mul_nonneg hx.le hb.le) hX.le

theorem scale_w''_le (sc : Scale) (n : ℕ) (hn : 1 ≤ n) : sc.w'' n ≤ sc.b' / sc.x ∧ sc.w'' n ≤ sc.b := by
  have hx : 0 < sc.x := by linarith [sc.one_lt_alt]
  have hb : 0 < sc.b := Real.exp_pos _
  have hX : 1 ≤ sc.X' := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hb' : 0 ≤ sc.b' := scale_b'_nonneg sc
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : sc.w'' n ≤ sc.b' / sc.x := by
    show sc.b' / (sc.x * n) ≤ sc.b' / sc.x
    rw [← div_div]
    exact div_le_self (div_nonneg hb' hx.le) hn'
  have h2 : sc.b' / sc.x ≤ sc.b := by
    rw [div_le_iff₀ hx]
    show sc.x * sc.b / sc.X' ≤ sc.b * sc.x
    rw [mul_comm sc.b]
    exact div_le_self (mul_nonneg hx.le hb.le) hX
  exact ⟨h1, h1.trans h2⟩

theorem scale_X'_le_X'' (sc : Scale) (n : ℕ) (hn : 1 ≤ n) : sc.X' ≤ sc.X'' n := by
  have hx : 0 < sc.x := by linarith [sc.one_lt_alt]
  have hb : 0 < sc.b := Real.exp_pos _
  have hX0 : 0 < sc.X' := Real.exp_pos _
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hxn : 1 ≤ sc.x * n := by nlinarith [sc.one_lt_alt]
  have hw : 0 < sc.w'' n := by
    show 0 < sc.x * sc.b / sc.X' / (sc.x * n)
    exact div_pos (div_pos (mul_pos hx hb) hX0) (by linarith)
  show sc.X' ≤ sc.a / sc.w'' n
  rw [le_div_iff₀ hw]
  show sc.X' * (sc.x * sc.b / sc.X' / (sc.x * n)) ≤ sc.x * sc.b
  rw [div_div, mul_div_assoc', mul_div_mul_left _ _ hX0.ne']
  exact div_le_self (mul_nonneg hx.le hb.le) hxn

theorem ranks_one_le_n (R : Ranks) : 1 ≤ R.n := by
  exact R.toFrame.ord_pos

section BaseA

variable {φ : Formalism.HC.Frame}

def bsVA (h t : φ.A) : ℕ := sInf {v | ∃ i : ℕ, (t + i • h).val = v}

theorem bsVA_mem (h t : φ.A) : ∃ i : ℕ, (t + i • h).val = bsVA h t := by
  unfold bsVA
  exact Nat.sInf_mem (s := {v | ∃ i : ℕ, (t + i • h).val = v}) ⟨(t + 0 • h).val, 0, rfl⟩

def bsA (h t : φ.A) : φ.A := φ.ofNat (bsVA h t)

theorem bsA_eq (h t : φ.A) : ∃ i : ℕ, bsA h t = t + i • h := by
  obtain ⟨i, hi⟩ := bsVA_mem h t
  refine ⟨i, ?_⟩
  apply Fin.ext (n := φ.ord)
  show bsVA h t % φ.ord = Fin.val (n := φ.ord) (t + i • h)
  rw [← hi]
  exact Nat.mod_eq_of_lt (Fin.isLt (n := φ.ord) (t + i • h))

theorem bsA_val (h t : φ.A) : (bsA h t).val = bsVA h t := by
  obtain ⟨i, hi⟩ := bsVA_mem h t
  show bsVA h t % φ.ord = bsVA h t
  rw [← hi]
  exact Nat.mod_eq_of_lt (Fin.isLt (n := φ.ord) (t + i • h))

private theorem ord_nsmul_eq_zero (h : φ.A) : φ.ord • h = 0 := by
  have h2 : Nat.card φ.A = φ.ord := by
    show Nat.card (Fin φ.ord) = φ.ord
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← h2]
  exact card_nsmul_eq_zero'

theorem bsA_orb (h t : φ.A) : ∃ i : ℕ, bsA h t + i • h = t := by
  obtain ⟨i, hi⟩ := bsA_eq h t
  obtain ⟨m, hm⟩ : ∃ m, φ.ord = m + 1 := ⟨φ.ord - 1, by have := φ.ord_pos; omega⟩
  have hk := ord_nsmul_eq_zero h
  rw [hm, succ_nsmul] at hk
  refine ⟨m * i, ?_⟩
  rw [hi]
  have key : ∀ k : ℕ, (k + m * k) • h = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : (k + 1 + m * (k + 1)) • h = (k + m * k) • h + (m • h + h) := by
        rw [show k + 1 + m * (k + 1) = (k + m * k) + (m + 1) by ring, add_nsmul, succ_nsmul]
      rw [e, ih, hk, add_zero]
  rw [add_assoc, ← add_nsmul, key, add_zero]

theorem bsA_step (h t : φ.A) : bsA h (t + h) = bsA h t := by
  obtain ⟨m, hm⟩ : ∃ m, φ.ord = m + 1 := ⟨φ.ord - 1, by have := φ.ord_pos; omega⟩
  have hk := ord_nsmul_eq_zero h
  rw [hm, succ_nsmul] at hk
  unfold bsA
  congr 1
  unfold bsVA
  congr 1
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i + 1, ?_⟩
    rw [succ_nsmul, add_comm (i • h) h, ← add_assoc]
  · rintro ⟨i, rfl⟩
    refine ⟨i + m, ?_⟩
    rw [add_nsmul]
    congr 1
    calc t + h + (i • h + m • h) = t + i • h + (m • h + h) := by abel
      _ = t + i • h := by rw [hk, add_zero]

theorem bsA_val_le (h t : φ.A) (i : ℕ) : (bsA h t).val ≤ (t + i • h).val := by
  rw [bsA_val]
  unfold bsVA
  exact Nat.sInf_le ⟨i, rfl⟩

theorem ord_nsmul_A (h : φ.A) : φ.ord • h = 0 := by
  exact ord_nsmul_eq_zero h

end BaseA

open Classical in

def offC (D : D7) (sc : Scale) (_j : ℕ) (z : Bool × G.HH D) : ℝ :=
  if G.IsTopPl D z then sc.b' / sc.x else if G.IsThickPl D z then sc.b else sc.w'' D.R.n

def instC (D : D7) (L : SizeData₂ D)
    (kapI : ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ) (ep : ℕ → ℕ) : G.Inst D L where
  bs := bsA
  bs_orb := bsA_orb
  bs_step := bsA_step
  off := offC D L.sc
  off_top := fun j z hz => by
    have := L.etaSz_pos
    simp only [offC, if_pos hz]
    constructor <;> linarith
  off_thin := fun j z hz => by
    have := L.etaSz_pos
    simp only [offC, if_neg hz.1, if_neg hz.2]
    constructor <;> linarith
  off_thick := fun j z hz => by
    have := L.etaSz_pos
    have ht : ¬ G.IsTopPl D z := fun h => by
      have h1 := h.1
      rw [hz.1] at h1
      exact Bool.noConfusion h1
    simp only [offC, if_neg ht, if_pos hz]
    constructor <;> linarith

  kapI := kapI
  ep := ep

section InstW

variable (D : D7)

theorem plGG_false (t : G.HH D) : G.plGG D (false, t) = D.R.tau1 t := by
  unfold G.plGG
  simp

theorem plGG_true (t : G.HH D) : G.plGG D (true, t) = D.R.tau2 t := by
  unfold G.plGG
  simp

theorem plGG_mem_Psi (z : Bool × G.HH D) : G.plGG D z ∈ D.R.Psi := by
  unfold G.plGG Formalism.HC.Frame.Psi
  rw [MonoidHom.mem_ker]
  split <;> first
    | rfl
    | simp [Formalism.HC.Frame.chD, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2]

def tauOf (z : Bool × G.HH D) : D.what₂.Tau := D.eTau.symm ⟨G.plGG D z, plGG_mem_Psi D z⟩

theorem eTau_tauOf (z : Bool × G.HH D) : (D.eTau (tauOf D z) : D.R.GG) = G.plGG D z := by
  unfold tauOf
  simp

theorem eq_tauOf (τ : D.what₂.Tau) (z : Bool × G.HH D) (h : (D.eTau τ : D.R.GG) = G.plGG D z) :
    τ = tauOf D z := by
  unfold tauOf
  rw [Equiv.eq_symm_apply]
  exact Subtype.ext h

theorem tau1_injective (φ : Formalism.HC.Frame) : Function.Injective φ.tau1 := by
  intro s t hst
  exact Multiplicative.ofAdd.injective (congrArg Prod.snd hst)

theorem doubling_injective (φ : Formalism.HC.Frame) : Function.Injective φ.tau2 := by
  intro s t hst
  exact Multiplicative.ofAdd.injective (congrArg Prod.snd hst)

theorem plGG_top_iff (z : Bool × G.HH D) : G.plGG D z ∈ D.host.topPlaces ↔ G.IsTopPl D z := by
  obtain ⟨b, t⟩ := z
  unfold G.IsTopPl Formalism.BasicNotions.Host.topPlaces
  cases b with
  | false =>
    simp only [plGG_false, Finset.mem_image, true_and]
    constructor
    · rintro ⟨s, hs, hst⟩
      rw [← tau1_injective D.R.toFrame hst]
      exact hs
    · intro h
      exact ⟨t, h, rfl⟩
  | true =>
    simp only [plGG_true, Finset.mem_image, Bool.true_eq_false, false_and, iff_false, not_exists, not_and]
    intro s _ hst
    have h1 : ((1 : ℤˣ), (1 : ℤˣ)) = ((-1 : ℤˣ), (1 : ℤˣ)) := congrArg Prod.fst hst
    have h2 : (1 : ℤˣ) = -1 := congrArg Prod.fst h1
    exact absurd (congrArg Units.val h2) (by norm_num)

theorem mem_thickPlaces (g : D.R.GG) :
    g ∈ D.host.thickPlaces ↔ ∃ s ∈ D.host.T2, D.R.tau2 (D.R.dig s + D.host.u0) = g := by
  unfold Formalism.BasicNotions.Host.thickPlaces
  rw [Finset.mem_image]

theorem plGG_thick_iff (z : Bool × G.HH D) : G.plGG D z ∈ D.host.thickPlaces ↔ G.IsThickPl D z := by
  obtain ⟨b, t⟩ := z
  unfold G.IsThickPl Formalism.BasicNotions.Host.thickPlaces
  cases b with
  | false =>
    simp only [plGG_false, Finset.mem_image, Bool.false_eq_true, false_and, iff_false, not_exists, not_and]
    intro s _ hst
    have h1 : ((-1 : ℤˣ), (1 : ℤˣ)) = ((1 : ℤˣ), (1 : ℤˣ)) := congrArg Prod.fst hst
    have h2 : (-1 : ℤˣ) = 1 := congrArg Prod.fst h1
    exact absurd (congrArg Units.val h2) (by norm_num)
  | true =>
    simp only [plGG_true, Finset.mem_image, true_and]
    constructor
    · rintro ⟨s, hs, hst⟩
      exact ⟨s, hs, doubling_injective D.R.toFrame hst⟩
    · rintro ⟨s, hs, hst⟩
      exact ⟨s, hs, by rw [hst]⟩

variable {D} (L : SizeData₂ D)

open Classical in

def offW (j : ℕ) (z : Bool × G.HH D) : ℝ :=
  if j ∈ SizeData₂.lifts D then
    wj D j (tauOf D z) - (if z.1 = false ∧ z.2 ∈ D.host.TT then (G.bL L z.2 : ℝ) else 0)
  else offC D L.sc j z

def instW (kapI : ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ) (ep : ℕ → ℕ) :
    G.Inst D L where
  bs := bsA
  bs_orb := bsA_orb
  bs_step := bsA_step
  off := offW L
  off_top := fun j z hz => by
    unfold offW
    by_cases hj : j ∈ SizeData₂.lifts D
    · have hj' := Finset.mem_Icc.1 hj
      have hz' : z.1 = false ∧ z.2 ∈ D.host.TT := hz

      have h0 : (D.eTau (tauOf D z) : D.R.GG) = D.R.tau1 z.2 := by
        rw [eTau_tauOf, ← plGG_false]
        congr 1
        exact Prod.ext hz'.1 rfl
      have h1 := L.win_top j hj'.1 hj'.2 (tauOf D z) ⟨z.2, hz'.2⟩ h0
      have h2 : G.bL L z.2 = L.bT ⟨z.2, hz'.2⟩ := by unfold G.bL; rw [dif_pos hz'.2]
      rw [if_pos hj, if_pos hz', h2]
      constructor <;> linarith [h1.1, h1.2]
    · rw [if_neg hj]
      exact (instC D L kapI ep).off_top j z hz
  off_thin := fun j z hz => by
    unfold offW
    by_cases hj : j ∈ SizeData₂.lifts D
    · have hj' := Finset.mem_Icc.1 hj
      have hz' : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) := hz.1
      have h1 := L.win_thin j hj'.1 hj'.2 (tauOf D z)
        (by
          rw [eTau_tauOf]
          exact ⟨plGG_mem_Psi D z, fun h => hz.1 ((plGG_top_iff D z).1 h), fun h => hz.2 ((plGG_thick_iff D z).1 h)⟩)
      rw [if_pos hj, if_neg hz', sub_zero]
      exact h1
    · rw [if_neg hj]
      exact (instC D L kapI ep).off_thin j z hz
  off_thick := fun j z hz => by
    have ht : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) := fun h => by
      have h1 := h.1
      rw [hz.1] at h1
      exact Bool.noConfusion h1
    unfold offW
    by_cases hj : j ∈ SizeData₂.lifts D
    · have hj' := Finset.mem_Icc.1 hj
      have h1 := L.win_thick j hj'.1 hj'.2 (tauOf D z) (by rw [eTau_tauOf]; exact (plGG_thick_iff D z).2 hz)
      rw [if_pos hj, if_neg ht, sub_zero]
      exact h1
    · rw [if_neg hj]
      exact (instC D L kapI ep).off_thick j z hz
  kapI := kapI
  ep := ep

theorem instW_fill (kapI : ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ) (ep : ℕ → ℕ) :
    ∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × G.HH D), (D.eTau τ : D.R.GG) = G.plGG D z →
      G.fill (instW L kapI ep) (G.bL L) j z = wj D j τ := by
  intro j hj τ z hτ
  have e := eq_tauOf D τ z hτ
  subst e
  simp only [G.fill, instW, offW, if_pos hj]
  split_ifs <;> ring

end InstW

section Comparison₂

variable {D : D7} (L0 : SizeData₂ D) (X0 : G.Inst D L0) (K : G.Consts)

theorem one_le_fill (hw : 1 ≤ L0.sc.w'' D.R.n) (j : ℕ) (z : Bool × G.HH D) :
    1 ≤ G.fill X0 (G.bL L0) j z := by
  have hs := scale_w''_le L0.sc D.R.n (ranks_one_le_n D.R)
  have hb' := scale_b'_nonneg L0.sc
  unfold G.fill
  by_cases htop : G.IsTopPl D z
  · have ho := (X0.off_top j z htop).1
    have hc : z.1 = false ∧ z.2 ∈ D.host.TT := htop
    rw [if_pos hc]
    have hbl : (0 : ℝ) ≤ (G.bL L0 z.2 : ℝ) := by
      unfold G.bL
      rw [dif_pos hc.2]
      exact hb'.trans (L0.bT_ge _)
    linarith [hs.1]
  · have hc : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) := htop
    rw [if_neg hc, zero_add]
    by_cases hthick : G.IsThickPl D z
    · linarith [(X0.off_thick j z hthick).1, hs.2]
    · linarith [(X0.off_thin j z ⟨htop, hthick⟩).1]

theorem TTP_subset (a b : G.HH D → ℤ) (p : ℕ) : ∀ t ∈ G.TTP X0 K a b p, t ∈ D.host.TT := by
  intro t ht
  unfold G.TTP at ht
  split at ht
  · exact ht
  · exact (Finset.mem_filter.1 ht).1

def belowSupp : Finset D.what₂.places.Pl := (finite_resChar_le D (L0.sc.X'' D.R.n)).toFinset

theorem mem_belowSupp (w : D.what₂.places.Pl) :
    w ∈ belowSupp L0 ↔ ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L0.sc.X'' D.R.n := by
  unfold belowSupp
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]

def specSupp (D : D7) : Finset D.what₂.places.Pl :=
  (finite_resChar_mem D {D.host.d, D.host.g 0, D.host.g 1}).toFinset

theorem mem_specSupp (w : D.what₂.places.Pl) :
    w ∈ specSupp D ↔ D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ) := by
  unfold specSupp
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]

open Classical in

def tieSupp : Finset D.what₂.places.Pl := belowSupp L0 ∪ specSupp D ∪ L0.supp

open Classical in
theorem mem_tieSupp (w : D.what₂.places.Pl) : w ∈ tieSupp L0 ↔
    ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L0.sc.X'' D.R.n ∨
      D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ) ∨ w ∈ L0.supp := by
  unfold tieSupp
  rw [Finset.mem_union, Finset.mem_union, mem_belowSupp, mem_specSupp, or_assoc]

theorem lt_of_not_mem_tieSupp (w : D.what₂.places.Pl) (h : w ∉ tieSupp L0) :
    L0.sc.X'' D.R.n < ((D.what₂.places.resChar w : ℕ) : ℝ) := by
  exact not_le.mp (fun h' => h ((mem_tieSupp L0 w).2 (Or.inl h')))

theorem Fval_off_tieSupp (j : ℕ) (w : D.what₂.places.Pl) (h : w ∉ tieSupp L0) : Fval L0 j w = 0 := by
  have hlt := lt_of_not_mem_tieSupp L0 w h
  have hns : D.what₂.places.resChar w ∉ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ) :=
    fun h' => h ((mem_tieSupp L0 w).2 (Or.inr (Or.inl h')))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hns
  have hg : D.what₂.places.resChar w ∉ L0.gTypes := by
    unfold Formalism.BasicNotions.SizeData₂.gTypes
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hns.2.1, hns.2.2⟩
  unfold Fval
  exact FvalP_above L0 j hlt hg hns.1

theorem VV_above (a b : G.HH D → ℤ) (p : ℕ) (h : L0.sc.X'' D.R.n < (p : ℝ)) : G.VV X0 K a b p = ∅ := by
  unfold G.VV
  rw [if_neg]
  rintro ⟨hc, -⟩
  unfold G.Cand at hc
  have := scale_X'_le_X'' L0.sc D.R.n (ranks_one_le_n D.R)
  linarith [hc.2.1]

theorem VV_eq_empty_of_not_isResidueClassZero (a b : G.HH D → ℤ) (p : ℕ) (h : ¬ G.IsResidueClassZero D p) : G.VV X0 K a b p = ∅ := by
  unfold G.VV
  rw [if_neg]
  rintro ⟨hc, -⟩
  unfold G.Cand at hc
  exact h hc.2.2.1

theorem tau_eq_zero_of_eq_empty (a b : G.HH D → ℤ) (p : ℕ) (h : G.VV X0 K a b p = ∅) : G.tauP X0 K a b p = 0 := by
  unfold G.tauP
  rw [if_pos h]

theorem ioP_eq_zero_of_VV_eq_empty (a b : G.HH D → ℤ) (p : ℕ) (h : G.VV X0 K a b p = ∅) : G.ioP X0 K a b p = 0 := by
  unfold G.ioP
  split
  · rename_i h'
    rw [h] at h'
    exact absurd h' Finset.not_nonempty_empty
  · rfl

theorem tauP_above (a b : G.HH D → ℤ) (p : ℕ) (h : L0.sc.X'' D.R.n < (p : ℝ)) : G.tauP X0 K a b p = 0 := by
  exact tau_eq_zero_of_eq_empty L0 X0 K a b p (VV_above L0 X0 K a b p h)

theorem ioP_eq_zero_of_lt (a b : G.HH D → ℤ) (p : ℕ) (h : L0.sc.X'' D.R.n < (p : ℝ)) : G.ioP X0 K a b p = 0 := by
  exact ioP_eq_zero_of_VV_eq_empty L0 X0 K a b p (VV_above L0 X0 K a b p h)

open Classical in

def tieWeightData (dr : Set ℕ) (len : D.what₂.Word → D.what₂.places.Pl → ℚ) (hw : 1 ≤ L0.sc.w'' D.R.n)
    (hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i)))
    (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0) : SizeData₂ D :=
  { L0 with
    supp := tieSupp L0
    gain := fun j w =>
      if w ∈ tieSupp L0 ∧ (G.IsResidueClassZero D (D.what₂.places.resChar w) ∨ G.IsSg D (D.what₂.places.resChar w)) then
        G.gainP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w) j else 0
    tau := fun w => G.tauP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w)
    io := fun w => G.ioP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w)
    gain_supp := fun j w h => if_neg (fun h' => h h'.1)
    F := fun j w => Fval L0 j w
    F_supp := fun j w h => Fval_off_tieSupp L0 j w h
    untwisted := fun w h j h1 h2 => ⟨(L0.untwisted w h j h1 h2).1, hu w h j h1 h2⟩
    F_conj := fun j w => Fval_conj L0 j w
    F_above := fun j _ h1 h2 h3 => FvalP_above L0 j h1 h2 h3
    E_supp := fun u j w h => L0.E_supp u j w (fun h' => h (Finset.mem_union_right _ h'))
    tau_supp := fun w h => tauP_above L0 X0 K _ _ _ (lt_of_not_mem_tieSupp L0 w h)
    io_supp := fun w h => ioP_eq_zero_of_lt L0 X0 K _ _ _ (lt_of_not_mem_tieSupp L0 w h)
    gain_g := fun j w h => if_neg (fun h' => by
      rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hg 0 (h ▸ h'.2)
      · exact hg 1 (h ▸ h'.2))
    not_inert := fun w h1 h2 =>
      ⟨fun j => if_neg (fun h' => h'.2.elim h2 h1), tau_eq_zero_of_eq_empty L0 X0 K _ _ _ (VV_eq_empty_of_not_isResidueClassZero L0 X0 K _ _ _ h2),
        ioP_eq_zero_of_VV_eq_empty L0 X0 K _ _ _ (VV_eq_empty_of_not_isResidueClassZero L0 X0 K _ _ _ h2)⟩
    drop := {p | p ∈ dr ∧ ∀ u, p ≠ (D.mem u).A.T}
    drop_alt := fun u h => h.2 u rfl
    LaG := G.La K L0.sc
    TTw := fun w => (G.TTP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w)).subtype (· ∈ D.host.TT)
    TTw_full := fun w h => by

      ext t
      simp only [Finset.mem_subtype, Finset.mem_univ, iff_true]
      unfold G.TTP
      rw [if_pos h]
      exact t.2
    wPart := fun j t p e => G.fill X0 (G.bL L0) j (G.partner D p t e)
    wPart_ge := fun j t p e => one_le_fill L0 X0 hw j _
    lenMN := len }

variable (dr : Set ℕ) (len : D.what₂.Word → D.what₂.places.Pl → ℚ) (hw : 1 ≤ L0.sc.w'' D.R.n)
    (hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i)))
    (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0)

def tieInst : G.Inst D (tieWeightData L0 X0 K dr len hw hg hu) where
  bs := X0.bs
  bs_orb := X0.bs_orb
  bs_step := X0.bs_step
  off := X0.off
  off_top := X0.off_top
  off_thin := X0.off_thin
  off_thick := X0.off_thick
  kapI := X0.kapI
  ep := X0.ep

theorem tie_supp_sat (w : D.what₂.places.Pl)
    (h : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ (tieWeightData L0 X0 K dr len hw hg hu).sc.X'' D.R.n) :
    w ∈ (tieWeightData L0 X0 K dr len hw hg hu).supp := by
  exact (mem_tieSupp L0 w).2 (Or.inl h)

theorem tie_supp_old (w : D.what₂.places.Pl) (h : w ∈ L0.supp) : w ∈ (tieWeightData L0 X0 K dr len hw hg hu).supp := by
  exact (mem_tieSupp L0 w).2 (Or.inr (Or.inr h))

theorem tie_FDef : (tieWeightData L0 X0 K dr len hw hg hu).FDef := by
  intro j _ w
  rfl

theorem tie_fills
    (hf : ∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × G.HH D),
      (D.eTau τ : D.R.GG) = G.plGG D z → G.fill X0 (G.bL L0) j z = wj D j τ)
    (w : D.what₂.places.Pl) :
    G.ParametersFill (tieInst L0 X0 K dr len hw hg hu) K w := by
  unfold G.ParametersFill
  intro p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hf
  · intro j t e
    rfl
  · dsimp only [tieWeightData]
    rw [Finset.subtype_map, Finset.filter_true_of_mem (TTP_subset L0 X0 K _ _ _)]
    rfl
  · intro h1 h2 j _
    dsimp only [tieWeightData]
    split
    · rfl
    · rename_i hc
      exact (hc ⟨h1, h2⟩).elim
  · rfl
  · rfl
  · rfl

end Comparison₂

end Formalism.MainNotions.Inhab

end
