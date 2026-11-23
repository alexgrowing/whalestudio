import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField

noncomputable section

namespace GlobalTheory.TupleCone

open Polynomial

section Saturation

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

def saturation (x : B) (hx : IsIntegral A x) : Subring B where
  carrier := {b | ∃ n : ℕ, IsIntegral A (b * x ^ n)}
  zero_mem' := ⟨0, by simpa using isIntegral_zero⟩
  one_mem' := ⟨0, by simpa using isIntegral_one⟩
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := (hn.mul (hx.pow m)).add (hm.mul (hx.pow n))
    convert this using 1
    ring
  mul_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := hn.mul hm
    convert this using 1
    ring
  neg_mem' := by
    rintro a ⟨n, hn⟩
    exact ⟨n, by simpa using hn.neg⟩

theorem mem_saturation_of_isIntegral {x : B} (hx : IsIntegral A x) {b : B}
    (hb : IsIntegral (saturation x hx) b) : b ∈ saturation x hx := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · rw [Subsingleton.elim b 0]
    exact zero_mem _
  obtain ⟨p, hp, hz⟩ := hb
  have hr : ∀ r : saturation x hx, ∃ n : ℕ, IsIntegral A ((r : B) * x ^ n) := fun r => r.2
  choose n hn using hr
  let N := p.support.sup fun i => n (p.coeff i)
  have hN : ∀ i k, k ≠ 0 → IsIntegral A ((p.coeff i : B) * (x ^ N) ^ k) := by
    intro i k hk
    by_cases hi : i ∈ p.support
    · have h1 : n (p.coeff i) ≤ N * k :=
        (Finset.le_sup (f := fun i => n (p.coeff i)) hi).trans
          (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk))
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
      rw [← pow_mul, hd, pow_add, ← mul_assoc]
      exact (hn _).mul (hx.pow _)
    · rw [notMem_support_iff.mp hi, ZeroMemClass.coe_zero, zero_mul]
      exact isIntegral_zero
  let q := p.map (algebraMap (saturation x hx) B)
  have hq : q.Monic := hp.map _
  have hqz : q.eval b = 0 := by rw [eval_map, hz]
  have hq0 : q.natDegree ≠ 0 := by
    intro h
    rw [hq.natDegree_eq_zero.mp h] at hqz
    simp at hqz
  refine ⟨N, IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := q.scaleRoots (x ^ N))
    ((monic_scaleRoots_iff _).mpr hq) (by rwa [natDegree_scaleRoots]) ?_ fun i => ?_⟩
  · rw [mul_comm, scaleRoots_eval_mul, hqz, mul_zero]
    exact isIntegral_zero
  · rw [coeff_scaleRoots]
    rcases lt_trichotomy i q.natDegree with h | rfl | h
    · rw [coeff_map]
      exact hN _ _ (by omega)
    · simpa [hq.coeff_natDegree] using isIntegral_one
    · simpa [coeff_eq_zero_of_natDegree_lt h] using isIntegral_zero

end Saturation

variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)

def cone : Subalgebra o L[X] := Algebra.adjoin o (Set.range fun s => C (t s) * X)

def ratioRing (i : σ) : Subalgebra o L := Algebra.adjoin o (Set.range fun k => t k / t i)

def piece (n : ℕ) : Submodule o L where
  carrier := {a | IsIntegral (cone o t) (C a * X ^ n)}
  zero_mem' := by simpa using isIntegral_zero
  add_mem' := by
    intro a b ha hb
    simpa [add_mul] using IsIntegral.add ha hb
  smul_mem' := by
    intro c a ha
    have h := (isIntegral_algebraMap (R := cone o t) (A := L[X]) (x := algebraMap o _ c)).mul ha
    change IsIntegral _ _
    rw [Algebra.smul_def, map_mul, mul_assoc]
    exact h

variable {o t}

theorem mem_piece {n : ℕ} {a : L} : a ∈ piece o t n ↔ IsIntegral (cone o t) (C a * X ^ n) := Iff.rfl

theorem C_mul_X_mem_cone (s : σ) : C (t s) * X ∈ cone o t := Algebra.subset_adjoin ⟨s, rfl⟩

theorem mul_mem_piece {m n : ℕ} {a b : L} (ha : a ∈ piece o t m) (hb : b ∈ piece o t n) :
    a * b ∈ piece o t (m + n) := by
  have h := IsIntegral.mul ha hb
  rwa [mem_piece, map_mul, pow_add, mul_mul_mul_comm]

theorem piece_mul_le (m n : ℕ) : piece o t m * piece o t n ≤ piece o t (m + n) :=
  Submodule.mul_le.mpr fun _ ha _ hb => mul_mem_piece ha hb

theorem mem_piece_one (s : σ) : t s ∈ piece o t 1 := by
  rw [mem_piece, pow_one]
  exact isIntegral_algebraMap (x := (⟨_, C_mul_X_mem_cone s⟩ : cone o t))

theorem one_mem_piece_zero : (1 : L) ∈ piece o t 0 := by
  simpa [mem_piece] using isIntegral_one

theorem span_pow_le_piece (n : ℕ) : Submodule.span o (Set.range t) ^ n ≤ piece o t n := by
  induction n with
  | zero => rw [pow_zero, Submodule.one_le]; exact one_mem_piece_zero
  | succ n ih =>
    rw [pow_succ]
    refine (mul_le_mul' ih (Submodule.span_le.mpr ?_)).trans (piece_mul_le n 1)
    rintro _ ⟨s, rfl⟩
    exact mem_piece_one s

theorem pow_mem_piece (s : σ) (n : ℕ) : t s ^ n ∈ piece o t n :=
  span_pow_le_piece n (Submodule.pow_mem_pow _ (Submodule.subset_span (Set.mem_range_self s)) n)

theorem coeff_mem_span_pow {p : L[X]} (hp : p ∈ cone o t) (n : ℕ) :
    p.coeff n ∈ Submodule.span o (Set.range t) ^ n := by
  induction hp using Algebra.adjoin_induction generalizing n with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [coeff_C_mul, coeff_X]
    split_ifs with h
    · subst h
      simpa using Submodule.subset_span (R := o) (Set.mem_range_self (f := t) s)
    · simp
  | algebraMap r =>
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      simp
    · simp
  | add x y _ _ hx hy => rw [coeff_add]; exact add_mem (hx n) (hy n)
  | mul x y _ _ hx hy =>
    rw [coeff_mul]
    refine Submodule.sum_mem _ fun c hc => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hc, pow_add]
    exact Submodule.mul_mem_mul (hx _) (hy _)

def spread (L : Type*) [CommRing L] : L[X] →+* L[X][X] :=
  eval₂RingHom (C.comp C) (C X * X)

theorem coeff_spread {L : Type*} [CommRing L] (p : L[X]) (n : ℕ) :
    (spread L p).coeff n = C (p.coeff n) * X ^ n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, add_mul]
  | monomial m a =>
    rw [spread, coe_eval₂RingHom, eval₂_monomial, mul_pow, ← C_pow, RingHom.comp_apply,
      ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, coeff_monomial]
    by_cases h : n = m
    · simp [h]
    · simp [h, Ne.symm h]

theorem isIntegral_cone_iff {p : L[X]} :
    IsIntegral (cone o t) p ↔ ∀ n, p.coeff n ∈ piece o t n := by
  constructor
  · intro hp n
    have h1 : ∀ s : cone o t, spread L s ∈ (mapRingHom (algebraMap (cone o t) L[X])).range := by
      rintro ⟨s, hs⟩
      induction hs using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        refine ⟨C ⟨_, C_mul_X_mem_cone s⟩ * X, ?_⟩
        simp [spread, mul_assoc]
      | algebraMap r =>
        refine ⟨C (algebraMap o _ r), ?_⟩
        simp [spread]
      | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
      | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy
    choose φ hφ using h1
    have hinj : Function.Injective (mapRingHom (algebraMap (cone o t) L[X])) :=
      Polynomial.map_injective _ Subtype.val_injective
    let ψ : cone o t →+* (cone o t)[X] :=
      { toFun := φ
        map_one' := hinj (by rw [hφ, map_one]; exact map_one _)
        map_zero' := hinj (by rw [hφ, map_zero]; exact map_zero _)
        map_add' := fun a b => hinj (by rw [map_add, hφ, hφ, hφ]; exact map_add _ _ _)
        map_mul' := fun a b => hinj (by rw [map_mul, hφ, hφ, hφ]; exact map_mul _ _ _) }
    letI : Algebra (cone o t)[X] L[X][X] := Polynomial.algebra _ _
    have h2 : IsIntegral (cone o t)[X] (spread L p) :=
      hp.map_of_comp_eq ψ (spread L) (RingHom.ext fun s => hφ s)
    rw [mem_piece, ← coeff_spread]
    exact Polynomial.isIntegral_iff_isIntegral_coeff.mp h2 n
  · intro h
    rw [p.as_sum_support_C_mul_X_pow]
    exact IsIntegral.sum _ fun n _ => h n

theorem piece_zero : piece o t 0 = (integralClosure o L).toSubmodule := by
  ext a
  rw [mem_piece, pow_zero, mul_one, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
  constructor
  · intro h
    have h1 : ∀ s : cone o t, ((evalRingHom 0).comp (algebraMap (cone o t) L[X])) s ∈
        (⊥ : Subalgebra o L) := fun s => by
      have := coeff_mem_span_pow s.2 0
      rw [pow_zero, Submodule.mem_one, coeff_zero_eq_eval_zero] at this
      exact Algebra.mem_bot.mpr this
    have h2 : IsIntegral (⊥ : Subalgebra o L) (evalRingHom 0 (C a)) :=
      h.map_of_comp_eq (RingHom.codRestrict _ _ h1) (evalRingHom 0) rfl
    rw [coe_evalRingHom, eval_C] at h2
    haveI : Algebra.IsIntegral o (⊥ : Subalgebra o L) := inferInstance
    exact isIntegral_trans a h2
  · intro h
    exact (h.map (CAlgHom (R := o) (A := L))).tower_top

theorem isIntegral_div_of_mem_piece (i : σ) {n : ℕ} {a : L} (ha : a ∈ piece o t n) :
    IsIntegral (ratioRing o t i) (a / t i ^ n) := by
  have h1 : ∀ s : cone o t, ((evalRingHom (t i)⁻¹).comp (algebraMap (cone o t) L[X])) s ∈
      ratioRing o t i := by
    rintro ⟨s, hs⟩
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact Algebra.subset_adjoin ⟨s, by simp [div_eq_mul_inv]⟩
    | algebraMap r => simpa using (ratioRing o t i).algebraMap_mem r
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | mul x y _ _ hx hy => simpa using mul_mem hx hy
  have h2 : IsIntegral (ratioRing o t i) (evalRingHom (t i)⁻¹ (C a * X ^ n)) :=
    IsIntegral.map_of_comp_eq (RingHom.codRestrict _ _ h1) (evalRingHom _) rfl ha
  simpa [div_eq_mul_inv] using h2

theorem isIntegral_ratioRing_iff {i : σ} (hi : t i ≠ 0) {f : L} :
    IsIntegral (ratioRing o t i) f ↔ ∃ n, f * t i ^ n ∈ piece o t n := by
  constructor
  · intro hf
    have hx : IsIntegral (cone o t) (C (t i) * X) :=
      isIntegral_algebraMap (x := (⟨_, C_mul_X_mem_cone i⟩ : cone o t))
    have h1 : ∀ s : ratioRing o t i, (C.comp (algebraMap (ratioRing o t i) L)) s ∈
        saturation _ hx := by
      rintro ⟨s, hs⟩
      induction hs using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        refine ⟨1, ?_⟩
        have := mem_piece_one (o := o) (t := t) s
        rw [mem_piece, pow_one] at this
        change IsIntegral _ (C (t s / t i) * _)
        rwa [pow_one, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hi]
      | algebraMap r =>
        refine ⟨0, ?_⟩
        rw [pow_zero, mul_one]
        exact isIntegral_algebraMap (x := algebraMap o (cone o t) r)
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | mul x y _ _ hx hy => simpa using mul_mem hx hy
    obtain ⟨n, hn⟩ := mem_saturation_of_isIntegral hx
      (hf.map_of_comp_eq (RingHom.codRestrict _ _ h1) C rfl)
    refine ⟨n, ?_⟩
    rwa [mem_piece, map_mul, map_pow, mul_assoc, ← mul_pow]
  · rintro ⟨n, hn⟩
    simpa [hi] using isIntegral_div_of_mem_piece i hn

section Finite

variable (o t) [IsDedekindDomain o] [CharZero L] [Algebra.EssFiniteType o L] [Finite σ]

theorem finite_integralClosure_cone :
    Module.Finite (cone o t) (integralClosure (cone o t) L[X]) := by
  haveI : Algebra.FiniteType o (cone o t) := .adjoin_of_finite (Set.finite_range _)
  haveI : Algebra.EssFiniteType o L[X] := .comp o L _
  haveI : Algebra.EssFiniteType (cone o t) L[X] := .of_comp o _ _
  exact finite_integralClosure_of_essFiniteType_of_isReduced o _ _

theorem exists_generators : ∃ e : ℕ, 0 < e ∧ ∃ N : ℕ → Submodule o L, (∀ q, (N q).FG) ∧
    (∀ q, N q ≤ piece o t q) ∧ (∀ q, e < q → N q = ⊥) ∧ ∀ n, piece o t n ≤
      ⨆ c ∈ Finset.HasAntidiagonal.antidiagonal n, Submodule.span o (Set.range t) ^ c.1 * N c.2 := by
  classical
  obtain ⟨G, hG⟩ := (finite_integralClosure_cone o t).fg_top
  let N : ℕ → Submodule o L := fun q => Submodule.span o
    ((fun g : integralClosure (cone o t) L[X] => (g : L[X]).coeff q) '' G)
  refine ⟨G.sup (fun g => g.1.natDegree) + 1, Nat.succ_pos _, N,
    fun q => Submodule.fg_span (G.finite_toSet.image _), fun q => Submodule.span_le.mpr ?_,
    fun q hq => Submodule.span_eq_bot.mpr ?_, fun n a ha => ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact isIntegral_cone_iff.mp g.2 q
  · rintro _ ⟨g, hg, rfl⟩
    have := Finset.le_sup (f := fun g : integralClosure (cone o t) L[X] => (g : L[X]).natDegree) hg
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  · have key : ∀ p ∈ Submodule.span (cone o t) (G : Set (integralClosure (cone o t) L[X])), ∀ n,
        (p : L[X]).coeff n ∈
          ⨆ c ∈ Finset.HasAntidiagonal.antidiagonal n, Submodule.span o (Set.range t) ^ c.1 * N c.2 := by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem g hg =>
        intro n
        refine Submodule.mem_iSup_of_mem (0, n) (Submodule.mem_iSup_of_mem (by simp) ?_)
        rw [pow_zero, one_mul]
        exact Submodule.subset_span ⟨g, hg, rfl⟩
      | zero => intro n; simp
      | add x y _ _ hx hy => intro n; simpa using add_mem (hx n) (hy n)
      | smul s x _ hx =>
        intro n
        change ((s : L[X]) * (x : L[X])).coeff n ∈ _
        rw [coeff_mul]
        refine Submodule.sum_mem _ fun d hd => ?_
        refine SetLike.le_def.mp ?_ (Submodule.mul_mem_mul (coeff_mem_span_pow s.2 d.1) (hx d.2))
        rw [Submodule.mul_iSup]
        refine iSup_le fun c => ?_
        rw [Submodule.mul_iSup]
        refine iSup_le fun hc => ?_
        rw [← mul_assoc, ← pow_add]
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hc hd
        exact le_iSup₂_of_le (d.1 + c.1, c.2) (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) le_rfl
    simpa using key ⟨_, ha⟩ (hG ▸ Submodule.mem_top) n

theorem piece_fg (n : ℕ) : (piece o t n).FG := by
  obtain ⟨e, -, N, hN, -, -, h⟩ := exists_generators o t
  refine Submodule.FG.of_le (Submodule.fg_biSup _ _ fun c _ => ?_) (h n)
  exact ((Submodule.fg_span (Set.finite_range t)).pow _).mul (hN _)

theorem exists_spanning_tuple (e : ℕ) : ∃ (M : ℕ) (z : Fin (M + 1) → L) (c : σ → Fin (M + 1)),
    Submodule.span o (Set.range z) = piece o t e ∧ ∀ j, z (c j) = t j ^ e := by
  classical
  obtain ⟨G, hG⟩ := piece_fg o t e
  have hfin : (insert 0 ((G : Set L) ∪ Set.range fun j => t j ^ e)).Finite :=
    (G.finite_toSet.union (Set.finite_range _)).insert _
  obtain ⟨n, z, -, hz⟩ := hfin.fin_param
  obtain ⟨k, -⟩ : (0 : L) ∈ Set.range z := hz ▸ Set.mem_insert _ _
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by have := k.2; omega⟩
  have hc : ∀ j, ∃ k, z k = t j ^ e := fun j =>
    show _ ∈ Set.range z from hz ▸ Set.mem_insert_of_mem _ (Or.inr ⟨j, rfl⟩)
  choose c hc using hc
  refine ⟨M, z, c, ?_, hc⟩
  rw [hz, Submodule.span_insert_zero, Submodule.span_union, hG, sup_eq_left, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact pow_mem_piece j e

theorem exists_piece_succ_eq : ∃ e : ℕ, 0 < e ∧ ∀ d, e ≤ d →
    piece o t (d + 1) = Submodule.span o (Set.range t) * piece o t d := by
  obtain ⟨e, he, N, -, hN, hN', h⟩ := exists_generators o t
  refine ⟨e, he, fun d hd => le_antisymm ((h _).trans (iSup₂_le fun c hc => ?_)) ?_⟩
  · rw [Finset.HasAntidiagonal.mem_antidiagonal] at hc
    by_cases hq : e < c.2
    · rw [hN' _ hq, Submodule.mul_bot]
      exact bot_le
    · obtain ⟨m, hm⟩ : ∃ m, c.1 = m + 1 := ⟨c.1 - 1, by omega⟩
      rw [hm, pow_succ', mul_assoc, show d = m + c.2 by omega]
      exact mul_le_mul' le_rfl
        ((mul_le_mul' (span_pow_le_piece m) (hN _)).trans (piece_mul_le _ _))
  · rw [add_comm]
    exact (mul_le_mul' (by simpa using span_pow_le_piece 1) le_rfl).trans
      (piece_mul_le 1 d)

theorem exists_piece_mul_eq_pow : ∃ e : ℕ, 0 < e ∧ ∀ j, 0 < j →
    piece o t (j * e) = piece o t e ^ j := by
  obtain ⟨e, he, h⟩ := exists_piece_succ_eq o t
  have h1 : ∀ d, e ≤ d → ∀ m,
      piece o t (d + m) = Submodule.span o (Set.range t) ^ m * piece o t d := by
    intro d hd m
    induction m with
    | zero => simp
    | succ m ih => rw [← add_assoc, h _ (by omega), ih, pow_succ', mul_assoc]
  refine ⟨e, he, fun j hj => ?_⟩
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [pow_succ', ← ih, Nat.succ_mul]
    refine le_antisymm ?_ ((piece_mul_le _ _).trans (add_comm e _ ▸ le_rfl))
    rw [h1 _ (Nat.le_mul_of_pos_left e hj)]
    exact mul_le_mul' (span_pow_le_piece e) le_rfl

end Finite

theorem isIntegral_ratioRing_iff_mem_adjoin {τ : Type*} {z : τ → L} {e : ℕ} (he : 0 < e)
    (hz : Submodule.span o (Set.range z) = piece o t e)
    (hv : ∀ j, 0 < j → piece o t (j * e) = piece o t e ^ j) {i : σ} (hi : t i ≠ 0) {f : L} :
    IsIntegral (ratioRing o t i) f ↔
      f ∈ Algebra.adjoin o (Set.range fun k => z k / t i ^ e) := by
  constructor
  · intro hf
    obtain ⟨n, hn⟩ := (isIntegral_ratioRing_iff hi).mp hf
    obtain ⟨m, hm⟩ : ∃ m, (n + 1) * e = n + m :=
      Nat.exists_eq_add_of_le ((Nat.le_succ n).trans (Nat.le_mul_of_pos_right _ he))
    have h1 := mul_mem_piece hn (pow_mem_piece i m)
    rw [mul_assoc, ← pow_add, ← hm, hv _ n.succ_pos, ← hz] at h1
    have key : ∀ j, ∀ a ∈ Submodule.span o (Set.range z) ^ j,
        a / t i ^ (j * e) ∈ Algebra.adjoin o (Set.range fun k => z k / t i ^ e) := by
      intro j a ha
      induction ha using Submodule.pow_induction_on_left' with
      | algebraMap r => simpa using Subalgebra.algebraMap_mem _ r
      | add x y i hx hy ihx ihy => rw [add_div]; exact add_mem ihx ihy
      | mem_mul m hm j x hx ih =>
        rw [Nat.succ_mul, pow_add, mul_comm (t i ^ _), mul_div_mul_comm]
        refine mul_mem ?_ ih
        clear ih hx
        induction hm using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨k, rfl⟩ := hx
          exact Algebra.subset_adjoin ⟨k, rfl⟩
        | zero => simp
        | add x y _ _ hx hy => rw [add_div]; exact add_mem hx hy
        | smul c x _ hx => rw [smul_div_assoc]; exact Subalgebra.smul_mem _ hx c
    simpa [hi] using key _ _ h1
  · intro hf
    have h : Algebra.adjoin o (Set.range fun k => z k / t i ^ e) ≤
        (integralClosure (ratioRing o t i) L).restrictScalars o := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨k, rfl⟩
      exact isIntegral_div_of_mem_piece i (hz ▸ Submodule.subset_span ⟨k, rfl⟩)
    exact h hf

end GlobalTheory.TupleCone
