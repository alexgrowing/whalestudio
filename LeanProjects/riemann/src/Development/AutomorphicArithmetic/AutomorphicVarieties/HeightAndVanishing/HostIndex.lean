import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Mathlib

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem index_inf_dvd_index_mul_index_of_commGroup {G : Type*} [CommGroup G] (A B : Subgroup G) :
    (A ⊓ B).index ∣ A.index * B.index := by
  have h := Subgroup.relIndex_inf_mul_relIndex A B ⊤
  rw [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h
  rw [← h]
  exact Nat.mul_dvd_mul_right (Subgroup.relIndex_dvd_index_of_normal _ _) _

private theorem index_comap_dvd_index_of_commGroup {G G' : Type*} [CommGroup G] [Group G'] (A : Subgroup G) (f : G' →* G) :
    (A.comap f).index ∣ A.index := by
  rw [Subgroup.index_comap]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

private theorem index_range_sq_units_zmod_prime_dvd_two (p : ℕ) (hp : p.Prime) :
    ((powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range).index ∣ 2 := by
  haveI := Fact.mk hp
  set S := (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range
  haveI : IsCyclic ((ZMod p)ˣ ⧸ S) :=
    isCyclic_of_surjective (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S)
  have hcard : Nat.card ((ZMod p)ˣ ⧸ S) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    induction g using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨x, rfl⟩
  exact hcard

private theorem index_zpowers_neg_one_units_zmod_two_pow_dvd (e : ℕ) :
    (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)).index ∣ 2 ^ e := by
  have h4 : 2 ^ 2 ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : Fact (1 < 2 ^ (e + 2)) := ⟨by omega⟩
  have h := Subgroup.index_mul_card (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
  rw [Nat.card_zpowers, ← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one,
    ZMod.ringChar_zmod_n, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ Nat.prime_two, if_neg (by omega)] at h
  have h' : 2 ^ (e + 1) * (2 - 1) = 2 ^ e * 2 := by ring
  rw [h'] at h
  rw [Nat.eq_of_mul_eq_mul_right (by norm_num) h]

private theorem index_ker_toUnitHom_dvd_orderOf_dirichletCharacter (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) :
    (MulChar.toUnitHom χ).ker.index ∣ orderOf χ := by
  rw [Subgroup.index_ker]
  haveI : IsCyclic (MulChar.toUnitHom χ).range := inferInstance
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
  obtain ⟨_, u, rfl⟩ := x
  apply Subtype.ext
  apply Units.ext
  have ho : orderOf χ ≠ 0 := (orderOf_pos χ).ne'
  simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom,
    OneMemClass.coe_one, Units.val_one]
  rw [← MulChar.pow_apply' χ ho, pow_orderOf_eq_one, MulChar.one_apply_coe]

private theorem orderOf_dirichletCharacter_le_level (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) : orderOf χ ≤ n := by
  have hpos : 0 < n.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have h1 : χ ^ n.totient = 1 := by
    ext u
    rw [MulChar.pow_apply' χ hpos.ne', ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient,
      Units.val_one, map_one, MulChar.one_apply_coe]
  exact (Nat.le_of_dvd hpos (orderOf_dvd_of_pow_eq_one h1)).trans (Nat.totient_le n)

theorem UpperTheory.V.HV.hostIndex :
    ∀ h : Host, h.H.index ∣ 2 ^ (h.ex + 2) * h.o ∧ h.H.index ≤ h.N ∧ 16 ∣ h.N ∧ 0 < h.o ∧ h.o ≤ h.q ∧
      (∀ p, p.Prime → (p ∣ h.N ↔ p = 2 ∨ p ∣ h.q ∨ p = h.q1 ∨ p = h.d)) ∧
      (∀ p, p.Prime → p ≠ 2 → p ≠ h.q1 → p ≠ h.d → ordProj[p] h.N = ordProj[p] h.q) ∧ ordProj[h.q1] h.N = h.q1 ∧ ordProj[h.d] h.N = h.d ∧
      ∀ u : (ZMod h.N)ˣ, u ^ (2 ^ (h.ex + 1) * h.o) ∈ h.H := by
  intro h
  obtain ⟨hq1, hq1m, hd, hdm, hcop⟩ := h.pair
  haveI := h.chi.ne
  have hq0 : h.q ≠ 0 := NeZero.ne _
  have hq12 : h.q1 ≠ 2 := by intro e; omega
  have hd2 : h.d ≠ 2 := by intro e; omega
  have hq1d : h.q1 ≠ h.d := by intro e; omega
  have cq1 : ¬ h.q1 ∣ h.q := fun hdv => hq1.one_lt.ne'
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) hcop) hdv)
  have cd : ¬ h.d ∣ h.q := fun hdv => hd.one_lt.ne'
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) hcop) hdv)
  have hN : h.N = (2 ^ (h.ex + 2)).lcm h.q * (h.q1 * h.d) := rfl
  have hN0 : h.N ≠ 0 := by
    rw [hN]
    exact Nat.mul_ne_zero (Nat.lcm_ne_zero (by positivity) hq0) (Nat.mul_ne_zero hq1.ne_zero hd.ne_zero)
  haveI : NeZero h.N := ⟨hN0⟩
  have hfac : ∀ p, p.Prime → h.N.factorization p =
      max ((h.ex + 2) * (if p = 2 then 1 else 0)) (h.q.factorization p) +
        ((if p = h.q1 then 1 else 0) + (if p = h.d then 1 else 0)) := by
    intro p hp
    rw [hN, Nat.factorization_mul (Nat.lcm_ne_zero (by positivity) hq0)
        (Nat.mul_ne_zero hq1.ne_zero hd.ne_zero),
      Nat.factorization_lcm (by positivity) hq0, Nat.factorization_mul hq1.ne_zero hd.ne_zero,
      Nat.factorization_pow, Nat.prime_two.factorization, hq1.factorization, hd.factorization]
    simp [Finsupp.single_apply, eq_comm]
    split_ifs <;> simp
  have fq1 : h.q.factorization h.q1 = 0 := Nat.factorization_eq_zero_of_not_dvd cq1
  have fd : h.q.factorization h.d = 0 := Nat.factorization_eq_zero_of_not_dvd cd
  have hdiv : h.H.index ∣ 2 ^ (h.ex + 2) * h.o := by
    have i1 := index_comap_dvd_index_of_commGroup (Subgroup.zpowers (-1 : (ZMod (2 ^ (h.ex + 2)))ˣ))
      (ZMod.unitsMap (Host.two_pow_dvd h))
    have i2 := index_comap_dvd_index_of_commGroup (MulChar.toUnitHom h.chi.χ).ker (ZMod.unitsMap (Host.q_dvd h))
    have i3 := index_comap_dvd_index_of_commGroup (powMonoidHom 2 : (ZMod h.q1)ˣ →* (ZMod h.q1)ˣ).range
      (ZMod.unitsMap (Host.host_q1_dvd_N h))
    have i4 := index_comap_dvd_index_of_commGroup (powMonoidHom 2 : (ZMod h.d)ˣ →* (ZMod h.d)ˣ).range
      (ZMod.unitsMap (Host.d_dvd h))
    have j1 := i1.trans (index_zpowers_neg_one_units_zmod_two_pow_dvd h.ex)
    have j2 := i2.trans (index_ker_toUnitHom_dvd_orderOf_dirichletCharacter h.chi.N h.chi.χ)
    have j3 := i3.trans (index_range_sq_units_zmod_prime_dvd_two h.q1 hq1)
    have j4 := i4.trans (index_range_sq_units_zmod_prime_dvd_two h.d hd)
    have k := ((((index_inf_dvd_index_mul_index_of_commGroup _ _).trans (Nat.mul_dvd_mul_right
      ((index_inf_dvd_index_mul_index_of_commGroup _ _).trans (Nat.mul_dvd_mul_right
        ((index_inf_dvd_index_mul_index_of_commGroup _ _).trans (Nat.mul_dvd_mul j1 j2)) _)) _))).trans
      (Nat.mul_dvd_mul (Nat.mul_dvd_mul (dvd_refl _) j3) j4))
    have e : 2 ^ h.ex * orderOf h.chi.χ * 2 * 2 = 2 ^ (h.ex + 2) * h.o := by
      simp only [Host.o, ordC]
      ring
    rw [← e]
    exact k
  refine ⟨hdiv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : h.H.index ∣ h.N.totient := by
      have := Subgroup.index_dvd_card h.H
      rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at this
    exact (Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)) hc).trans (Nat.totient_le _)
  · rw [hN]
    exact (Nat.pow_dvd_pow 2 (by have := h.two_le; omega : 4 ≤ h.ex + 2)).trans
      ((Nat.dvd_lcm_left _ _).trans (dvd_mul_right _ _))
  · exact orderOf_pos _
  · exact orderOf_dirichletCharacter_le_level _ _
  · intro p hp
    rw [hp.dvd_iff_one_le_factorization hN0, hp.dvd_iff_one_le_factorization hq0, hfac p hp]
    by_cases e2 : p = 2 <;> by_cases e3 : p = h.q1 <;> by_cases e4 : p = h.d <;>
      simp [e2, e3, e4] <;> omega
  · intro p hp h2 h3 h4
    rw [hfac p hp]
    simp [h2, h3, h4]
  · rw [hfac _ hq1, fq1]
    simp [hq12, hq1d]
  · rw [hfac _ hd, fd]
    simp [hd2, hq1d.symm]
  · intro u
    have sq : ∀ (n : ℕ) (w : (ZMod n)ˣ),
        w ^ (2 ^ (h.ex + 1) * h.o) ∈ (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range := by
      intro n w
      refine ⟨w ^ (2 ^ h.ex * h.o), ?_⟩
      rw [powMonoidHom_apply, ← pow_mul]
      congr 1
      ring
    simp only [Host.H, Subgroup.mem_inf, Subgroup.mem_comap, map_pow]
    refine ⟨⟨⟨?_, ?_⟩, sq _ _⟩, sq _ _⟩
    · have ht : (2 ^ (h.ex + 2)).totient = 2 ^ (h.ex + 1) := by
        rw [Nat.totient_prime_pow_succ Nat.prime_two]
        simp
      rw [pow_mul, ← ht, ZMod.pow_totient, one_pow]
      exact Subgroup.one_mem _
    · rw [MonoidHom.mem_ker, map_pow]
      have h1 : (MulChar.toUnitHom h.chi.χ) (ZMod.unitsMap (Host.q_dvd h) u) ^ h.o = 1 := by
        apply Units.ext
        have ho : orderOf h.chi.χ ≠ 0 := (orderOf_pos _).ne'
        rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one]
        simp only [Host.o, ordC]
        rw [← MulChar.pow_apply' _ ho, pow_orderOf_eq_one, MulChar.one_apply_coe]
      rw [mul_comm, pow_mul, h1, one_pow]
