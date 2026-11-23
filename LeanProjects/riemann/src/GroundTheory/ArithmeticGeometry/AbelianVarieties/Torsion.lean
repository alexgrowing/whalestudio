import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KernelCard

namespace GroundTheory.Arith.Abelian

open AddSubgroup

section Group

variable {A : Type*} [AddCommGroup A]

theorem exists_addOrderOf_eq_of_card {n : ℕ} (hn : 0 < n) (hA : ∀ a : A, n • a = 0)
    (hcard : Nat.card A = n ^ 2)
    (hker : ∀ m, m ∣ n → Nat.card {a : A // m • a = 0} ≤ m ^ 2) :
    ∃ P : A, addOrderOf P = n := by
  have hex : AddMonoid.ExponentExists A := ⟨n, hn, hA⟩
  obtain ⟨P, hP⟩ := AddMonoid.exists_addOrderOf_eq_exponent hex
  refine ⟨P, hP.trans ?_⟩
  have he : AddMonoid.exponent A ∣ n := AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hA
  have hepos : 0 < AddMonoid.exponent A := Nat.pos_of_dvd_of_pos he hn
  have h1 : Nat.card {a : A // AddMonoid.exponent A • a = 0} = Nat.card A :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun a => AddMonoid.exponent_nsmul_eq_zero a)
  have h2 := hker _ he
  rw [h1, hcard] at h2
  have h3 : n ≤ AddMonoid.exponent A := by
    by_contra h
    push Not at h
    have := Nat.pow_lt_pow_left h (two_ne_zero)
    omega
  exact le_antisymm (Nat.le_of_dvd hn he) h3

private noncomputable def zmodHom (n : ℕ) (P : A) (hP : n • P = 0) : ZMod n →+ A :=
  ZMod.lift n ⟨zmultiplesHom A P, by simp [hP]⟩

private theorem zmodHom_apply {n : ℕ} [NeZero n] (P : A) (hP : n • P = 0) (a : ZMod n) :
    zmodHom n P hP a = a.val • P := by
  have h : ((a.val : ℤ) : ZMod n) = a := by simp
  conv_lhs => rw [← h]
  rw [zmodHom, ZMod.lift_coe]
  simp only [zmultiplesHom_apply, natCast_zsmul]

theorem nonempty_addEquiv_zmod_prod {n : ℕ} (hn : 0 < n) (hA : ∀ a : A, n • a = 0)
    (hcard : Nat.card A = n ^ 2)
    (hker : ∀ m, m ∣ n → Nat.card {a : A // m • a = 0} ≤ m ^ 2) :
    Nonempty (A ≃+ ZMod n × ZMod n) := by
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨P, hP⟩ := exists_addOrderOf_eq_of_card hn hA hcard hker
  set C := AddSubgroup.zmultiples P with hCdef
  have hC : Nat.card C = n := by rw [Nat.card_zmultiples, hP]
  have hB : Nat.card (A ⧸ C) = n := by
    have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup C
    rw [hcard, hC] at h
    have : n * n = Nat.card (A ⧸ C) * n := by rw [← h]; ring
    exact (Nat.eq_of_mul_eq_mul_right hn this).symm
  have hBn : ∀ b : A ⧸ C, n • b = 0 := by
    intro b
    induction b using QuotientAddGroup.induction_on with
    | H a => rw [← QuotientAddGroup.mk_nsmul, hA, QuotientAddGroup.mk_zero]

  obtain ⟨Qb, hQb⟩ : ∃ Qb : A ⧸ C, addOrderOf Qb = n := by
    have hexB : AddMonoid.ExponentExists (A ⧸ C) := ⟨n, hn, hBn⟩
    obtain ⟨Qb, hQ⟩ := AddMonoid.exists_addOrderOf_eq_exponent hexB
    refine ⟨Qb, hQ.trans ?_⟩
    set m := AddMonoid.exponent (A ⧸ C) with hmdef
    have hm : m ∣ n := AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hBn
    have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm hn
    obtain ⟨d, hd⟩ := hm
    have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)
    let φ : A →+ A :=
      { toFun := fun a => m • a
        map_zero' := nsmul_zero m
        map_add' := fun a b => nsmul_add a b m }
    have hφ : ∀ a, φ a = m • a := fun a => rfl

    have hkerφ : Nat.card φ.ker ≤ m ^ 2 := by
      have : Nat.card φ.ker = Nat.card {a : A // m • a = 0} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun a => by rw [AddMonoidHom.mem_ker, hφ])
      rw [this]
      exact hker m ⟨d, hd⟩

    have hrange : Nat.card φ.range ≤ d := by
      have hmem : ∀ x : φ.range, (x : A) ∈ C := by
        rintro ⟨_, a, rfl⟩
        show φ a ∈ C
        rw [← QuotientAddGroup.eq_zero_iff, hφ, QuotientAddGroup.mk_nsmul]
        exact AddMonoid.exponent_nsmul_eq_zero _
      have hd' : ∀ x : φ.range, d • (x : A) = 0 := by
        rintro ⟨_, a, rfl⟩
        show d • φ a = 0
        rw [hφ, ← mul_nsmul', mul_comm, ← hd, hA]
      let ι : φ.range → {c : C // d • c = 0} := fun x =>
        ⟨⟨x, hmem x⟩, by
          apply Subtype.ext
          simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
          exact hd' x⟩
      have hι : Function.Injective ι := by
        intro x y h
        have := congrArg (fun z => ((z.1 : C) : A)) h
        exact Subtype.ext this
      have hle := Nat.card_le_card_of_injective ι hι
      classical
      have : Fintype C := Fintype.ofFinite C
      have hcyc := IsAddCyclic.card_nsmul_eq_zero_le (α := C) hdpos
      rw [Nat.card_eq_fintype_card (α := {c : C // d • c = 0}), Fintype.card_subtype] at hle
      exact hle.trans (by convert hcyc)
    have htot : Nat.card A = Nat.card φ.ker * Nat.card φ.range := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
    rw [hcard, hd] at htot
    have h1 : (m * d) ^ 2 ≤ m ^ 2 * d := by
      rw [htot]; exact Nat.mul_le_mul hkerφ hrange
    have hd1 : d ≤ 1 := by
      by_contra h
      push Not at h
      have : m ^ 2 * d < (m * d) ^ 2 := by
        rw [mul_pow]
        have : d < d ^ 2 := by nlinarith
        exact Nat.mul_lt_mul_of_pos_left this (by positivity)
      omega
    have : d = 1 := by omega
    rw [hd, this, mul_one]
  obtain ⟨Q, rfl⟩ := QuotientAddGroup.mk_surjective Qb
  have hQn : n • Q = 0 := hA Q
  let f : ZMod n × ZMod n →+ A := (zmodHom n P (hA P)).coprod (zmodHom n Q hQn)
  have hf : ∀ x : ZMod n × ZMod n, f x = x.1.val • P + x.2.val • Q := by
    intro x
    simp [f, AddMonoidHom.coprod_apply, zmodHom_apply]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    rw [hf] at hab
    have hPC : (P : A ⧸ C) = 0 := (QuotientAddGroup.eq_zero_iff P).mpr (AddSubgroup.mem_zmultiples P)
    have hb : b.val • (Q : A ⧸ C) = 0 := by
      have := congrArg (QuotientAddGroup.mk (s := C)) hab
      simpa [QuotientAddGroup.mk_add, QuotientAddGroup.mk_nsmul, hPC] using this
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hQb] at hb
    have hb0 : b = 0 := by
      rw [← ZMod.val_eq_zero]
      exact Nat.eq_zero_of_dvd_of_lt hb (ZMod.val_lt b)
    subst hb0
    simp only [ZMod.val_zero, zero_smul, add_zero] at hab
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hP] at hab
    have ha0 : a = 0 := by
      rw [← ZMod.val_eq_zero]
      exact Nat.eq_zero_of_dvd_of_lt hab (ZMod.val_lt a)
    simp [ha0]
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_prod, Nat.card_zmod, sq])
  exact ⟨(AddEquiv.ofBijective f hbij).symm⟩

end Group

section Curve

variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

theorem card_torsionBy {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (torsionBy W.toAffine.Point n) = n ^ 2 := by
  classical
  have h := card_zsmul_eq_zero W (n := (n : ℤ)) (by exact_mod_cast hn)
  rw [Int.natAbs_natCast] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P => Submodule.mem_torsionBy_iff _ _)

theorem nonempty_torsionBy_addEquiv {n : ℕ} (hn : (n : F) ≠ 0) :
    Nonempty (torsionBy W.toAffine.Point n ≃+ ZMod n × ZMod n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  refine nonempty_addEquiv_zmod_prod hn0 (fun x => torsionBy.nsmul x) (card_torsionBy W hn) ?_
  intro m hm
  have hmF : (m : F) ≠ 0 := by
    obtain ⟨k, rfl⟩ := hm
    intro h
    exact hn (by push_cast; rw [h, zero_mul])
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmF
  have : Finite (torsionBy W.toAffine.Point m) :=
    Nat.finite_of_card_ne_zero (by rw [card_torsionBy W hmF]; exact pow_ne_zero _ hm0)
  rw [← card_torsionBy W hmF]
  refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, torsionBy.nsmul_iff.mpr ?_⟩) ?_
  · have := congrArg Subtype.val x.2
    simpa using this
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h

end Curve

end GroundTheory.Arith.Abelian
