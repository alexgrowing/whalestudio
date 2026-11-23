import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.CongruenceDescent

theorem mem_Gamma_iff_exists {N : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ CongruenceSubgroup.Gamma N ↔ ∃ B : Matrix (Fin 2) (Fin 2) ℤ, (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (N : ℤ) • B := by
  rw [CongruenceSubgroup.Gamma_mem]
  constructor
  · rintro ⟨h00, h01, h10, h11⟩
    have d00 : (N : ℤ) ∣ γ 0 0 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h00]; ring
    have d01 : (N : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h01
    have d10 : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
    have d11 : (N : ℤ) ∣ γ 1 1 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h11]; ring
    obtain ⟨a, ha⟩ := d00; obtain ⟨b, hb⟩ := d01; obtain ⟨c, hc⟩ := d10; obtain ⟨d, hd⟩ := d11
    refine ⟨!![a, b; c, d], ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
  · rintro ⟨B, hB⟩
    have e : ∀ i j, γ i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j + N * B i j := fun i j => by
      rw [show γ i j = (γ : Matrix (Fin 2) (Fin 2) ℤ) i j from rfl, hB, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;> simp

theorem Gamma_le_of_dvd {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  obtain ⟨B, hB⟩ := mem_Gamma_iff_exists.1 hγ
  obtain ⟨c, rfl⟩ := h
  exact mem_Gamma_iff_exists.2 ⟨(c : ℤ) • B, by rw [hB, smul_smul]; push_cast; ring_nf⟩

theorem pow_mem_Gamma_mul {L q : ℕ} (hq : q ∣ L) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma L) :
    γ ^ q ∈ CongruenceSubgroup.Gamma (L * q) := by
  obtain ⟨B, hB⟩ := mem_Gamma_iff_exists.1 hγ
  have key : ∀ m : ℕ, ∃ Y : Matrix (Fin 2) (Fin 2) ℤ,
      (γ : Matrix (Fin 2) (Fin 2) ℤ) ^ m = 1 + ((m : ℤ) * L) • B + ((L : ℤ) * L) • (B * B * Y) := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨Y, hY⟩ := ih
      refine ⟨(m : ℤ) • 1 + Y + Y * ((L : ℤ) • B), ?_⟩
      rw [pow_succ, hY, hB]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_add, smul_smul, Matrix.mul_assoc]
      push_cast
      module
  obtain ⟨Y, hY⟩ := key q
  obtain ⟨c, rfl⟩ := hq
  refine mem_Gamma_iff_exists.2 ⟨B + (c : ℤ) • (B * B * Y), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_pow, hY, smul_add, smul_smul]
  push_cast
  module

theorem pow_pow_mem_Gamma_mul {L q : ℕ} (hq : q ∣ L) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma L) (j : ℕ) :
    γ ^ (q ^ j) ∈ CongruenceSubgroup.Gamma (L * q ^ j) := by
  induction j with
  | zero => simpa only [pow_zero, pow_one, mul_one] using hγ
  | succ j ih =>
    rw [pow_succ, pow_mul, ← mul_assoc]
    exact pow_mem_Gamma_mul (hq.mul_right _) ih

theorem coprime_card_of_pow_eq_one {Q : Type} [Group Q] [Finite Q] {l m : ℕ} (hl : l.Prime) (hm : l.Coprime m)
    (h : ∀ x : Q, x ^ m = 1) : l.Coprime (Nat.card Q) := by
  rw [hl.coprime_iff_not_dvd]
  intro hd
  haveI := Fact.mk hl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hd
  have := orderOf_dvd_of_pow_eq_one (h x)
  rw [hx] at this
  exact (hl.coprime_iff_not_dvd.1 hm) this

theorem exists_invariant {H A : Type} [Group H] [CommGroup A] (s : H → A →* A)
    (hs : ∀ g h a, s (g * h) a = s h (s g a)) (D : Subgroup H) [D.Normal] [Finite (H ⧸ D)] {m : ℕ}
    (hm : m.Coprime (Nat.card (H ⧸ D))) (f : A) (hD : ∀ δ ∈ D, s δ f = f) (hf : ∀ γ, ∃ g : A, s γ f = f * g ^ m) :
    ∃ h : A, ∀ γ, s γ (f * h ^ m) = f * h ^ m := by
  classical
  haveI := Fintype.ofFinite (H ⧸ D)
  choose g hg using hf
  have hwd : ∀ a b : H, (a : H ⧸ D) = b → s a f = s b f := by
    intro a b hab
    have h1 : a * (a⁻¹ * b) * a⁻¹ ∈ D := Subgroup.Normal.conj_mem ‹_› _ (QuotientGroup.eq.1 hab) a
    have h2 : b = (a * (a⁻¹ * b) * a⁻¹) * a := by group
    conv_rhs => rw [h2, hs, hD _ h1]
  set F : A := ∏ x : H ⧸ D, s x.out f with hF
  have hinv : ∀ γ, s γ F = F := by
    intro γ
    rw [hF, map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight (γ : H ⧸ D)) _ _ fun x => ?_
    rw [← hs]
    apply hwd
    simp
  have hFeq : F = f ^ Nat.card (H ⧸ D) * (∏ x : H ⧸ D, g x.out) ^ m := by
    rw [hF]
    simp only [hg, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hm
  refine ⟨f ^ (-u) * (∏ x : H ⧸ D, g x.out) ^ v, fun γ => ?_⟩
  have e : f * (f ^ (-u) * (∏ x : H ⧸ D, g x.out) ^ v) ^ m = F ^ v := by
    have e1 : f * f ^ (-u * (m : ℤ)) = f ^ ((Nat.card (H ⧸ D) : ℤ) * v) := by
      rw [← _root_.zpow_one_add]
      congr 1
      linear_combination -huv
    rw [hFeq, mul_pow, _root_.mul_zpow, ← _root_.zpow_natCast, ← _root_.zpow_natCast, ← _root_.zpow_natCast,
      ← _root_.zpow_natCast]
    simp only [← _root_.zpow_mul]
    rw [← mul_assoc, e1, mul_comm v]
  rw [e, map_zpow, hinv]

end GlobalTheory.KZ.ES.CongruenceDescent

namespace GlobalTheory.KZ.ES

open CongruenceDescent CongruenceSubgroup in

theorem exists_lev_mul_pow_of_invariant_mod_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n M e : ℕ), l.Prime → 0 < M → ∀ f : X.Kˣ, Lev X (M ^ e) f → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) * (h : X.K) ^ (l ^ n)) := by
  intro Ω _ _ _ ε X l n M e hl hM f hlev hf
  obtain ⟨a, q, hq, hMq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hl.ne_one
  have hlq : l.Coprime q := hl.coprime_iff_not_dvd.2 hq
  let H : Subgroup SL(2, ℤ) := Gamma (M * l ^ (a * e))
  haveI := Gamma_normal (M ^ e)
  haveI : NeZero (M ^ e) := ⟨(pow_pos hM e).ne'⟩
  let D : Subgroup H := (Gamma (M ^ e)).subgroupOf H
  haveI : D.FiniteIndex := inferInstance
  have hcard : l.Coprime (Nat.card (H ⧸ D)) := by
    refine coprime_card_of_pow_eq_one hl (hlq.pow_right e) fun x => ?_
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    refine Gamma_le_of_dvd ?_ (pow_pow_mem_Gamma_mul (q := q) ?_ γ.2 e)
    · exact ⟨M, by rw [hMq]; ring⟩
    · exact ⟨l ^ a * l ^ (a * e), by rw [hMq]; ring⟩
  obtain ⟨h, hh⟩ := exists_invariant (H := H) (A := X.Kˣ)
    (fun γ => Units.map (X.sl (ofSL γ) : X.K →* X.K))
    (fun g h a => Units.ext (by simp [X.sl_mul])) D (hcard.pow_left n) f
    (fun δ hδ => Units.ext (by simpa using hlev δ hδ))
    (fun γ => by
      obtain ⟨g, hg⟩ := hf γ (Gamma_le_of_dvd (dvd_mul_right _ _) γ.2)
      exact ⟨g, Units.ext (by simpa using hg)⟩)
  refine ⟨a * e, h, fun γ hγ => ?_⟩
  have := congrArg Units.val (hh ⟨γ, hγ⟩)
  simpa using this

end GlobalTheory.KZ.ES
