import Mathlib
open NumberField

namespace GlobalTheory.PrimaryTorsionBlocks

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

def killedBy (I : Ideal R) : AddSubgroup M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun {x y} hx hy a ha => by
    show a • (x + y) = 0
    rw [smul_add, hx a ha, hy a ha, add_zero]
  neg_mem' := fun {x} hx a ha => by
    show a • (-x) = 0
    rw [smul_neg, hx a ha, neg_zero]

def annOf (x : M) : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M x)

lemma mem_annOf {x : M} {a : R} : a ∈ annOf x ↔ a • x = 0 := by
  simp [annOf]

lemma mem_killedBy_iff {I : Ideal R} {x : M} : x ∈ killedBy (M := M) I ↔ I ≤ annOf x :=
  ⟨fun h a ha => mem_annOf.2 (h a ha), fun h a ha => mem_annOf.1 (h ha)⟩

theorem card_killedBy_block (P J : Ideal R) (n : R) (e : ℕ)
    (hspan : Ideal.span {n} = P ^ e * J) (hcop : P ⊔ J = ⊤)
    (hlift : ∀ j : ℕ, ∀ y : M, n ^ j • y = 0 → ∃ z : M, n ^ (j + 1) • z = 0 ∧ n • z = y)
    (j : ℕ) :
    Nat.card (killedBy (M := M) (P ^ (e * (j + 1)))) =
      Nat.card (killedBy (M := M) (P ^ (e * j))) * Nat.card (killedBy (M := M) (P ^ e)) := by
  have hpow : ∀ k : ℕ, Ideal.span {n ^ k} = P ^ (e * k) * J ^ k := by
    intro k
    rw [← Ideal.span_singleton_pow, hspan, mul_pow, pow_mul]
  have hcop' : ∀ a b : ℕ, P ^ a ⊔ J ^ b = ⊤ := by
    intro a b
    exact Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_iff_sup_eq.2 hcop).pow)
  have hnmem : ∀ k : ℕ, n ^ k ∈ P ^ (e * k) := by
    intro k
    have : n ^ k ∈ Ideal.span {n ^ k} := Ideal.mem_span_singleton_self _
    rw [hpow k] at this
    exact (Ideal.mul_le_left : P ^ (e * k) * J ^ k ≤ P ^ (e * k)) this
  have hn : n ∈ P ^ e := by simpa using hnmem 1
  have hexp : e * (j + 1) = e * j + e := by ring
  have hle1 : P ^ (e * (j + 1)) ≤ P ^ (e * j) := Ideal.pow_le_pow_right (by rw [hexp]; omega)
  have hle2 : P ^ (e * (j + 1)) ≤ P ^ e := Ideal.pow_le_pow_right (by rw [hexp]; omega)

  let f : killedBy (M := M) (P ^ (e * (j + 1))) →+ killedBy (M := M) (P ^ (e * j)) :=
    AddMonoidHom.mk' (fun x => ⟨n • (x : M), fun a ha => by
      rw [smul_smul]
      apply x.2
      rw [hexp, pow_add]
      exact Ideal.mul_mem_mul ha hn⟩)
      (fun x y => by ext; simp [smul_add])
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hy0 : n ^ j • y = 0 := hy _ (hnmem j)
    obtain ⟨z, hz, hzy⟩ := hlift j y hy0
    have h1 : (1 : R) ∈ P ^ (e * (j + 1)) ⊔ J ^ (j + 1) := by rw [hcop']; trivial
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1
    refine ⟨⟨t • z, fun a ha => ?_⟩, ?_⟩
    · rw [smul_smul]
      have hat : a * t ∈ Ideal.span {n ^ (j + 1)} := by
        rw [hpow]
        exact Ideal.mul_mem_mul ha ht
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hat
      rw [← hc, mul_smul, hz, smul_zero]
    · ext
      show n • t • z = y
      rw [smul_comm, hzy]
      have hsy : s • y = 0 := hy s (hle1 hs)
      calc t • y = s • y + t • y := by rw [hsy, zero_add]
        _ = (s + t) • y := (add_smul s t y).symm
        _ = y := by rw [hst, one_smul]
  have hsup : P ^ e ≤ P ^ (e * (j + 1)) ⊔ Ideal.span {n} := by
    have hc : P ^ (e * j) ⊔ J = ⊤ := by simpa using hcop' (e * j) 1
    have : P ^ e = P ^ e * (P ^ (e * j) ⊔ J) := by rw [hc, Ideal.mul_top]
    rw [this, Ideal.mul_sup, hspan, ← pow_add, hexp, add_comm (e * j) e]
  have hker : Nat.card f.ker = Nat.card (killedBy (M := M) (P ^ e)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : M), ?_⟩
        invFun := fun x => ⟨⟨(x : M), fun a ha => x.2 a (hle2 ha)⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    · have hx1 := mem_killedBy_iff.1 x.1.2
      have hx2 : n • (x.1 : M) = 0 := by
        have := x.2
        rw [AddMonoidHom.mem_ker] at this
        exact congrArg Subtype.val this
      refine mem_killedBy_iff.2 (le_trans hsup (sup_le hx1 ?_))
      rw [Ideal.span_singleton_le_iff_mem]
      exact mem_annOf.2 hx2
    · rw [AddMonoidHom.mem_ker]
      ext
      exact x.2 n hn
  have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv, hker] at hmul
  exact hmul

end GlobalTheory.PrimaryTorsionBlocks

namespace GlobalTheory

open GlobalTheory.PrimaryTorsionBlocks in

theorem card_primaryTorsion_mul_blocks :
    ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Finite {x : M // (N ^ j) • x = 0}) →
    (∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y) →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    ∃ e : ℕ, 1 ≤ e ∧ ∀ j : ℕ, Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * (j + 1)), a • x = 0} =
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * j), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ e, a • x = 0} := by
  classical
  intro F _ _ M _ _ N hN _ hlift 𝔭 h𝔭 hN𝔭
  have hne : (N : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hI : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨Q, hPQ, hspan⟩ := Ideal.eq_prime_pow_mul_coprime hI 𝔭
  refine ⟨Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(N : 𝓞 F)})),
    ?_, fun j => ?_⟩
  · by_contra h0
    have h0' : Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {(N : 𝓞 F)})) = 0 := by omega
    rw [h0', pow_zero, one_mul] at hspan
    have hQ : Q ≤ 𝔭 := by rw [← hspan, Ideal.span_singleton_le_iff_mem]; exact hN𝔭
    rw [sup_eq_left.2 hQ] at hPQ
    exact h𝔭.ne_top hPQ
  · have hlift' : ∀ j : ℕ, ∀ y : M, (N : 𝓞 F) ^ j • y = 0 →
        ∃ z : M, (N : 𝓞 F) ^ (j + 1) • z = 0 ∧ (N : 𝓞 F) • z = y := by
      intro j y hy
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hy
      obtain ⟨z, h1, h2⟩ := hlift j y hy
      refine ⟨z, ?_, ?_⟩
      · rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; exact h1
      · rw [Nat.cast_smul_eq_nsmul]; exact h2
    exact card_killedBy_block 𝔭 Q (N : 𝓞 F) _ hspan hPQ hlift' j

end GlobalTheory
