import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PerfectProj

theorem exists_pow_prime_pow_kill (p : ℕ) (hp : 1 < p) (k B : Type) [Field k] [CommRing B]
    [Algebra k B] [Module.Finite k B] :
    ∃ r : ℕ, ∀ x : B, IsNilpotent x → x ^ (p ^ r) = 0 := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := B)
  refine ⟨n, fun x hx => ?_⟩
  have hmem : x ^ n ∈ (nilradical B) ^ n := Ideal.pow_mem_pow (mem_nilradical.mpr hx) n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hmem
  exact pow_eq_zero_of_le (Nat.lt_pow_self hp).le hmem

theorem exists_eq_pow_prime_pow (p : ℕ) {A : Type} [CommRing A] (π : A → A)
    (h : ∀ a, ∃ b, π a = π b ^ p) : ∀ (m : ℕ) (a : A), ∃ b, π a = π b ^ (p ^ m) := by
  intro m
  induction m with
  | zero => intro a; exact ⟨a, by simp⟩
  | succ m ih =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    obtain ⟨c, hc⟩ := h b
    exact ⟨c, by rw [hb, hc, ← pow_mul, pow_succ']⟩

theorem natural_idempotent_reduced : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Module.Finite k B] (π : A →ₐ[k] A) (π' : B →ₐ[k] B), ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : B, IsNilpotent (a - π' a)) ∧ ∀ a : B, ∃ b : B, π' a = π' b ^ p) → (∀ (f : A →ₐ[k] B) (a : A), f (π a) = π' (f a)) ∧ (∀ b, π' (π' b) = π' b) ∧ ∀ b, IsNilpotent (π' b) → π' b = 0 := by
  intro p _ k _ _ A B _ _ _ _ _ π π' hA hB
  rcases subsingleton_or_nontrivial B with hs | hs
  · exact ⟨fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _,
      fun _ _ => Subsingleton.elim _ _⟩
  haveI : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
  obtain ⟨r, hr⟩ := exists_pow_prime_pow_kill p (Fact.out : p.Prime).one_lt k B
  have iA := exists_eq_pow_prime_pow p π hA.2 r
  have iB := exists_eq_pow_prime_pow p π' hB.2 r
  have h3 : ∀ b, IsNilpotent (π' b) → π' b = 0 := by
    intro b hb
    obtain ⟨c, hc⟩ := iB b
    rw [hc] at hb ⊢
    exact hr _ hb.of_pow
  refine ⟨fun f a => ?_, fun y => ?_, h3⟩
  · obtain ⟨b, hb⟩ := iA a
    obtain ⟨c, hc⟩ := iB (f a)
    have hd : IsNilpotent (f (π a) - π' (f a)) := by
      have h1 : IsNilpotent (f (a - π a)) := (hA.1 a).map f
      have h2 := hB.1 (f a)
      have e : f (π a) - π' (f a) = (f a - π' (f a)) - f (a - π a) := by rw [map_sub]; ring
      rw [e]
      exact (Commute.all _ _).isNilpotent_sub h2 h1
    have he : f (π a) - π' (f a) = (f (π b) - π' c) ^ (p ^ r) := by
      rw [sub_pow_char_pow, hb, hc, map_pow]
    rw [he] at hd
    exact sub_eq_zero.mp (he.trans (hr _ hd.of_pow))
  · obtain ⟨c, hc⟩ := iB y
    have he : π' (π' y) - π' y = (π' (π' c) - π' c) ^ (p ^ r) := by
      rw [sub_pow_char_pow, hc, map_pow]
    have hn : IsNilpotent (π' (π' c) - π' c) := by
      rw [← neg_sub]; exact (hB.1 (π' c)).neg
    exact sub_eq_zero.mp (he.trans (hr _ hn))

end GlobalTheory.PerfectProj
