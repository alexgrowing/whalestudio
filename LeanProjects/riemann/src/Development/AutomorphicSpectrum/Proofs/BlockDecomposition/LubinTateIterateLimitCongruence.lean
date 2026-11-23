import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.QLim

theorem map_mem {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) (q : ℕ) {x : B}
    (hx : x ∈ S) : ϖ * x + x ^ q ∈ S :=
  S.add_mem (S.mul_mem hϖ hx) (S.pow_mem hx q)

theorem step_congr {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) {q : ℕ}
    (hq : ∃ s ∈ S, (q : B) = ϖ * s) {a b c : B} (hb : b ∈ S) (hc : c ∈ S) {m : ℕ} (hm : 1 ≤ m)
    (hab : a - b = ϖ ^ m * c) :
    ∃ c' ∈ S, (ϖ * a + a ^ q) - (ϖ * b + b ^ q) = ϖ ^ (m + 1) * c' := by
  obtain ⟨s, hs, hqs⟩ := hq
  have hy : ϖ ^ m * c ∈ S := S.mul_mem (S.pow_mem hϖ m) hc
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (Polynomial.X ^ q : Polynomial S)
    (⟨b, hb⟩ : S) (⟨ϖ ^ m * c, hy⟩ : S)
  have hk' : (b + ϖ ^ m * c) ^ q =
      b ^ q + (q : B) * b ^ (q - 1) * (ϖ ^ m * c) + (k : B) * (ϖ ^ m * c) ^ 2 := by
    have h := congrArg (Subtype.val) hk
    simpa [Polynomial.derivative_X_pow] using h
  have ha : a = b + ϖ ^ m * c := by linear_combination hab
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨c + s * b ^ (q - 1) * c + (k : B) * ϖ ^ m' * c ^ 2, ?_, ?_⟩
  · exact S.add_mem (S.add_mem hc (S.mul_mem (S.mul_mem hs (S.pow_mem hb _)) hc))
      (S.mul_mem (S.mul_mem k.2 (S.pow_mem hϖ _)) (S.pow_mem hc _))
  · rw [ha, hk', hqs]; ring

theorem iter_congr {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) {q : ℕ}
    (hq : ∃ s ∈ S, (q : B) = ϖ * s) (n : ℕ) :
    ∀ {a b c : B} {m : ℕ}, a ∈ S → b ∈ S → c ∈ S → 1 ≤ m → a - b = ϖ ^ m * c →
      ∃ c' ∈ S, ltIter ϖ q n a - ltIter ϖ q n b = ϖ ^ (m + n) * c' := by
  induction n with
  | zero =>
    intro a b c m _ _ hc _ hab
    exact ⟨c, hc, by simpa [ltIter] using hab⟩
  | succ n ih =>
    intro a b c m ha hb hc hm hab
    obtain ⟨c₁, hc₁, h₁⟩ := step_congr hϖ hq hb hc hm hab
    obtain ⟨c₂, hc₂, h₂⟩ := ih (map_mem hϖ q ha) (map_mem hϖ q hb) hc₁ (by omega) h₁
    refine ⟨c₂, hc₂, ?_⟩
    have e : m + (n + 1) = m + 1 + n := by omega
    rw [e]
    exact h₂

theorem exists_limit : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}, PerEnv S F ϖ → ∀ (q : ℕ), 2 ≤ q → (∃ s ∈ S, (q : B) = ϖ * s) →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → (∀ n, v (n + 1) ^ q = v n) →
      ∃ Q ∈ S, ∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a := by
  intro B _ S F ϖ E q _ hq v hv hvq
  have hd : ∀ n, ∃ e ∈ S, ltIter ϖ q (n + 1) (v (n + 1)) - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * e := by
    intro n
    have h1 : (ϖ * v (n + 1) + v (n + 1) ^ q) - v n = ϖ ^ 1 * v (n + 1) := by
      rw [hvq]; ring
    obtain ⟨c, hc, h⟩ := iter_congr E.mem hq n (map_mem E.mem q (hv (n + 1))) (hv n) (hv (n + 1))
      le_rfl h1
    refine ⟨c, hc, ?_⟩
    have e : ltIter ϖ q (n + 1) (v (n + 1)) = ltIter ϖ q n (ϖ * v (n + 1) + v (n + 1) ^ q) := rfl
    rw [e, h, add_comm n 1]
  choose e he hde using hd
  let s : ℕ → B := fun n => Nat.casesOn n (v 0) e
  have hs : ∀ n, s n ∈ S := by
    intro n
    cases n with
    | zero => exact hv 0
    | succ n => exact he n
  obtain ⟨r, hr, hsum⟩ := E.sumS s hs
  have tel : ∀ N, ∑ n ∈ Finset.range (N + 1), ϖ ^ n * s n = ltIter ϖ q N (v N) := by
    intro N
    induction N with
    | zero => simp [s, ltIter]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hN : s (N + 1) = e N := rfl
      rw [hN, ← hde N]
      ring
  refine ⟨r, hr, fun n => ?_⟩
  obtain ⟨a, ha, h⟩ := hsum (n + 1)
  rw [tel n] at h
  exact ⟨a, ha, h⟩

end GlobalTheory.CompanionTheory.LTPer.QLim
