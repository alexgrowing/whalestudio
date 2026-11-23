import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PrimeApproximation

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem yPrime_approx {R σ : Type} [CommRing R] {y : σ → R} {f : R} {BB : Type} [CommRing BB]
    [Algebra R BB] (h : IsYCpl y f BB) (n : ℕ) (J : Ideal R) (x : BB) (hx : x ∈ J.map (algebraMap R BB)) :
    ∃ (k : ℕ) (a : R), a ∈ J ∧
      algebraMap R BB f ^ k * x - algebraMap R BB a ∈ (Ideal.span (Set.range y) ^ n).map (algebraMap R BB) :=
  _root_.UpperTheory.Reformulated.B.PrimeApproximation.yPrime_approx h n J x hx

private theorem yPrime_back {R σ : Type} [CommRing R] {y : σ → R} {f : R} {BB : Type} [CommRing BB]
    [Algebra R BB] (h : IsYCpl y f BB) (n : ℕ) (J : Ideal R) (hJ : Ideal.span (Set.range y) ^ n ≤ J)
    (r : R) (hr : algebraMap R BB r ∈ J.map (algebraMap R BB)) : ∃ k : ℕ, f ^ k * r ∈ J := by
  obtain ⟨k, a, ha, h1⟩ := yPrime_approx h n J _ hr
  rw [← map_pow, ← map_mul, ← map_sub] at h1
  obtain ⟨m, hm⟩ := h.strict n _ h1
  refine ⟨m + k, ?_⟩
  convert J.add_mem (hJ hm) (J.mul_mem_left (f ^ m) ha) using 1
  ring

theorem UpperTheory.V.Pa.Core.yPrime :
    ∀ (R σ : Type) [CommRing R] [Fintype σ] (y : σ → R) (f : R) (BB : Type) [CommRing BB] [Algebra R BB], IsYCpl y f BB → ∀ q : Ideal R, q.IsPrime → f ∉ q → (∀ a, y a ∈ q) → (q.map (algebraMap R BB)).IsPrime ∧ (q.map (algebraMap R BB)).comap (algebraMap R BB) = q ∧ (∀ P : Ideal BB, P.IsPrime → (∀ a, algebraMap R BB (y a) ∈ P) → P.comap (algebraMap R BB) ≤ q → P ≤ q.map (algebraMap R BB)) ∧ ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra BB B] [Algebra R B] [IsScalarTower R BB B], IsCplAt BB (q.map (algebraMap R BB)) B → IsCplAt R q B := by
  intro R σ _ _ y f BB _ _ h q hq hf hy
  have hI : Ideal.span (Set.range y) ≤ q := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact hy a
  have hfk : ∀ k : ℕ, f ^ k ∉ q := fun k hk => hf (hq.mem_of_pow_mem k hk)
  have hmul : ∀ {s t : R}, s ∉ q → t ∉ q → s * t ∉ q := fun hs ht hst =>
    (hq.mem_or_mem hst).elim hs ht
  have hcom : ∀ r : R, algebraMap R BB r ∈ q.map (algebraMap R BB) → r ∈ q := by
    intro r hr
    obtain ⟨k, hk⟩ := yPrime_back h 1 q (by simpa using hI) r hr
    exact (hq.mem_or_mem hk).resolve_left (hfk k)
  have hcomap : (q.map (algebraMap R BB)).comap (algebraMap R BB) = q :=
    le_antisymm (fun r hr => hcom r hr) Ideal.le_comap_map
  have hIn : ∀ n : ℕ, (Ideal.span (Set.range y) ^ n).map (algebraMap R BB) ≤
      (q ^ n).map (algebraMap R BB) := fun n => Ideal.map_mono (Ideal.pow_right_mono hI n)
  have hI1 : ∀ n : ℕ, (Ideal.span (Set.range y) ^ (n + 1)).map (algebraMap R BB) ≤
      q.map (algebraMap R BB) := fun n =>
    Ideal.map_mono ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans hI)
  have hI2 : ∀ n : ℕ, (Ideal.span (Set.range y) ^ (n + 1)).map (algebraMap R BB) ≤
      (q ^ n).map (algebraMap R BB) := fun n =>
    (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n))).trans (hIn n)
  have hiff : ∀ (n k : ℕ) (x : BB) (r : R), algebraMap R BB f ^ k * x - algebraMap R BB r ∈
      (Ideal.span (Set.range y) ^ (n + 1)).map (algebraMap R BB) →
      (x ∈ q.map (algebraMap R BB) ↔ r ∈ q) := by
    intro n k x r hx
    have h1 := hI1 n hx
    constructor
    · intro hx'
      apply hcom
      have := Ideal.sub_mem _ (Ideal.mul_mem_left _ (algebraMap R BB f ^ k) hx') h1
      simpa using this
    · intro hr
      have := Ideal.add_mem _ h1 (Ideal.mem_map_of_mem (algebraMap R BB) hr)
      rw [sub_add_cancel] at this
      exact (Ideal.unit_mul_mem_iff_mem _ (h.unit.pow k)).1 this
  refine ⟨⟨?_, ?_⟩, hcomap, ?_, ?_⟩
  · intro ht
    apply hq.ne_top
    rw [← hcomap, ht, Ideal.comap_top]
  · intro x z hxz
    obtain ⟨j, r, hr⟩ := h.dense (0 + 1) x
    obtain ⟨k, s, hs⟩ := h.dense (0 + 1) z
    rw [hiff 0 j x r hr, hiff 0 k z s hs]
    apply hq.mem_or_mem
    rw [← hiff 0 (j + k) (x * z) (r * s) ?_]
    · exact hxz
    · convert Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R BB f ^ k * z) hr)
        (Ideal.mul_mem_left _ (algebraMap R BB r) hs) using 1
      simp only [map_mul]
      ring
  · intro P _ hyP hPq x hx
    obtain ⟨j, r, hr⟩ := h.dense (0 + 1) x
    rw [hiff 0 j x r hr]
    apply hPq
    have hIP : (Ideal.span (Set.range y) ^ (0 + 1)).map (algebraMap R BB) ≤ P := by
      rw [zero_add, pow_one, Ideal.map_le_iff_le_comap, Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      exact hyP a
    have := P.sub_mem (P.mul_mem_left (algebraMap R BB f ^ j) hx) (hIP hr)
    rw [Ideal.mem_comap]
    simpa using this
  · intro B _ _ _ _ _ hB
    have hm : ∀ (n : ℕ) (x : BB), x ∈ (q ^ n).map (algebraMap R BB) →
        algebraMap BB B x ∈ maximalIdeal B ^ n := by
      intro n x hx
      have h1 : (q.map (algebraMap R BB)).map (algebraMap BB B) ≤ maximalIdeal B := by
        rw [Ideal.map_le_iff_le_comap, hB.comap_eq]
      apply Ideal.pow_right_mono h1 n
      rw [← Ideal.map_pow, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
    refine ⟨hB.noeth, hB.complete, ?_, ?_, ?_⟩
    · rw [IsScalarTower.algebraMap_eq R BB B, ← Ideal.comap_comap, hB.comap_eq, hcomap]
    · intro n b
      obtain ⟨a, s, hs, hb⟩ := hB.dense n b
      obtain ⟨j, s', hs'⟩ := h.dense (n + 1) s
      obtain ⟨k, a', ha'⟩ := h.dense (n + 1) a
      refine ⟨f ^ j * a', f ^ k * s', hmul (hfk k) (fun hh => hs ((hiff n j s s' hs').2 hh)), ?_⟩
      have k1 := hm n _ (hI2 n hs')
      have k2 := hm n _ (hI2 n ha')
      simp only [map_sub, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at k1 k2
      convert Ideal.add_mem _ (Ideal.sub_mem _
        (Ideal.mul_mem_left _ (algebraMap R B f ^ (j + k)) hb)
        (Ideal.mul_mem_left _ (algebraMap R B f ^ k * b) k1))
        (Ideal.mul_mem_left _ (algebraMap R B f ^ j) k2) using 1
      simp only [map_mul, map_pow]
      ring
    · intro n a ha
      rw [IsScalarTower.algebraMap_apply R BB B] at ha
      obtain ⟨s, hs, hsa⟩ := hB.strict n _ ha
      rw [← Ideal.map_pow] at hsa
      obtain ⟨j, s', hs'⟩ := h.dense (n + 1) s
      have h1 : algebraMap R BB (s' * a) ∈ (q ^ n).map (algebraMap R BB) := by
        convert Ideal.sub_mem _ (Ideal.mul_mem_left _ (algebraMap R BB f ^ j) hsa)
          (Ideal.mul_mem_left _ (algebraMap R BB a) (hI2 n hs')) using 1
        simp only [map_mul]
        ring
      obtain ⟨k, hk⟩ := yPrime_back h n (q ^ n) (Ideal.pow_right_mono hI n) _ h1
      exact ⟨f ^ k * s', hmul (hfk k) (fun hh => hs ((hiff n j s s' hs').2 hh)), by rwa [mul_assoc]⟩
