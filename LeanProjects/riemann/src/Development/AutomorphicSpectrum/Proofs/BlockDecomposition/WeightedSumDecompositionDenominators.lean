import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PeriodicWeightBounded
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceSummable
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesDifferentiableLeftStrip

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral

def IntW (l K : ℕ) {r : ℕ} (v : (Fin r → ℕ) → ℚ) : Prop :=
  ∀ m, ∃ z : ℤ, (l : ℚ) ^ K * v m = z

theorem IntW.succ {l K r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) : IntW l (K + 1) v := by
  intro m
  obtain ⟨z, hz⟩ := h m
  refine ⟨l * z, ?_⟩
  push_cast
  rw [← hz, pow_succ]
  ring

theorem IntW.mono {l K K' r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) (hK : K ≤ K') :
    IntW l K' v := by
  induction K', hK using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih.succ

theorem IntW.neg_one_pow_mul {l K r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) (c : ℕ) :
    IntW l K (fun m => (-1 : ℚ) ^ c * v m) := by
  intro m
  obtain ⟨z, hz⟩ := h m
  refine ⟨(-1) ^ c * z, ?_⟩
  push_cast
  rw [← hz]
  ring

theorem int_sum {α : Type} (s : Finset α) (q : ℚ) (f : α → ℚ)
    (h : ∀ a ∈ s, ∃ z : ℤ, q * f a = z) : ∃ z : ℤ, q * ∑ a ∈ s, f a = z := by
  classical
  choose! g hg using h
  refine ⟨∑ a ∈ s, g a, ?_⟩
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl hg

theorem partialSum_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) :
    IntW l K (partialSum i v) :=
  fun m => int_sum _ _ _ fun k _ => h _

theorem intW_partialSumMean {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (meanP l i v) := by
  intro m
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  obtain ⟨z, hz⟩ := int_sum (Finset.range l) ((l : ℚ) ^ K)
    (fun k => partialSum i v (Function.update m i k)) (fun k _ => partialSum_int h _)
  refine ⟨z, ?_⟩
  rw [← hz, meanP, pow_succ]
  field_simp

theorem aop_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (Aop l i v) := by
  intro m
  obtain ⟨a, ha⟩ := (partialSum_int (i := i) h).succ (m + Pi.single i 1)
  obtain ⟨b, hb⟩ := intW_partialSumMean (i := i) hl h m
  refine ⟨a - b, ?_⟩
  push_cast
  rw [← ha, ← hb, Aop]
  ring

theorem bop_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (Bop l i v) := by
  intro m
  by_cases h0 : m i = 0
  · simpa [Bop, h0] using intW_partialSumMean (i := i) hl h m
  · exact ⟨0, by simp [Bop, h0]⟩

theorem iterate_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v)
    (c : ℕ) : IntW l (K + c) ((Aop l i)^[c] v) := by
  induction c with
  | zero => simpa using h
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact aop_int hl ih

theorem uW_int {l N K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v)
    (c : Fin (N + 1)) : IntW l (K + (N + 1)) (OneVar.uW l N i v c) := by
  unfold OneVar.uW
  split_ifs with hc
  · have h1 : IntW l (K + c + 1) (Bop l i ((Aop l i)^[c] v)) := bop_int hl (iterate_int hl h c)
    exact (h1.mono (by omega)).neg_one_pow_mul _
  · exact ((iterate_int hl h N).mono (by omega)).neg_one_pow_mul _

theorem abel_oneVar_uW (r l N : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (hl : 0 < l) (hg : GoodAt l i v)
    (hb : BddW v) :
    (∀ c : Fin (N + 1), BddW (OneVar.uW l N i v c)) ∧
    (∀ c : Fin (N + 1), (c : ℕ) = N ∨ ∀ m, m i ≠ 0 → OneVar.uW l N i v c m = 0) ∧
    (∀ (c : Fin (N + 1)) k, k ≠ i → GoodAt l k v → GoodAt l k (OneVar.uW l N i v c)) ∧
    (∀ (c : Fin (N + 1)) k, k ≠ i → (∀ m, m k ≠ 0 → v m = 0) → ∀ m, m k ≠ 0 → OneVar.uW l N i v c m = 0) ∧
    ∀ g : (Fin r → ℕ) → ℂ, Summable g →
      ∑' m, (v m : ℂ) * g m =
        ∑ c : Fin (N + 1), ∑' m, (OneVar.uW l N i v c m : ℂ) * DL (List.replicate (c : ℕ) i) g m := by
  refine ⟨fun c => ?_, fun c => ?_, fun c k hk hgk => ?_, fun c k hk hsk => ?_, fun g hs => ?_⟩
  · unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · have hc := OneVar.iterate_good_bdd hl hg hb c
      exact OneVar.bddW_sign _ (@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.aop_props r l i _ hl hc.1 hc.2).2.1
    · exact OneVar.bddW_sign _ (OneVar.iterate_good_bdd hl hg hb N).2
  · by_cases h : (c : ℕ) < N
    · refine Or.inr fun m hm => ?_
      simp [OneVar.uW, h, Bop, hm]
    · exact Or.inl (by have := c.isLt; omega)
  · unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · exact OneVar.goodAt_smul _ ((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).1 (OneVar.iterate_good_other hk hgk c)).2
    · exact OneVar.goodAt_smul _ (OneVar.iterate_good_other hk hgk N)
  · intro m hm
    unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · simp [((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).2 (OneVar.iterate_supp_other hk hsk c)).2 m hm]
    · simp [OneVar.iterate_supp_other hk hsk N m hm]
  · rw [OneVar.tsum_iterate hl hg hb hs N, Fin.sum_univ_castSucc, Finset.sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      have hc : (c : ℕ) < N := c.isLt
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [OneVar.uW, hc, mul_assoc]
    · rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [OneVar.uW, mul_assoc]

theorem expansion_on_finset_int (r l N : ℕ) (w : (Fin r → ℕ) → ℚ) (hl : 0 < l) (hw : GoodWeight l w)
    (hz : ∀ m, ∃ z : ℤ, w m = z) (I : Finset (Fin r)) :
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ),
      (∀ q, BddW (u q)) ∧ (∀ q i, i ∉ I → GoodAt l i (u q) ∧ (cs q).count i = 0) ∧
      (∀ q i, i ∈ I → (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      (∀ q, IntW l K (u q)) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => [], fun _ => w, 0,
      fun _ => GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic r l w hl (fun i m => hw.1 m i),
      fun _ i _ => ⟨⟨fun m => hw.1 m i, fun m => hw.2 m i⟩, by simp⟩,
      fun _ i hi => absurd hi (by simp), fun _ m => ?_, fun g _ => by simp [DL]⟩
    obtain ⟨z, hz⟩ := hz m
    exact ⟨z, by simp [hz]⟩
  | insert a I ha ih =>
    obtain ⟨Q, _, cs, u, K, hb, hg, hs, hi, hid⟩ := ih
    have hP := fun q => abel_oneVar_uW r l N a (u q) hl (hg q a ha).1 (hb q)
    have h1 := fun q => (hP q).1
    have h2 := fun q => (hP q).2.1
    have h3 := fun q => (hP q).2.2.1
    have h4 := fun q => (hP q).2.2.2.1
    have h5 := fun q => (hP q).2.2.2.2
    refine ⟨Q × Fin (N + 1), inferInstance, fun p => List.replicate (p.2 : ℕ) a ++ cs p.1,
      fun p => OneVar.uW l N a (u p.1) p.2, K + (N + 1), fun p => h1 p.1 p.2, ?_, ?_,
      fun p => uW_int hl (hi p.1) p.2, ?_⟩
    · rintro ⟨q, c⟩ k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkI : k ∉ I := fun h => hk (Finset.mem_insert_of_mem h)
      refine ⟨h3 q c k hka (hg q k hkI).1, ?_⟩
      simp [List.count_append, List.count_replicate, (hg q k hkI).2, hka.symm]
    · rintro ⟨q, c⟩ k hk
      by_cases hka : k = a
      · subst hka
        have h0 : (cs q).count k = 0 := (hg q k ha).2
        rcases h2 q c with h | h
        · left
          simp [List.count_append, h0, h]
        · exact Or.inr h
      · have hkI : k ∈ I := (Finset.mem_insert.1 hk).resolve_left hka
        have hak : a ≠ k := fun h => hka h.symm
        rcases hs q k hkI with h | h
        · left
          simp [List.count_append, List.count_replicate, hak, h]
        · exact Or.inr (h4 q c k hka h)
    · intro g hgs
      rw [hid g hgs, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [h5 q _ (GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_DL r (cs q) g hgs)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [DL, List.foldr_append]

theorem expansion_all_variables_int : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w →
    (∀ m, ∃ z : ℤ, w m = z) →
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ),
      (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      (∀ q m, ∃ z : ℤ, (l : ℚ) ^ K * u q m = z) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  intro r l N w hl hw hz
  obtain ⟨Q, iQ, cs, u, K, hb, -, hs, hi, hid⟩ := expansion_on_finset_int r l N w hl hw hz Finset.univ
  exact ⟨Q, iQ, cs, u, K, hb, fun q i => hs q i (Finset.mem_univ i), hi, hid⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral
