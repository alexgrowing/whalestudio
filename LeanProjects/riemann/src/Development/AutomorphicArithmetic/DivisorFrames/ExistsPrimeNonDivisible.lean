import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRadicalOfHolomorphicRatioTendsto
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg

private theorem exists_least_of_total {ι : Type} (r : ι → ι → Prop) (htot : ∀ i j, r i j ∨ r j i)
    (htr : ∀ i j k, r i j → r j k → r i k) (i₀ : ι) (s : Finset ι) : ∃ i, ∀ j ∈ s, r i j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨i₀, by simp⟩
  | insert a s _ ih =>
    obtain ⟨i, hi⟩ := ih
    rcases htot i a with h | h
    · refine ⟨i, fun j hj => ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact h
      · exact hi j hj
    · refine ⟨a, fun j hj => ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact (htot j j).elim id id
      · exact htr _ _ _ h (hi j hj)

theorem UpperTheory.exists_prime_non_divisible :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (m : ℕ) (b : Fin m → A) (d : A), d ≠ 0 → (∃ j, ¬ d ∣ b j) → ∃ (P : Ideal A) (t : A) (c : Fin m → A) (j₀ : Fin m), P.IsPrime ∧ d ∈ P ∧ t ∈ P ∧ c j₀ ∉ P ∧ ∀ j, b j * t = d * c j := by
  intro A _ _ _ _ m b d hd ⟨j₁, hj₁⟩
  classical
  obtain ⟨P, hP, h1, hdP, hno⟩ : ∃ P : Ideal A, P.IsPrime ∧ P.height = 1 ∧ d ∈ P ∧
      ¬ ∃ s, s ∉ P ∧ d ∣ s * b j₁ := by
    by_contra hcon
    refine hj₁ (GlobalTheory.dvd_of_forall_height_eq_one hd fun P hP h1 hdP => ?_)
    by_contra hn
    exact hcon ⟨P, hP, h1, hdP, hn⟩
  have hmul : ∀ {x y : A}, x ∉ P → y ∉ P → x * y ∉ P := fun hx hy h =>
    (hP.mem_or_mem h).elim hx hy
  obtain ⟨j₀, hj₀⟩ := exists_least_of_total (fun i j => ∃ s, s ∉ P ∧ b i ∣ s * b j)
    (fun i j => GlobalTheory.ShFam.BdArc.dvd_or_dvd_of_height_eq_one P h1 (b i) (b j))
    (by
      rintro i j k ⟨s, hs, u, hu⟩ ⟨s', hs', u', hu'⟩
      refine ⟨s * s', hmul hs hs', u * u', ?_⟩
      rw [mul_assoc, hu', ← mul_assoc, hu, mul_assoc]) j₁ Finset.univ
  choose s hs hsd using fun j => hj₀ j (Finset.mem_univ j)
  have hS : (∏ j, s j) ∉ P := by
    intro h
    obtain ⟨j, -, hj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 h
    exact hs j hj
  have hdiv : ∀ j, b j₀ ∣ (∏ j, s j) * b j := fun j =>
    (hsd j).trans (mul_dvd_mul_right (Finset.dvd_prod_of_mem s (Finset.mem_univ j)) _)
  generalize (∏ j, s j) = S at hS hdiv
  choose c hc using hdiv
  have hno' : ∀ x, x ∉ P → ¬ d ∣ x * b j₀ := by
    intro x hx h
    refine hno ⟨x * S, hmul hx hS, ?_⟩
    rw [mul_assoc, hc j₁, ← mul_assoc]
    exact h.mul_right _
  have hb0 : b j₀ ≠ 0 := fun h => hno' S hS (by rw [h, mul_zero]; exact dvd_zero d)
  have hcS : c j₀ = S := mul_left_cancel₀ hb0 (by rw [← hc j₀, mul_comm])
  obtain ⟨s', hs', t', ht'⟩ := (GlobalTheory.ShFam.BdArc.dvd_or_dvd_of_height_eq_one P h1 d (b j₀)).resolve_left
    (fun ⟨x, hx, h⟩ => hno' x hx h)
  have ht'P : t' ∈ P := by
    by_contra hn
    exact hno' t' hn ⟨s', by rw [mul_comm t', ← ht', mul_comm]⟩
  refine ⟨P, S * t', fun j => s' * c j, j₀, hP, hdP, P.mul_mem_left _ ht'P, ?_, fun j => ?_⟩
  · simp only [hcS]
    exact hmul hs' hS
  · have := hc j
    simp only
    linear_combination t' * this - c j * ht'
