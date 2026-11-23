import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplSpec

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.chainAbs :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing R] (s : MvPowerSeries σ Λ →+* R) (ii ann : Ideal R) (h d : ℕ) (q : Fin (h + 1) → Ideal R) (o : PatchedSupportCompletions s ii ann q d) (St : Ideal (R ⧸ ii) → Prop) (Th : ∀ i, Ideal (o.B i) → Prop), (∀ i, (q i).IsPrime ∧ ii ≤ q i) → (∀ p p', p ≤ p' → St p' → St p) → (∀ i (Z Q : Ideal (o.B i)), Z.IsPrime → Q.IsPrime → St (Z.comap (algebraMap (R ⧸ ii) (o.B i))) → (d : WithBot ℕ∞) ≤ ringKrullDim (o.B i ⧸ Z) → St (Q.comap (algebraMap (R ⧸ ii) (o.B i))) ∨ Th i Q → Z ≤ Q) → ∀ E : Fin h → Ideal (R ⧸ ii), (∀ i, (E i).IsPrime ∧ (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ E i) ∧ (E i).comap (Ideal.Quotient.mk ii) ≤ q i.castSucc ∧ (E i).comap (Ideal.Quotient.mk ii) ≤ q i.succ ∧ ∀ Q : Ideal (o.B i.castSucc), Q.IsPrime → Q.comap (algebraMap (R ⧸ ii) _) = E i → Th _ Q) → (∃ p : Ideal (R ⧸ ii), p.IsPrime ∧ (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ p) ∧ p.comap (Ideal.Quotient.mk ii) ≤ q 0 ∧ St p ∧ ann ≤ p.comap (Ideal.Quotient.mk ii)) → ∀ p : Ideal (R ⧸ ii), p.IsPrime → (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ p) → p.comap (Ideal.Quotient.mk ii) ≤ q (Fin.last h) → (St p ∨ ∀ Q : Ideal (o.B (Fin.last h)), Q.IsPrime → Q.comap (algebraMap (R ⧸ ii) _) = p → Th _ Q) → ann ≤ p.comap (Ideal.Quotient.mk ii) := by
  intro Λ R σ _ _ _ _ s ii ann h d q o St Th hq hSt hkey E hE h0 p hp hpX hpq hpS
  have hOver : ∀ (j : Fin (h + 1)) (P : Ideal (R ⧸ ii)), P.IsPrime →
      P.comap (Ideal.Quotient.mk ii) ≤ q j →
      ∃ Q : Ideal (o.B j), Q.IsPrime ∧ Q.comap (algebraMap (R ⧸ ii) (o.B j)) = P := by
    intro j P hP hle
    apply (IsCplAt.exists_prime_over (R ⧸ ii) _ (o.B j) (o.cpl j)).1 P hP
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ (hle hx)
  have hInv : ∀ j : Fin (h + 1), ∃ Z : Ideal (o.B j), Z.IsPrime ∧ o.S j ≤ Z ∧
      St (Z.comap (algebraMap (R ⧸ ii) (o.B j))) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      obtain ⟨p0, hp0, hp0X, hp0q, hp0St, hp0ann⟩ := h0
      obtain ⟨Q, hQ, hQc⟩ := hOver 0 p0 hp0 hp0q
      refine ⟨Q, hQ, ?_, by rw [hQc]; exact hp0St⟩
      refine (o.fib 0 Q hQ ?_).mpr ?_
      · intro a
        have hx := hp0X a
        rw [← hQc] at hx
        exact hx
      · rw [hQc]
        exact hp0ann
    | succ i ih =>
      obtain ⟨Z, hZ, hSZ, hStZ⟩ := ih
      obtain ⟨hEp, hEX, hEc, hEs, hETh⟩ := hE i
      obtain ⟨Q, hQ, hQc⟩ := hOver i.castSucc (E i) hEp hEc
      have hThQ := hETh Q hQ hQc
      obtain ⟨Z0, hZ0, hZ0le⟩ := Ideal.exists_minimalPrimes_le hSZ
      have hStZ0 := hSt _ _ (Ideal.comap_mono hZ0le) hStZ
      have hZ0Q := hkey i.castSucc Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) (Or.inr hThQ)
      have hQX : ∀ a, algebraMap (R ⧸ ii) (o.B i.castSucc)
          (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q := by
        intro a
        have hx := hEX a
        rw [← hQc] at hx
        exact hx
      obtain ⟨Z', hZ', hSZ', hZ'c⟩ := o.move i.castSucc i.succ Z0 Q hZ0.1.1 hQ hZ0.1.2 hZ0Q hQX
        (by rw [hQc]; exact hEs)
      exact ⟨Z', hZ', hSZ', by rw [hZ'c]; exact hStZ0⟩
  obtain ⟨Z, hZ, hSZ, hStZ⟩ := hInv (Fin.last h)
  obtain ⟨Q, hQ, hQc⟩ := hOver (Fin.last h) p hp hpq
  have hQX : ∀ a, algebraMap (R ⧸ ii) (o.B (Fin.last h))
      (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q := by
    intro a
    have hx := hpX a
    rw [← hQc] at hx
    exact hx
  obtain ⟨Z0, hZ0, hZ0le⟩ := Ideal.exists_minimalPrimes_le hSZ
  have hStZ0 := hSt _ _ (Ideal.comap_mono hZ0le) hStZ
  have hQc' : St (Q.comap (algebraMap (R ⧸ ii) (o.B (Fin.last h)))) ∨ Th (Fin.last h) Q := by
    rcases hpS with h1 | h1
    · left
      rw [hQc]
      exact h1
    · right
      exact h1 Q hQ hQc
  have hZ0Q := hkey (Fin.last h) Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) hQc'
  have hann := (o.fib _ Q hQ hQX).mp (hZ0.1.2.trans hZ0Q)
  rw [hQc] at hann
  exact hann
