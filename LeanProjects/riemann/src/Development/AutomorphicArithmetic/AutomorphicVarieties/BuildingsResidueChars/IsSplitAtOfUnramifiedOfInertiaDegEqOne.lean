import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

theorem UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → w.asIdeal.inertiaDeg ℤ = 1 → IsSplitAt w := by
  intro E _ _ _ w hun hf
  classical
  set F := maximalRealSubfield E
  set P : Ideal (𝓞 E) := w.asIdeal
  set p : Ideal (𝓞 F) := P.under (𝓞 F)
  have hfin : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F E
  have he : P.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one P (𝓞 F)
  have hf' : P.inertiaDeg (𝓞 F) = 1 := by
    have h := Ideal.inertiaDeg_tower (R := ℤ) p P
    rw [hf] at h
    exact (Nat.eq_one_of_mul_eq_one_left h.symm)
  by_contra hns
  have hone : ∀ q : p.primesOver (𝓞 E), q.1 = P := by
    intro q
    by_contra hq
    apply hns
    have hq0 : q.1 ≠ ⊥ := by
      intro h0
      have hP0 : p = ⊥ := by
        have := q.2.2
        rw [Ideal.liesOver_iff, h0] at this
        rw [this]
        exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      apply w.ne_bot
      exact Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 F) hP0
    refine ⟨⟨q.1, q.2.1, hq0⟩, ?_, ?_⟩
    · intro h
      exact hq (congrArg HeightOneSpectrum.asIdeal h)
    · ext1
      change Ideal.under (𝓞 F) q.1 = p
      exact (Ideal.liesOver_iff _ _).mp q.2.2 |>.symm
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hPmem : P ∈ p.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  have huniq : (Finset.univ : Finset (p.primesOver (𝓞 E))) = {⟨P, hPmem⟩} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subtype.ext (hone q)
  rw [huniq, Finset.sum_singleton, he, hf', hfin] at hsum
  omega
