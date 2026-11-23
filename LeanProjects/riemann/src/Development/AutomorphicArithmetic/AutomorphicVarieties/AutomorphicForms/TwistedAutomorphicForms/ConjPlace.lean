import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

theorem UpperTheory.V.Af.Tw.conjPlace :
    UpperTheory.V.Af.Tw.ConjPlace := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h g hg w w' A hA hne hun
  haveI : Algebra.IsQuadraticExtension F L := ⟨h⟩
  have hc : Nat.card (L ≃ₐ[F] L) = 2 := (IsGalois.card_aut_eq_finrank F L).trans h
  obtain ⟨t, -, hu⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hc
  have h1 : g.restrictNormal L = t := by
    refine hu _ fun h1 => hg ?_
    refine ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun y => ?_, AlgEquiv.ext fun _ => rfl⟩
    have := AlgEquiv.restrictNormal_commutes g L y
    rw [h1] at this
    exact this.symm
  have hlift : ∀ x : L, g (algebraMap L Ω x) = algebraMap L Ω (t x) := fun x => by
    rw [← h1]
    exact (AlgEquiv.restrictNormal_commutes g L x).symm
  haveI := w.isPrime
  haveI := w'.isPrime
  haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  haveI : w'.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hun.symm⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal w.asIdeal w'.asIdeal
    (L ≃ₐ[F] L)
  obtain rfl : σ = t := hu σ fun h0 => hne (HeightOneSpectrum.ext (by rw [← hσ, h0, one_smul]))
  have hA' : ∀ x, g.toRingEquiv x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨g • A, fun x => ?_, fun s s' hs => ?_⟩
  · obtain ⟨y, rfl⟩ := MulAction.surjective σ x
    rw [← hσ, Ideal.smul_mem_pointwise_smul_iff, ← hA y, ← val_lt_one hA']
    have h2 : g.toRingEquiv (algebraMap L Ω (y : L)) = algebraMap L Ω ((σ • y : 𝓞 L) : L) := hlift y
    rw [h2]
  · have hss : ∀ x, s' (g x) = g (s x) := fun x => by
      refine (DFunLike.congr_fun hs (g x)).trans ?_
      show g (s (g.symm (g x))) = _
      rw [AlgEquiv.symm_apply_apply]
    have hD : s ∈ Dec (F := L) A → s' ∈ Dec (F := L) (g • A) := fun hs0 => by
      refine mem_Dec.2 ?_
      show resG F L Ω s' • g • A = g • A
      have h3 : resG F L Ω s • A = A := mem_Dec.1 hs0
      rw [hs, ← mul_smul, inv_mul_cancel_right, mul_smul, h3]
    have hle : ∀ y, (g • A).valuation (g y) ≤ 1 → A.valuation y ≤ 1 := fun y hy =>
      (A.valuation_le_one_iff _).2 ((hA' y).1 (((g • A).valuation_le_one_iff _).1 hy))
    refine ⟨fun hI => ⟨hD hI.1, fun x hx => ?_⟩, fun q hF => ⟨hD hF.1, fun x hx => ?_⟩⟩
    · obtain ⟨y, rfl⟩ := g.surjective x
      rw [hss, ← map_sub]
      exact (val_lt_one hA' _).2 (hI.2 y (hle y hx))
    · obtain ⟨y, rfl⟩ := g.surjective x
      rw [hss, ← map_pow, ← map_sub]
      exact (val_lt_one hA' _).2 (hF.2 y (hle y hx))
