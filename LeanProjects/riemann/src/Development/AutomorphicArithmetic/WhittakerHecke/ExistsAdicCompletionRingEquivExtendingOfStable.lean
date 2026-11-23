import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBaseChangePlaces
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

private lemma intValuation_le_of_equiv {L : Type} [Field L] [NumberField L]
    (u : HeightOneSpectrum (𝓞 L)) (σ : 𝓞 L ≃+* 𝓞 L)
    (h : ∀ x : 𝓞 L, σ x ∈ u.asIdeal ↔ x ∈ u.asIdeal) (r : 𝓞 L) :
    u.intValuation (σ r) ≤ u.intValuation r := by
  by_cases hr : r = 0
  · simp [hr]
  have hc : Ideal.comap (σ : 𝓞 L →+* 𝓞 L) u.asIdeal = u.asIdeal := by
    ext x; exact h x
  have hm : ∀ n : ℕ, Ideal.comap (σ : 𝓞 L →+* 𝓞 L) (u.asIdeal ^ n) = u.asIdeal ^ n := fun n => by
    have e : Ideal.comap (σ : 𝓞 L →+* 𝓞 L) (u.asIdeal ^ n) =
        Ideal.map (σ.symm : 𝓞 L →+* 𝓞 L) (u.asIdeal ^ n) := Ideal.comap_symm (I := u.asIdeal ^ n) σ.symm
    have e1 : Ideal.map (σ.symm : 𝓞 L →+* 𝓞 L) u.asIdeal = u.asIdeal := by
      have e2 : Ideal.comap (σ : 𝓞 L →+* 𝓞 L) u.asIdeal =
          Ideal.map (σ.symm : 𝓞 L →+* 𝓞 L) u.asIdeal := Ideal.comap_symm (I := u.asIdeal) σ.symm
      rw [← e2, hc]
    rw [e, Ideal.map_pow, e1]
  rw [HeightOneSpectrum.intValuation_if_neg u hr]
  have hmem : r ∈ u.asIdeal ^ ((Associates.mk u.asIdeal).count
      (Associates.mk (Ideal.span {r})).factors) := by
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_if_neg u hr]
  have hmem' : σ r ∈ u.asIdeal ^ ((Associates.mk u.asIdeal).count
      (Associates.mk (Ideal.span {r})).factors) := by
    have := hm ((Associates.mk u.asIdeal).count (Associates.mk (Ideal.span {r})).factors)
    rw [← this] at hmem
    exact hmem
  exact (HeightOneSpectrum.intValuation_le_pow_iff_mem u _ _).2 hmem'

private lemma intValuation_eq_of_equiv {L : Type} [Field L] [NumberField L]
    (u : HeightOneSpectrum (𝓞 L)) (σ : 𝓞 L ≃+* 𝓞 L)
    (h : ∀ x : 𝓞 L, σ x ∈ u.asIdeal ↔ x ∈ u.asIdeal) (r : 𝓞 L) :
    u.intValuation (σ r) = u.intValuation r := by
  refine le_antisymm (intValuation_le_of_equiv u σ h r) ?_
  have h' : ∀ x : 𝓞 L, σ.symm x ∈ u.asIdeal ↔ x ∈ u.asIdeal := fun x => by
    rw [← h (σ.symm x), σ.apply_symm_apply]
  simpa using intValuation_le_of_equiv u σ.symm h' (σ r)

private lemma valuation_eq_of_equiv {L : Type} [Field L] [NumberField L]
    (u : HeightOneSpectrum (𝓞 L)) (s : L ≃+* L)
    (h : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom (s : L →+* L) x ∈ u.asIdeal ↔ x ∈ u.asIdeal) (y : L) :
    u.valuation L (s y) = u.valuation L y := by
  let σ : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv s
  have hσ : ∀ x : 𝓞 L, σ x ∈ u.asIdeal ↔ x ∈ u.asIdeal := fun x => h x
  have key : ∀ a : 𝓞 L, u.valuation L (s (algebraMap (𝓞 L) L a)) =
      u.valuation L (algebraMap (𝓞 L) L a) := fun a => by
    have e : s (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L (σ a) := rfl
    rw [e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      intValuation_eq_of_equiv u σ hσ]
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) y
  rw [map_div₀, map_div₀, map_div₀, key, key]

open scoped WithZeroTopology in
theorem UpperTheory.exists_adicCompletion_ringEquiv_extending_of_stable :
    ∀ {L : Type} [Field L] [NumberField L] (u : HeightOneSpectrum (𝓞 L)) (s : L ≃+* L),
        (∀ x : 𝓞 L, RingOfIntegers.mapRingHom (s : L →+* L) x ∈ u.asIdeal ↔ x ∈ u.asIdeal) →
        ∃ i : u.adicCompletion L ≃+* u.adicCompletion L, Continuous i ∧
          (∀ x, i (algebraMap L _ x) = algebraMap L _ (s x)) ∧ ∀ x, Valued.v (i x) = Valued.v x := by
  intro L _ _ u s h
  have h' : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom (s.symm : L →+* L) x ∈ u.asIdeal ↔ x ∈ u.asIdeal := by
    intro x
    rw [← h (RingOfIntegers.mapRingHom (s.symm : L →+* L) x)]
    have e : RingOfIntegers.mapRingHom (s : L →+* L) (RingOfIntegers.mapRingHom (s.symm : L →+* L) x) = x := by
      apply RingOfIntegers.ext
      simp
    rw [e]
  obtain ⟨μ, hμc, hμ⟩ := GlobalTheory.CompositumCompletion.exists_completion_map (s : L →+* L) u u h
  obtain ⟨μ', hμ'c, hμ'⟩ := GlobalTheory.CompositumCompletion.exists_completion_map (s.symm : L →+* L) u u h'
  have h1 : ∀ a, μ' (μ a) = a := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap L u).equalizer (hμ'c.comp hμc) continuous_id
      (funext fun x => by simp [hμ, hμ'])) a
  have h2 : ∀ a, μ (μ' a) = a := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap L u).equalizer (hμc.comp hμ'c) continuous_id
      (funext fun x => by simp [hμ, hμ'])) a
  let i : u.adicCompletion L ≃+* u.adicCompletion L :=
    { μ with invFun := μ', left_inv := h1, right_inv := h2 }
  have hi : ∀ a, i a = μ a := fun _ => rfl
  refine ⟨i, hμc, fun x => hμ x, fun x => ?_⟩
  refine (HeightOneSpectrum.denseRange_algebraMap L u).induction_on
    (p := fun x => Valued.v (i x) = Valued.v x) x
    (isClosed_eq
      ((Valued.continuous_valuation_of_surjective (u.valuedAdicCompletion_surjective L)).comp hμc)
      (Valued.continuous_valuation_of_surjective (u.valuedAdicCompletion_surjective L))) fun k => ?_
  rw [hi, hμ]
  have e : ∀ y : L, Valued.v (algebraMap L (u.adicCompletion L) y) = u.valuation L y := fun y =>
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u y)
  rw [e, e]
  exact valuation_eq_of_equiv u s h k
