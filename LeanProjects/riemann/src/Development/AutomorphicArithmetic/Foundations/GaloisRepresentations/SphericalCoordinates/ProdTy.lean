import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

open scoped Classical in
private theorem prod_ty {F : Type} [Field F] {g : ℕ} [Fintype (F →+* ℂ)]
    (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ)
    (f : (F →+* ℂ) → ℂ → ℂ) :
    ∏ i, f (ty i) (ev i) = ∏ τ, ((evAt ty ev τ).map (f τ)).prod := by
  unfold evAt
  simp only [Multiset.map_map, Function.comp_def]
  rw [← Finset.prod_fiberwise Finset.univ ty (fun i => f (ty i) (ev i))]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun i hi => ?_
  simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [hi]

open scoped Classical in
theorem UpperTheory.Gal.W2.fibW_of :
    UpperTheory.Gal.W2.FibW := by
  intro F _ _ g n t₀ ε ty ev χ mu hcx hn heps hcard hrts hmu x y
  have invol := ComplexEmbedding.involutive_conjugate F
  obtain ⟨A, hA'⟩ : ∃ A : (F →+* ℂ) → ℂ,
      ∀ τ, A τ = ((evAt ty ev τ).map (fun r => 1 - τ x * (y * r))).prod := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B : (F →+* ℂ) → ℂ, ∀ τ, B τ =
      ((evAt ty ev (ComplexEmbedding.conjugate τ)).map
        (fun r => 1 - τ x * starRingEnd ℂ r)).prod := ⟨_, fun _ => rfl⟩
  have hA : ∏ i, (1 - ty i x * (y * ev i)) = ∏ τ, A τ := by
    simp only [hA']
    exact prod_ty ty ev (fun τ r => 1 - τ x * (y * r))
  have hB : starRingEnd ℂ (∏ i, (1 - ty i x * ev i)) = ∏ τ, B τ := by
    rw [map_prod]
    simp only [map_sub, map_one, map_mul]
    rw [prod_ty ty ev (fun τ r => 1 - starRingEnd ℂ (τ x) * starRingEnd ℂ r)]
    refine (Equiv.prod_comp (invol.toPerm _) _).symm.trans
      (Finset.prod_congr rfl fun τ _ => ?_)
    simp [hB', Function.Involutive.coe_toPerm, ComplexEmbedding.conjugate_coe_eq]
  have hmem : ComplexEmbedding.conjugate t₀ ∈ Finset.univ.erase t₀ :=
    Finset.mem_erase.2 ⟨hcx t₀, Finset.mem_univ _⟩
  have key : ∏ τ, (A τ * B τ) = A t₀ * B t₀ *
      (A (ComplexEmbedding.conjugate t₀) * B (ComplexEmbedding.conjugate t₀) *
        ∏ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), (A τ * B τ)) := by
    rw [Finset.mul_prod_erase _ (fun τ => A τ * B τ) hmem,
      Finset.mul_prod_erase _ (fun τ => A τ * B τ) (Finset.mem_univ t₀)]
  have hrest : ∏ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), (A τ * B τ) =
      ∏ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀),
        ((rts χ τ).map (fun r => 1 - τ x * (y ^ ε τ * r))).prod := by
    refine Finset.prod_congr rfl fun τ hτ => ?_
    have h1 : τ ≠ ComplexEmbedding.conjugate t₀ := (Finset.mem_erase.1 hτ).1
    have h2 : τ ≠ t₀ := (Finset.mem_erase.1 (Finset.mem_erase.1 hτ).2).1
    have h3 : ComplexEmbedding.conjugate τ ≠ t₀ := fun h => h1 (by rw [← h, invol])
    have h4 : ComplexEmbedding.conjugate τ ≠ ComplexEmbedding.conjugate t₀ :=
      fun h => h2 (invol.injective h)
    have he := heps τ h2 h1
    have hc1 : (evAt ty ev τ).card = n * ε τ := by simp [hcard, typeMult, h1, h2]
    have hc2 : (evAt ty ev (ComplexEmbedding.conjugate τ)).card =
        n * ε (ComplexEmbedding.conjugate τ) := by simp [hcard, typeMult, h3, h4]
    rw [hA', hB', hrts, evFull, Multiset.map_add, Multiset.prod_add, Multiset.map_map]
    rcases (by omega : ε τ = 0 ∧ ε (ComplexEmbedding.conjugate τ) = 1 ∨
        ε τ = 1 ∧ ε (ComplexEmbedding.conjugate τ) = 0) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, Nat.mul_zero, Multiset.card_eq_zero] at hc1
      rw [hc1, e1]
      simp [Function.comp_def]
    · rw [e2, Nat.mul_zero, Multiset.card_eq_zero] at hc2
      rw [hc2, e1]
      simp [Function.comp_def]
  have hr0 : (rts χ t₀).erase mu = (evAt ty ev (ComplexEmbedding.conjugate t₀)).map (starRingEnd ℂ) := by
    rw [hrts, evFull, hmu, Multiset.singleton_add, Multiset.erase_cons_head]
  have hpair : A t₀ * B t₀ * (A (ComplexEmbedding.conjugate t₀) * B (ComplexEmbedding.conjugate t₀)) =
      (1 - t₀ x * (y * mu)) * (((rts χ t₀).erase mu).map (fun r => 1 - t₀ x * r)).prod *
        ((1 - starRingEnd ℂ (t₀ x) * starRingEnd ℂ mu) *
          (((rts χ t₀).erase mu).map
            (fun r => 1 - starRingEnd ℂ (t₀ x) * (y * starRingEnd ℂ r))).prod) := by
    rw [hr0, hA', hA', hB', hB', invol t₀, hmu]
    simp only [Multiset.map_map, Function.comp_def, Multiset.map_singleton, Multiset.prod_singleton,
      ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
    ring
  rw [hA, hB, ← Finset.prod_mul_distrib, key, hrest]
  unfold fibW
  rw [← hpair]
  ring
