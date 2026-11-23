import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt

open NumberField in
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

theorem UpperTheory.V.Br.weakEx :
    UpperTheory.V.Br.WeakEx := by
  intro h F E _ _ hF _ _ hE _ h2 a ha π
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsGalois F E := inferInstance
  have hp : (Module.finrank F E).Prime := h2 ▸ Nat.prime_two
  rcases (h F E hp (Or.inl hF) (Or.inr hE) a ha).1 _ _ (Or.inr ⟨hF, π, rfl, rfl⟩) with h1 | ⟨sat', inf', hc, hw, hi⟩
  · exact Or.inl h1
  · rcases hc with ⟨_, P, rfl, rfl⟩ | ⟨hr, -⟩
    · refine Or.inr ⟨P, ⟨hi, ?_⟩⟩
      filter_upwards [hw] with w hw v hv f hf
      obtain rfl : v = w.under (NumberField.RingOfIntegers F) := IsDedekindDomain.HeightOneSpectrum.ext hv
      exact hw f hf
    · exact (not_both E hr hE).elim
