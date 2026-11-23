import Development.AutomorphicArithmetic.BlowupCategories.SpanScale

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.isIso_of_bijective_on_simplices :
    ∀ {S S' : Spc} (f : S ⟶ S'), (∀ (k : ℕ) (T : Scheme.{0}), Function.Bijective (fun x : Sx S k T => x.map f)) → IsIso f := by
  intro S S' f h
  haveI : ∀ n : SimplexCategoryᵒᵖ, IsIso (f.app n) := by
    intro n
    haveI : ∀ T : Schemeᵒᵖ, IsIso ((f.app n).app T) := by
      intro T
      obtain ⟨⟨k⟩⟩ := n
      obtain ⟨T⟩ := T
      rw [isIso_iff_bijective]
      exact h k T
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _
