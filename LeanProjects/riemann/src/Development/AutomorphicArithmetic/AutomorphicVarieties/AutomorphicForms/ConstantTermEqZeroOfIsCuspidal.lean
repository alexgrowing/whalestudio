import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

open MeasureTheory in
theorem UpperTheory.constantTerm_eq_zero_of_isCuspidal :
    UpperTheory.V.Fb.CuspTo := by
  intro E _ _ a φ _ _ h r h0 h1 g
  have hμ : (unipMeasure E a r).IsAddHaarMeasure := inferInstance
  have hB : BorelSpace (UPos a r → AdeleRing (𝓞 E) E) := inferInstance
  have hL : ratN E a r = unipLattice E a r := AddSubgroup.ext fun x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  have hu : ∀ x : UPos a r → AdeleRing (𝓞 E) E, unip x = unipGL x := fun x => Units.ext rfl
  have hF : IsAddFundamentalDomain (ratN E a r) (unipFundamentalDomain E a r) (unipMeasure E a r) := by
    rw [hL]; exact isAddFundamentalDomain_unipFundamentalDomain
  have key := h r h0 h1 (unipMeasure E a r) (unipFundamentalDomain E a r) hμ hF g
  simp only [hu] at key
  exact key
