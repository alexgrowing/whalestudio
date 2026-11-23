import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.basis :
    ∀ (l : ℕ) [Fact l.Prime] (E E' : IntermediateField ℚ_[l] (Qbar l)) [FiniteDimensional ℚ_[l] ↥E'], E ≤ E' → ∃ (d : ℕ) (ε : Fin d → Qbar l) (π : Fin d → (Qbar l →ₗ[↥E] ↥E)), (∀ x ∈ E', x = ∑ i, ε i * (π i x : Qbar l)) ∧ ∀ i, ContinuousOn (π i) (E' : Set (Qbar l)) := by
  intro l _ E E' _ h
  let V : Submodule (↥E) (Qbar l) := (IntermediateField.extendScalars h).toSubalgebra.toSubmodule
  have hV : ∀ x, x ∈ V ↔ x ∈ E' := fun x => Iff.rfl
  haveI : Module.Finite ℚ_[l] V := by
    let f : ↥E' →ₗ[ℚ_[l]] V :=
      { toFun := fun x => ⟨x.1, (hV _).2 x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact Module.Finite.of_surjective f (fun y => ⟨⟨y.1, (hV _).1 y.2⟩, rfl⟩)
  haveI : Module.Finite (↥E) V := Module.Finite.of_restrictScalars_finite ℚ_[l] (↥E) V
  let b := Module.finBasis (↥E) V
  choose π hπ using fun i => LinearMap.exists_extend (b.coord i)
  refine ⟨_, fun i => (b i : Qbar l), π, ?_, ?_⟩
  · intro x hx
    have h1 := congrArg (fun y : V => (y : Qbar l)) (b.sum_repr ⟨x, (hV _).2 hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    refine h1.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    have h2 : π i x = b.repr ⟨x, (hV _).2 hx⟩ i := by
      have := LinearMap.congr_fun (hπ i) ⟨x, (hV _).2 hx⟩
      simpa using this
    rw [h2, mul_comm]
    rfl
  · intro i
    rw [continuousOn_iff_continuous_restrict]
    let g : ↥E' →ₗ[ℚ_[l]] ↥E := ((π i).restrictScalars ℚ_[l]).comp E'.val.toLinearMap
    exact g.continuous_of_finiteDimensional
