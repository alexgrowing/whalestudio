import Mathlib
import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.CrystallineUnitParts.UnitPart

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.HeckeGal Polynomial

namespace CompanionTheory.PRW.ACWD

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem finExt_isClosed (L : FinExt l) : IsClosed (L.1 : Set (Qbar l)) := by
  have := L.2
  exact L.1.toSubalgebra.toSubmodule.closed_of_finiteDimensional

theorem map_mem_of_gen (θ : E) (hθ : IntermediateField.adjoin ℚ {θ} = ⊤) (φ : E →+* Qbar l) (L : FinExt l)
    (h : φ θ ∈ L.1) (y : E) : φ y ∈ L.1 := by
  let T : Subfield E := L.1.toSubfield.comap φ
  have hq : ∀ q : ℚ, algebraMap ℚ E q ∈ T := fun q => by
    show φ (algebraMap ℚ E q) ∈ L.1
    rw [eq_ratCast, map_ratCast]
    exact SubfieldClass.ratCast_mem L.1 q
  let T' : IntermediateField ℚ E := T.toIntermediateField hq
  have h1 : IntermediateField.adjoin ℚ {θ} ≤ T' := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact h
  have h2 : y ∈ T' := h1 (hθ ▸ IntermediateField.mem_top)
  exact h2

theorem exists_big (L₁ : FinExt l) (k : ℕ) (hk : 0 < k) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ L₂ : FinExt l, L₁.1 ≤ L₂.1 ∧ (∀ z : Qbar l, z ^ k = 1 → z ∈ L₂.1) ∧
      ∀ (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}) (x : w.adicCompletion E), j.1 x ∈ L₂.1 := by
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ E
  haveI := finite_contEmb (l := l) w
  let S : Set (Qbar l) := ((X ^ k - 1 : ℚ_[l][X]).rootSet (Qbar l) : Set (Qbar l)) ∪
    Set.range (fun j : {j : w.adicCompletion E →+* Qbar l // Continuous j} => j.1 (algebraMap E _ θ))
  haveI : Finite S := Set.Finite.to_subtype (Set.Finite.union (Finset.finite_toSet _) (Set.finite_range _))
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let L₂ : FinExt l := ⟨L₁.1 ⊔ IntermediateField.adjoin ℚ_[l] S,
    haveI := L₁.2; IntermediateField.finiteDimensional_sup _ _⟩
  have hS : IntermediateField.adjoin ℚ_[l] S ≤ L₂.1 := le_sup_right
  refine ⟨L₂, le_sup_left, fun z hz => hS (IntermediateField.subset_adjoin _ _ (Or.inl ?_)), fun j x => ?_⟩
  · have hne : (X ^ k - 1 : ℚ_[l][X]) ≠ 0 := X_pow_sub_C_ne_zero hk 1
    rw [mem_rootSet]
    exact ⟨hne, by simp [hz]⟩
  · have hjθ : j.1 (algebraMap E _ θ) ∈ L₂.1 := hS (IntermediateField.subset_adjoin _ _ (Or.inr ⟨j, rfl⟩))
    have hE : ∀ y : E, j.1 (algebraMap E (w.adicCompletion E) y) ∈ L₂.1 := fun y =>
      map_mem_of_gen θ hθ (j.1.comp (algebraMap E (w.adicCompletion E))) L₂ hjθ y
    exact (HeightOneSpectrum.denseRange_algebraMap E w).induction_on x
      ((finExt_isClosed L₂).preimage j.2) hE

end CompanionTheory.PRW.ACWD

end
