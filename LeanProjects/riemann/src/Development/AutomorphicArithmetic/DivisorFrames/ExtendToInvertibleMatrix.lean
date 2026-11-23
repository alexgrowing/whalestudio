import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.TriFrDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

theorem UpperTheory.extend_to_invertible_matrix :
    ∀ (A : Type) [CommRing A] [Nontrivial A] (n g : ℕ) (v : Fin n → Fin g → A) (s : Fin n → Fin g), IsUnit (minor v le_rfl s) → ∃ (e : Fin n ↪ Fin g) (B : Matrix (Fin g) (Fin g) A), IsUnit B.det ∧ ∀ m, B (e m) = v m := by
  intro A _ _ n g v s h
  classical
  have h' : IsUnit (Matrix.of fun l i => v l (s i) : Matrix (Fin n) (Fin n) A).det := h
  have hs : Function.Injective s := by
    intro i j hij
    by_contra hne
    have : (Matrix.of fun l i => v l (s i) : Matrix (Fin n) (Fin n) A).det = 0 :=
      Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])
    rw [this] at h'
    exact not_isUnit_zero h'
  let E : Fin n ⊕ {x : Fin g // ¬ x ∈ Set.range s} ≃ Fin g :=
    (Equiv.sumCongr (Equiv.ofInjective s hs) (Equiv.refl _)).trans
      (Equiv.sumCompl (fun x => x ∈ Set.range s))
  have hE : ∀ m, E (Sum.inl m) = s m := fun m => rfl
  let C : Matrix (Fin n ⊕ {x : Fin g // ¬ x ∈ Set.range s})
      (Fin n ⊕ {x : Fin g // ¬ x ∈ Set.range s}) A :=
    Matrix.fromBlocks (Matrix.of fun l i => v l (s i)) (Matrix.of fun l i => v l i.1) 0 1
  refine ⟨⟨s, hs⟩, Matrix.reindex E E C, ?_, ?_⟩
  · rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    exact h'
  · intro m
    funext j
    obtain ⟨k, rfl⟩ := E.surjective j
    have h1 : (Matrix.reindex E E C) (E (Sum.inl m)) (E k) = C (Sum.inl m) k := by
      simp [Matrix.reindex_apply]
    change (Matrix.reindex E E C) (E (Sum.inl m)) (E k) = _
    rw [h1]
    cases k with
    | inl k => rfl
    | inr k => rfl
