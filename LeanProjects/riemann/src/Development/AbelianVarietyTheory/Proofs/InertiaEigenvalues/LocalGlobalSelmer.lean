import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

namespace GlobalTheory.Proof.LocalGlobalSelmer

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i) (k : ℕ) (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)), InR' D.nd r S 1 → UnrOut i r Xs → ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i (cocW i r S Xs ψ) v = ⊥ := by
  intro D i r Xs S k ψ hone hU v h1 h2 h3
  have hY : ∀ γ, InY D.nd r S (yg D.nd r S γ) := fun γ =>
    ⟨1, fun _ => 1, fun _ => γ, fun _ => hone, by simp⟩
  have hy : ∀ γ x', yg D.nd r S γ x' = (rTwO D.nd i r (S.p x') γ - 1) * Eel D.nd S x' := by
    intro γ x'
    simp [yg, rTwO, twistM, sub_mul]
  rw [resIne, cocW, Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨_, ⟨φ, -, h0, rfl⟩, rfl⟩
  funext γ
  exact h0 _ (hY γ.1) fun x' hx => by rw [hy, hU v h1 h2 h3 _ hx γ.1 γ.2]; simp

end GlobalTheory.Proof.LocalGlobalSelmer
