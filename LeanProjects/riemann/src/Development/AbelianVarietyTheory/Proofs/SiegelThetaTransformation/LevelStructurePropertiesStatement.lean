import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n), X.Λ ∈ D.lats ∧ (∀ u k k', D.Red u k → D.Red u k' → k = k') ∧ (∀ γ, γ ∈ D.grp ↔ IsUn X γ ∧ ∃ k ∈ D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k) ∧ (∀ L ∈ D.lats, SelfD X (D.sh L) ∧ Submodule.span E (L : Set (Fin r → E)) = ⊤ ∧ (∀ L' ∈ D.lats, (D.sh L').toAddSubgroup.relIndex (D.sh L).toAddSubgroup = L'.toAddSubgroup.relIndex L.toAddSubgroup) ∧ ∀ γ ∈ D.grp, mapL γ L ∈ D.lats ∧ D.sh (mapL γ L) = mapL γ (D.sh L)) ∧ (∀ k : D.J, ‖((D.lam k : ℂˣ) : ℂ)‖ = 1) ∧ (∀ y y' : Matrix (Fin n) (Fin r) E, (∀ k, Cong X D.𝔪 (y k) (y' k)) → D.dat hn y = D.dat hn y') ∧ ∀ γ ∈ D.grp, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → ∀ y : Matrix (Fin n) (Fin r) E, D.dat hn (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) = (D.lam k : ℂˣ) * D.dat hn y := by
  first | exact @GlobalTheory.SW.level_laws | exact GlobalTheory.SW.level_laws | (intros; apply GlobalTheory.SW.level_laws <;> assumption)
