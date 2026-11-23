import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelAffineCoverRadical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_model_affine_cover_radical : ∀ (F : Type) [Field F] [NumberField F] (G T : Scheme.{0}) (s : G ⟶ Sp F) (S : Set G) (d : ℕ) (ι : G ⟶ T) (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ G) (ρ : X ⟶ T), IsPre s S d ι q jB πB ρ → ∀ (n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)) (N : Fin n → ℕ), (∀ j, IsAffineOpen (U j)) → (∀ j, N j ≠ 0) → (∀ j, (N j : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical) → ∃ (X' W' : Scheme.{0}) (b : X' ⟶ X) (jB' : W' ⟶ X') (πB' : W' ⟶ G), IsPre s S d ι (b ≫ q) jB' πB' (b ≫ ρ) ∧ ∀ (Y : Scheme.{0}) (ν : Y ⟶ X') (w : Y) (j : Fin n), (ν ≫ b) w ∈ U j → ∃ (V : Y.Opens) (hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', ((ν ≫ b).appLE (U j) V hV).hom (A j k) ∣ ((ν ≫ b).appLE (U j) V hV).hom (A j k') := by
  first | exact @GlobalTheory.ArLieBase.exists_blowup_principalises | exact GlobalTheory.ArLieBase.exists_blowup_principalises | (intros; apply GlobalTheory.ArLieBase.exists_blowup_principalises <;> assumption)
