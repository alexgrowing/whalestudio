import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuccessiveMinimaPositiveNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.successive_minima_positive_norms : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (g : ℕ) (J : Type) [Fintype J] (h : J → Fin g → C), (∀ c : Fin g → C, (∀ j, ∑ i, h j i * c i = 0) → c = 0) → ∀ (m : ℕ) (a : Fin m → Fin g → C), LinearIndependent C a → ∀ (N : Fin m → ℝ), (∀ l, N l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧ (∀ j, ‖∑ i, h j i * ∑ l', cf l' * a l' i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹}) → (∀ l, 0 < N l) ∧ ∀ (k : ℕ) (hk : k ≤ m), ∏ l : Fin k, N (Fin.castLE hk l) = ⨆ σ : Fin k → J, ‖∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s‖ := by
  first | exact @GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor | exact GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor | (intros; apply GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor <;> assumption)
