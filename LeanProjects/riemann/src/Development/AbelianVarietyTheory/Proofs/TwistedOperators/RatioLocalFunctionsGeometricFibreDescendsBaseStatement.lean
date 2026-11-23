import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatioLocalFunctionsGeometricFibreDescendsBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratio_localFunctions_geometricFibre_descends_base : ∀ (T : Type) [CommRing T] [IsReduced T] (Y : Scheme.{0}) (q : Y ⟶ Sp T) (I₀ : Type) (U : I₀ → Y.Opens) (t t₀ : ∀ j, Γ(Y, U j)), Smooth q → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω), ∃ α : Ω, (∀ (j : I₀) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ → (w.appLE (U j) ⊤ h).hom (t j) = toΓ Ω α * (w.appLE (U j) ⊤ h).hom (t₀ j)) ∧ ∃ (j : I₀) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ ∧ (w.appLE (U j) ⊤ h).hom (t₀ j) ≠ 0) → ∃ a : T, ∀ j, t j = (q.appLE ⊤ (U j) le_top).hom (toΓ T a) * t₀ j := by
  first | exact @GlobalTheory.ratio_descends | exact GlobalTheory.ratio_descends | (intros; apply GlobalTheory.ratio_descends <;> assumption)
