import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedGeneratorUniqueGlobalFunctionsBase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_generator_unique_globalFunctions_base : ∀ {X X' Y S₀ : Scheme.{0}} {M : LB X} {M' : LB X'}, M.IsLB → M'.IsLB → ∀ {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ} (w : LB.Iso M' (LB.LinComb M ψ δ)), w.IsGen → ∀ {K K₁ : Type} [Fintype K] [Fintype K₁] {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}, FormEq (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2) φ ε₁ → ∀ {t' : LB.Gen (LB.LinComb M' φ' ε)}, t'.IsGen → ∀ {t : LB.Gen (LB.LinComb M φ ε₁)}, t.IsGen → ∀ (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 _ → Function.Surjective p.appTop.hom → (∀ (y : S₀) (J : (S₀ ⟶ X) → M.ι) (J' : (S₀ ⟶ X') → M'.ι), Good M y J → Good M' y J' → (∏ a, GlobalTheory.TensBal.isoV w y J J' (e ≫ φ' a) ^ ε a) * val t' e y J' = val t e y J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι), Good M z J → Good M' z J' → (∏ a, GlobalTheory.TensBal.isoV w z J J' (r ≫ φ' a) ^ ε a) * val t' r z J' = val t r z J := by
  first | exact @GlobalTheory.TensBalUniq.iso_unique | exact GlobalTheory.TensBalUniq.iso_unique | (intros; apply GlobalTheory.TensBalUniq.iso_unique <;> assumption)
