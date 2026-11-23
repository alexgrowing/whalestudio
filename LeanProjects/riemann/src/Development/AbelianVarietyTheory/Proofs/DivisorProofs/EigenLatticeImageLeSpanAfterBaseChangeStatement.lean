import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenLatticeImageLeSpanAfterBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenLattice_image_le_span_after_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G))
    (f' : Fin n → (A'.t.G ⟶ B'.t.G)) (g' : Fin n → (B'.t.G ⟶ A'.t.G)),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) → (∀ i, Serre.IsLinearHom A'.t.act B'.t.act (f' i)) →
    (∀ i, Serre.IsLinearHom B'.t.act A'.t.act (g' i)) → (∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) →
    ∏ i, (g' i ≫ f' i) = 𝟙 B'.t.G →
    ∀ (FA : GenFib A.pol) (FB : GenFib B.pol) (M : Fin n → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
    (∀ i, FA.IsDiffOf FB (f i) (M i)) → ∀ (τ : 𝓞 E →+* 𝓞 K), ∀ w ∈ FB.eigLat B.t.act τ,
    (fun k => j (w k)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin FB.P₀.g → K) k => j (c k)) ''
      {v | ∃ i, ∃ e ∈ FA.eigLat A.t.act τ, v = M i e}) := by
  first | exact @GlobalTheory.CM.LieSpanBaseChange.eigLat_image_le_span_diff | exact GlobalTheory.CM.LieSpanBaseChange.eigLat_image_le_span_diff | (intros; apply GlobalTheory.CM.LieSpanBaseChange.eigLat_image_le_span_diff <;> assumption)
