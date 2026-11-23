import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolydiscCmUniformization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polydisc_cm_uniformization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔞 𝔟 : FracId (FR E))
    (φ : I → E →+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), IsCMType φ → c ≠ ⊥ → ∀ s : ℕ, 1 ≤ s →
    ∀ z ∈ polydisc I, ∀ (ue : Fin (Module.finrank ℚ (FR E)) ≃ I) (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ))
      (τ : (FR E →+* ℝ) → ℂ) (lam : Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ j (x : FR E), (e j x : ℂ) = φ (ue j) (x : E)) → τ ∈ halfSpace (FR E) → (∀ j, lam j ≠ 0) →
      (∀ w : Fin (Module.finrank ℚ (FR E)) → ℂ, (∃ x ∈ lattice c y, w = fun j ↦ defCoord φ z x (ue j)) ↔
        ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt,
          w = fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j)))) →
      ∀ G, IsEis 𝔞 𝔟 (2 * s) G → ∀ g, IsDefSum φ (2 * s) (lattice c y) g →
        g z = (cWt E (2 * s) : ℂ) * ((∏ j, lam j)⁻¹) ^ (2 * s) * G τ := by
  first | exact @GlobalTheory.LatSumCmp.defSum_eq_eis | exact GlobalTheory.LatSumCmp.defSum_eq_eis | (intros; apply GlobalTheory.LatSumCmp.defSum_eq_eis <;> assumption)
