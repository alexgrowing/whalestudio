import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticSectionIsAlgebraicStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HolomorphicGluingLocalFunctionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem gagaSections_pure : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (D : ℕ), IsProper s → SmoothOfRelativeDimension D s → ∀ (L : LB X), L.IsLB → ∀ h : L.ι → (Sp ℂ ⟶ X) → ℂ, (∀ (i : L.ι) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = 𝟙 _ ∧ ⊤ ≤ y b ⁻¹ᵁ L.U i) → DifferentiableOn ℂ (fun b => h i (y b)) B) → (∀ (i j : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) → h i x = valAt' x (L.U i ⊓ L.U j) (L.g i j).val * h j x) → ∃ σ : L.Sec, ∀ (i : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ L.U i → valAt' x (L.U i) (σ.f i) = h i x := by
  intro X s D hp hs L hL h hh hg
  obtain ⟨σ, hσ, e⟩ := GlobalTheory.T.holomorphic_gluing_local_functions X s D hs (AnRead.all s (RingHom.id ℂ) D) L hL h hh hg
  obtain ⟨t, ht⟩ := GlobalTheory.T.analytic_section_is_algebraic X s D hs hp (AnRead.all s (RingHom.id ℂ) D) L hL σ hσ
  refine ⟨t, fun i x hx hU => ?_⟩
  have hx' : x ≫ s = spMap (RingHom.id ℂ) := by
    rw [hx, spMap]; exact (by simp)
  let y : CxPts s (RingHom.id ℂ) := ⟨x, hx'⟩
  have hy : y ∈ ptsIn s (RingHom.id ℂ) (L.U i) := hU
  have h1 := e i y hy
  rw [← ht] at h1
  exact h1

end GlobalTheory.CompanionTheory.Gaga
