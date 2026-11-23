import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNonnegCurveDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelSectionsLinearRingOfIntegersStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem valR_algX_cxPts {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (τ : k →+* ℂ)
    (U : Y.Opens) (y : GlobalTheory.CxPts p τ) (h : ⊤ ≤ y.1 ⁻¹ᵁ U) (a : k) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 U (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U a) = τ a := by
  have h1 := GlobalTheory.Points.valR_appLE y.1 p (U := ⊤) (V := U) (by simp) h
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)
  have h2 : y.1 ≫ p = Spec.map (CommRingCat.ofHom τ) := y.2
  rw [h2] at h1
  exact h1.trans (GlobalTheory.Points.valR_specMap (CommRingCat.ofHom τ) a)

theorem valR_section_sum : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (τ : 𝓞 K →+* ℂ) (i : L.B.ι) (y : GlobalTheory.CxPts p τ), y ∈ GlobalTheory.CxPts.ptsIn p τ (L.B.U i) → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s x).f i) = ∑ k, τ (β k) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s (u k)).f i) := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev τ i y hy m β u x hx
  have h : ⊤ ≤ y.1 ⁻¹ᵁ L.B.U i := hy
  rw [GlobalTheory.T.imageModel_sections_linear_ringOfIntegers K V Ω Nm W ev D X p L ψ s hM hev m β u x hx i, GlobalTheory.Points.valR_eq _ _ h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← GlobalTheory.Points.valR_eq _ _ h, GlobalTheory.Points.valR_mul _ _ h, valR_algX_cxPts p τ _ y h]

end GlobalTheory.ImageModel
