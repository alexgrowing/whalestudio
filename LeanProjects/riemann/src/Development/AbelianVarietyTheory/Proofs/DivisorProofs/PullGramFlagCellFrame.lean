import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackGramMatricesIndependentOfFrameStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pullGram_cell : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ z : CxPts Y.str σ, InCell E E' φ f A u (under z) → pullGram E H φ f hf (upM u * A.map φ) z = fun τ => upM (fun j => ratVal (u j) z) τ * H A (ptMap σ f hf z) τ * (upM (fun j => ratVal (u j) z) τ)ᴴ := by
  intro F _ σ X Y ι _ m E E' φ f hf hR _c A u H hH z hz
  obtain ⟨hA, hB⟩ := hz
  funext τ
  rw [(GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame F σ X Y ι m E E' φ f hf hR H hH z).2 A hA _ hB τ]
  have hd : ∀ τ, ((A.map φ) τ).det ≠ 0 := fun τ => by
    change ((A τ).map φ).det ≠ 0
    have := RingHom.map_det (φ : X.Fn →+* Y.Fn) (A τ)
    rw [RingHom.mapMatrix_apply] at this
    change ((A τ).map (φ : X.Fn →+* Y.Fn)).det ≠ 0
    rw [← this]
    exact (map_ne_zero _).2 (Fr.det_ne hA τ)
  have e : upM u * A.map φ * (A.map φ)⁻¹ = upM u := by rw [mul_assoc, Mat.mul_inv hd, mul_one]
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) z
  have h0 : ratVal (0 : Y.Fn) z = 0 := by simpa using hψ 0
  have h1 : ratVal (1 : Y.Fn) z = 1 := by simpa using hψ 1
  have hv : (upM u).map (ratVal · z) τ = upM (fun j => ratVal (u j) z) τ := by
    ext a b
    simp only [Mat.map, upM, upU, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp [h0, h1]
  rw [e, hv]

end GlobalTheory.FlagCell2
