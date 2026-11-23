import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainFrameLiftAlgebraicChartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameFormStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

theorem lieGram_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ ix : Fin X.dim ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q, ∃ (φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim) (g : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ) (cc : (E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧ AnalyticAt ℂ φ (c'.e y) ∧ (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) (c'.e y)) ∧ (∀ τ, IsUnit (g (c'.e y) τ).det) ∧ InDom (coordOf ix (φ (c'.e y))) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∀ τ, lieGram e U hj f₀ A₀ A (c'.e.symm w) τ = (cc τ : ℂ) • (g w τ * modelGram H Dw (coordOf ix (φ w)) τ * (g w τ)ᴴ) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hc' A hA ix
  obtain ⟨hoi, -, hT⟩ := hL
  obtain ⟨k', s, hs, hev⟩ := GlobalTheory.T.exists_analytic_flagDomain_frame_lift_algebraicChart E H Dw l Xo c O β Y T F e σ U hσ hU X j hj hoi y hy c' hc'
  obtain ⟨K, hK, hKu, hKev⟩ :=
    GlobalTheory.T.exists_holomorphic_invertible_frame_coordinates E H Dw l Xo c O β Y T F e σ U hσ hU X j f₀ Eb A₀ hj hoi hT y hy c' hc' A hA k' s hs hev
  obtain ⟨G, z, cc, hcc, hG⟩ := GlobalTheory.T.hodgeMetric_gram_holomorphic_frame_form E H Dw l Xo c O β T.Z σ U hσ hU k'
  obtain ⟨hs0, -⟩ := hev.self_of_nhds
  obtain ⟨hGa, hza, hGu, hzD, -⟩ := hG (s (c'.e y)) hs0
  let φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim := fun w =>
    (EuclideanSpace.equiv (Fin X.dim) ℂ).symm (fun i => z (s w) (ix i).1 (ix i).2.1 (ix i).2.2)
  have hco : ∀ w, coordOf ix (φ w) = z (s w) := fun w => by
    funext τ a b
    simp [φ, coordOf]
  refine ⟨φ, fun w τ => (K w τ)ᵀ * G (s w) τ, cc, hcc, ?_, ?_, ?_, ?_, ?_⟩
  · refine (EuclideanSpace.equiv (Fin X.dim) ℂ).symm.analyticAt _ |>.comp ?_
    refine analyticAt_pi_iff.2 fun i => ?_
    exact (hza (ix i).1 (ix i).2.1 (ix i).2.2).comp hs
  · intro τ a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.analyticAt_fun_sum Finset.univ (fun i _ => (hK τ i a).mul ((hGa τ i b).comp hs))
  · intro τ
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact (hKu τ).mul (hGu τ)
  · rw [hco]
    exact hzD
  · filter_upwards [hKev, hev] with w ⟨⟨g0, hg0⟩, hKw⟩ ⟨hsw, _⟩ τ
    have hex : ∃ g, FrameAt e f₀ A₀ A (c'.e.symm w) g := ⟨g0, hg0⟩
    rw [lieGram, dif_pos hex]
    show ((hodgeMet T.Z U).gram _ hex.choose τ)ᵀ = _
    rw [hKw hsw _ hex.choose_spec, Matrix.transpose_mul, Matrix.transpose_mul, (hG (s w) hsw).2.2.2.2 τ, hco]
    have hKt : ((K w τ)ᴴ)ᵀ = ((K w τ)ᵀ)ᴴ := by ext; simp
    rw [hKt]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end GlobalTheory.PointChern
