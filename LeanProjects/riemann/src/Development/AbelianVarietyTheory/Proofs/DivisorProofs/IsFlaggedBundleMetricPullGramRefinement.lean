import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackGramMatricesIndependentOfFrameStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
open GlobalTheory.GoodMetric.RepBundle

namespace GlobalTheory.ChernCalc

theorem isMetricFr_pullGram : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → IsMetricFr E' (pullGram E H φ f hf) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH
  have key := GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame F σ X Y ι m E E' φ f hf hR H hH
  refine ⟨fun y B hB τ => ?_, fun y B hB τ i j => ?_, fun y B hB B' hB' τ => ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) y
    obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have hT := ((hR.sub _ B hB A hA).map_of (ratVal · y) ψ hψ).det_ne τ
    rw [(key y).2 A hA B hB τ]
    exact (hH.posDef _ mem_ptsIn_top A ((key y).1 ▸ hA) τ).mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hT.isUnit))
  · obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have hA' : A ∈ E.S (under (ptMap σ f hf y)) := (key y).1 ▸ hA
    have hC := hR.sub _ B hB A hA
    have hc : Continuous (ptMap σ f hf) := GlobalTheory.Points.PtsOver.continuous_map f hf _
    have hev : ∀ᶠ z in 𝓝 y, pullGram E H φ f hf B z τ = (B * (A.map φ)⁻¹).map (ratVal · z) τ *
        H A (ptMap σ f hf z) τ * ((B * (A.map φ)⁻¹).map (ratVal · z) τ)ᴴ := by
      filter_upwards [hc.continuousAt.eventually (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m 0 E _ A hA'),
        GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ Y ι m m E' y B hB] with z hAz hBz
      exact (key z).2 A ((key z).1 ▸ hAz) B hBz τ
    have hT : ∀ k l, CS (fun z => (B * (A.map φ)⁻¹).map (ratVal · z) τ k l) y := fun k l =>
      cs_ratVal (mem_O_ratOf.1 ((hC τ).1 k l))
    have hS : ∀ k l, CS (fun z => H A (ptMap σ f hf z) τ k l) y := fun k l =>
      ⟨CInfAt.pull f hf (hH.smooth _ mem_ptsIn_top A hA' τ k l).1,
        CInfAt.pull f hf (hH.smooth _ mem_ptsIn_top A hA' τ k l).2⟩
    exact CS.congr (v := fun z => pullGram E H φ f hf B z τ i j) (cs_conj_entry hT hS i j)
      (hev.mono fun z hz => by simp only [hz])
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) y
    obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have e := Par.map_mul_of ((Fr.mem_iff hB).1 hB') (hR.sub _ B hB A hA) (ratVal · y) ψ hψ
    rw [mul_assoc, ← mul_assoc B⁻¹, Mat.inv_mul (Fr.det_ne hB), one_mul] at e
    rw [(key y).2 A hA B hB τ, (key y).2 A hA B' hB' τ, e, Pi.mul_apply, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.ChernCalc
