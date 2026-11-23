import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolAdapted
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialControlUniformDelta
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix
open scoped ComplexOrder
open GlobalTheory.ShFam.Hor GlobalTheory.HermFrame GlobalTheory.Toroidal

private theorem UpperTheory.exists_compact_nbhd_chart {X E : Type} [TopologicalSpace X] [TopologicalSpace E] [LocallyCompactSpace E]
    (e : OpenPartialHomeomorph X E) {y₀ : X} (hy : y₀ ∈ e.source) :
    ∃ V L : Set X, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ L ∧ IsCompact L ∧ L ⊆ e.source := by
  obtain ⟨K, hK, hKt, hKc⟩ := local_compact_nhds (e.open_target.mem_nhds (e.map_source hy))
  refine ⟨e.source ∩ e ⁻¹' interior K, e.symm '' K, e.isOpen_inter_preimage isOpen_interior,
    ⟨hy, mem_interior_iff_mem_nhds.2 hK⟩, ?_, hKc.image_of_continuousOn (e.continuousOn_symm.mono hKt), ?_⟩
  · rintro y ⟨h1, h2⟩
    exact ⟨e y, interior_subset h2, e.left_inv h1⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact e.map_target (hKt hv)

theorem UpperTheory.chart_metric_lower_bound :
    OnCore fun D O x P => ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (y₀ : GlobalTheory.CxPts (O.var c).str σ), y₀ ∈ ch.e.source →
      ∃ (V : Set (GlobalTheory.CxPts (O.var c).str σ)) (c₀ : ℝ), IsOpen V ∧ y₀ ∈ V ∧ V ⊆ ch.e.source ∧ 0 < c₀ ∧
        ∀ y ∈ V, ∀ ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim, c₀ * ‖ξ‖ ≤ √(P.om c σ ch y ξ.ofLp) := by
  intro D O x P _ _ _ c σ ch y₀ hy₀
  have hka : IsKaehlerForm (GlobalTheory.AnRead.all (O.var c).str σ (O.var c).dim) (P.om c σ) := P.om_kaehler c σ
  obtain ⟨V, L, hVo, hyV, hVL, hL, hLs⟩ := UpperTheory.exists_compact_nbhd_chart ch.e hy₀
  obtain ⟨m, hm, hmL⟩ := GlobalTheory.ChernReg.ExphOn.exists_mul_norm_sq_le hka ch hL hLs
  refine ⟨V, √m, hVo, hyV, hVL.trans hLs, Real.sqrt_pos.2 hm, fun y hy ξ => ?_⟩
  refine Real.le_sqrt_of_sq_le ?_
  rw [mul_pow, Real.sq_sqrt hm.le]
  exact hmL y (hVL hy) ξ
