import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromSpecStalkMemZeroLocusIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DdcLogNormBoundedByKaehlerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjInvariantDivisorNormStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjCompatibleKaehlerFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjCompatibleLieMetricStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam

theorem conj_comp_ne_of_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) : (starRingEnd ℂ).comp σ ≠ σ := by
  intro h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal (Formalism.L2.PjFree.relab c σ τ) ?_
  rw [ComplexEmbedding.isReal_iff]
  exact RingHom.ext fun a => RingHom.congr_fun h _

theorem nonempty_toroidal_boundary_data (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)]
    (hsnc : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z)) : Nonempty (OddPrimesWithRootsOfUnity Z) := by
  have hp : IsProjOver (genStr Z) := ProjSpace.isProjOver_pullback_snd _ Z.proj
  have := isProper_genStr Z
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hc := conj_comp_ne_of_coeff c
  obtain ⟨m, C, hC, hE⟩ := GlobalTheory.SncComponents.exists_compList_effCartier c.F (gen Z) (genStr Z) Dw.dim (genBd Z) hsnc
  choose n hn hn' using fun i => GlobalTheory.T.exists_conj_invariant_divisor_norm c.F (gen Z) (genStr Z) Dw.dim (C i) hp hc (hE i)
  obtain ⟨a, ha, ha'⟩ := GlobalTheory.T.exists_conj_compatible_kaehler_forms c.F (gen Z) (genStr Z) Dw.dim hp
  obtain ⟨h, hh, hh'⟩ := GlobalTheory.T.exists_conj_compatible_lie_metric c.F (gen Z) (genStr Z) Dw.dim E H Z.X Z.t (genι Z) hp hc
  choose K hK using fun q : (c.F →+* ℂ) × Fin m =>
    GlobalTheory.T.ddc_log_norm_bounded_by_kaehler c.F (gen Z) (genStr Z) Dw.dim q.1 (C q.2) (n q.2 q.1) (a q.1) hp (hn q.2 q.1) (ha q.1)
  obtain ⟨K₀, hK₀⟩ := (Set.finite_range K).bddAbove
  have hM : 0 ≤ max K₀ 0 := le_max_right _ _
  have hD : 0 < 2 * (m : ℝ) * max K₀ 0 + 1 := by positivity
  refine ⟨{
    m := m, cpt := C, cpt_list := hC, nrm := fun σ i => n i σ, nrm_div := fun σ i => hn i σ,
    nrm_conj := fun σ σ' j hj i z => hn' i σ σ' j hj z, kae := a, kae_kaehler := ha, kae_conj := ha',
    cst := Real.exp 1 / (2 * m * max K₀ 0 + 1), cst_pos := by positivity, cst_small := ?_,
    met := h, met_smooth := hh, met_conj := hh' }⟩
  intro σ i ch y hy hi ξ
  by_cases hξ : ξ = 0
  · have h1 := hK (σ, i) ch y hy hi ξ
    have h0 : a σ ch y ξ = 0 := by
      obtain ⟨W, φ, hW, -, -, e⟩ := (ha σ).1 y
      rw [e ch y hy hW, hξ]
      simp [ddcForm, AlgChart.levi, ReciprocityTheory.L2DbarEstimates.leviV]
    rw [h0, mul_zero] at h1
    rw [h0, mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
  · have hpos := ((ha σ).2 ch y hy ξ hξ).le
    have h1 := (hK (σ, i) ch y hy hi ξ).trans
      (mul_le_mul_of_nonneg_right ((hK₀ ⟨(σ, i), rfl⟩).trans (le_max_left K₀ 0)) hpos)
    refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
    rw [← _root_.mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hpos
    rw [mul_right_comm, ← mul_div_assoc, div_le_iff₀ hD]
    have := Real.exp_pos 1
    nlinarith

end GlobalTheory.ShFam
