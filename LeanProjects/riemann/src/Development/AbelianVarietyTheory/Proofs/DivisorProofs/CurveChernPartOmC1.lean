import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConstantOneMemNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame

namespace GlobalTheory.CurveChernPart

theorem dens_ofValues (α : ReciprocityTheory.L2DbarEstimates.V 1 → ReciprocityTheory.L2DbarEstimates.V 1 → ℂ) :
    (dens ((ofValues α : Ev 1) : Alt 1)).re = 2 * diagVal α (EuclideanSpace.single 0 1) := by
  have e : (ofValues α : Ev 1) =
      (2 * (-Complex.I * α (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1))) • vol 1 := by
    simp only [ofValues, vol, Fin.sum_univ_one, Fin.prod_univ_one, smul_smul]
    congr 1
    linear_combination (α (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)) * Complex.I_mul_I
  have e' (c : ℂ) : dens ((c • vol 1 : Ev 1) : Alt 1) = c * dens (vol 1 : Alt 1) := by
    simp [dens, mul_div_assoc]
  rw [e, e', dens_vol, mul_one, diagVal]
  simp

theorem glue_congr {M ι : Type} [TopologicalSpace M] [MeasurableSpace M] {n : ℕ}
    (e : ι → OpenPartialHomeomorph M (ReciprocityTheory.L2DbarEstimates.V n)) {ρ ρ' : ι → M → ENNReal}
    (H : ∀ i, ∀ y ∈ (e i).source, ρ i y = ρ' i y) :
    ChartGlue.glueMeas e ρ = ChartGlue.glueMeas e ρ' := by
  refine iSup_congr fun i => congrArg (Measure.map _) (withDensity_congr_ae ?_)
  filter_upwards [ae_restrict_mem (e i).open_target.measurableSet] with v hv
  exact H i _ ((e i).map_target hv)

theorem part_om_c1 : ∀ (B : BottChern) (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (h : IsRegVar p 1) (R : ArRing B h) (N : HermLB p) (σ : k →+* ℂ) (ε : ℤˣ),
    (h.atlas σ).part (h.coeFld (R.om (R.c1 N)) σ) ε = (N.φ σ).chernPart 1 ε := by
  intro B k _ X p h R L σ ε
  have key (c : AlgChart p σ 1) (y) (hy : y ∈ c.e.source) :
      (dens ((h.atlas σ).loc (h.coeFld (R.om (R.c1 L)) σ) c (c.e y))).re = c.chernDens (L.φ σ) y := by
    have h₁ := R.chernForm_firstChernClass L σ ⟨(c, y), hy⟩ _ (mem_pick (L.φ σ).isLB y)
    refine (congrArg (fun t => (dens t).re) ((h.atlas σ).loc_crd _ ⟨(c, y), hy⟩)).trans ?_
    refine (congrArg (fun t : Ev 1 => (dens (t : Alt 1)).re) h₁).trans ((dens_ofValues _).trans ?_)
    have hd := (L.cInf σ).contDiffAt c hy (mem_pick (L.φ σ).isLB y)
    have e : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
      rw [kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]; simp
    rw [AlgChart.chernDens, AlgChart.hess, Matrix.det_unique,
      CurveDens.cHess_apply_eq_ddbar (contDiffAt_ofReal_comp hd), diagVal, ddc,
      ← mul_assoc (-Complex.I), e, Complex.re_ofReal_mul, ← mul_assoc]
    congr 1
    simp only [Nat.factorial_one, Nat.cast_one, pow_one]
    have := Real.pi_pos
    field_simp
  exact glue_congr _ fun c y hy => congrArg (fun t => ENNReal.ofReal (_ * t)) (key c y hy)

end GlobalTheory.CurveChernPart
