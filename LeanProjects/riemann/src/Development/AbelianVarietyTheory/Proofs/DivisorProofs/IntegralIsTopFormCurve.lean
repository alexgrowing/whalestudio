import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.CxForm (IsRegVar dens)
open scoped ContDiff

namespace GlobalTheory.TorsionForm

theorem isTopForm_reDens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (h : IsRegVar p 1) (θ : h.Fld),
    (∀ σ, (h.atlas σ).IsForm (θ σ)) →
    IsTopForm (fun σ (c : AlgChart p σ 1) y => (dens ((h.atlas σ).loc (θ σ) c (c.e y))).re) (h.integral θ) := by
  intro k _ X p h θ hθ
  refine ⟨fun σ c => ⟨?_, fun c' y hy hy' => (h.atlas σ).reDens_compat (hθ σ) c c' y hy hy'⟩, fun σ ε => ?_, ?_⟩
  · have h1 : ContDiffOn ℝ ∞ (fun v => (dens ((h.atlas σ).loc (θ σ) c v)).re) c.e.target :=
      Complex.reCLM.contDiff.comp_contDiffOn (((hθ σ).smooth c Finset.univ).div_const _)
    refine h1.congr fun v hv => ?_
    simp only [Function.comp_apply, c.e.right_inv hv]
  · have := CxPts.compactSpace σ h.isProjOver
    have := secondCountableTopology_of_isProjOver (σ := σ) h.isProjOver
    exact (LineForm.TopInt.part_finite (h.atlas σ) (hθ σ) ε).measure_univ_lt_top.ne
  · refine finsum_congr fun σ => ?_
    rw [UnitsInt.univ, Finset.sum_pair (by decide)]
    simp only [CxForm.HolAtlas.integral, Measure.real, sub_eq_add_neg, Units.val_one, Units.val_neg, Int.cast_one,
      Int.cast_neg, one_mul, neg_mul, CxForm.HolAtlas.part]
    rfl

end GlobalTheory.TorsionForm
