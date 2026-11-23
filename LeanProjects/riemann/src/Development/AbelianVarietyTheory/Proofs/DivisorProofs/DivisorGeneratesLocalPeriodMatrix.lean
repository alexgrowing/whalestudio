import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticEquationLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericUnitEquationChartStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open Filter Topology
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Mean4O GlobalTheory.Mean4 ReciprocityTheory.AnForm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeLocGeo

theorem lnN_root_local : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ h => ∀ (c : O.Y.Comp) (a : Fin ((T.M c).n + 1)) (j : Fin ((T.M c).A a).n),
  ∀ y ∈ (((T.M c).A a).chart j).target, (((T.M c).A a).chart j).symm y ∉ (T.M c).Z a →
  ∀ f : DV.Rt D.what₂.Tau O.N → (O.var c).Fn,
    (∀ x, (GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under ((h.man c).pt a ((((T.M c).A a).chart j).symm y))) (f x)) →
  ∃ (Zm : D.what₂.Tau → (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin O.j) (Fin (O.N - O.j)) ℂ)
    (GW : D.what₂.Tau → (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin O.j) (Fin O.j) ℂ)
    (GΩ : D.what₂.Tau → (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin (O.N - O.j)) (Fin (O.N - O.j)) ℂ)
    (cW cΩ : D.what₂.Tau → ℝ) (g : DV.Rt D.what₂.Tau O.N → (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → ℂ),
    (∀ τ, 0 < cW τ) ∧ (∀ τ, 0 < cΩ τ) ∧ (∀ x, g x y ≠ 0) ∧
    ∀ᶠ v in 𝓝 y, (∀ τ a b, AnalyticAt ℂ (fun w => Zm τ w a b) v) ∧ (∀ τ a b, AnalyticAt ℂ (fun w => GW τ w a b) v) ∧
      (∀ τ a b, AnalyticAt ℂ (fun w => GΩ τ w a b) v) ∧ (∀ x, AnalyticAt ℂ (g x) v) ∧
      (∀ τ, (1 - (Zm τ v)ᴴ * Zm τ v).PosDef) ∧ (∀ τ, IsUnit (GW τ v).det) ∧ (∀ τ, IsUnit (GΩ τ v).det) ∧
      ∀ x, GlobalTheory.Mean4O.lnN (O.met.hm c none ((h.man c).ε a) (O.ex x)) (f x) ((h.man c).pt a ((((T.M c).A a).chart j).symm v)) =
        Real.log ‖g x v‖ + Real.log (rootNorm O.N O.j (cW x.1) (cΩ x.1) (GW x.1 v) (GΩ x.1 v) (Zm x.1 v) x.2) / 2 := by
  intro _ _ D O hC _ _ T _ h c a j y hy hZ f hf
  obtain ⟨x, P, hw⟩ := hC
  obtain ⟨c', hc'⟩ := (h.man c).alg a j
  have hsymm : ∀ v, (h.man c).pt a ((((T.M c).A a).chart j).symm v) = c'.finChart.symm v := by
    intro v
    rw [hc', Homeomorph.transOpenPartialHomeomorph_symm_apply]
    simp
  have hyt : y ∈ c'.finChart.target := by
    rw [hc'] at hy
    simpa using hy
  have hp0 : c'.finChart.symm y ∈ c'.finChart.source := c'.finChart.map_target hyt
  have hp0y : c'.finChart (c'.finChart.symm y) = y := c'.finChart.right_inv hyt
  have hbd : (O.Φ.C c).π (under (c'.finChart.symm y)) ∉ genBd O.s.T.Z := by
    have h1 := ((h.an c).Z a ((((T.M c).A a).chart j).symm y)).not.1 hZ
    rwa [hsymm] at h1
  obtain ⟨t, U, Zm, GW, GΩ, cW, cΩ, hU, ht, hcW, hcΩ, hev⟩ :=
    GlobalTheory.T.generic_unit_equation_chart D O.A O.N O.j O.S O.κ O.s x O.Φ c ((h.man c).ε a) _ c' _ hp0 hbd
  have hgen : ∀ x', (divOf (O.Φ.C c) (O.ex x')).GeneratesAt (under (c'.finChart.symm y)) (f x') := by
    intro x'
    have h1 := hf x'
    rwa [hsymm] at h1
  have hE : ∀ x', ∀ y' ∈ U, (divOf (O.Φ.C c) (O.ex x')).IsEqn y' (prodPow t (O.ex x')) := by
    intro x' y' hy'
    have key : ∀ s : Finset (Letter O.S.Dw), (∑ z ∈ s, O.ex x' z • (O.Φ.C c).gr z.1 z.2).IsEqn y'
        (∏ z ∈ s, t z.1 z.2 ^ O.ex x' z) := fun s => by
      classical
      induction s using Finset.induction_on with
      | empty => simpa using CartierDiv.isEqn_zero y'
      | insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((ht y' hy' _ _).zsmul _).add ih
    exact key Finset.univ
  choose g hg0 hgev using fun x' =>
    GlobalTheory.T.analytic_equation_locus (O.var c) ((h.man c).ε a) c' _ hp0 _ _ U hU (hE x') (f x') (hgen x')
  rw [hp0y] at hg0 hgev hev
  have hne : ∀ x', ∀ᶠ v in 𝓝 y, g x' v ≠ 0 := fun x' =>
    (hgev x').self_of_nhds.1.continuousAt.eventually_ne (hg0 x')
  refine ⟨Zm, GW, GΩ, cW, cΩ, g, hcW, hcΩ, hg0, ?_⟩
  filter_upwards [hev, Filter.eventually_all.2 hgev, Filter.eventually_all.2 hne] with v hv hgv hnv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hv
  refine ⟨h1, h2, h3, fun x' => (hgv x').1, h4, h5, h6, fun x' => ?_⟩
  obtain ⟨-, heq, hpn⟩ := hgv x'
  have hm : O.met.hm = metsOf x O.Φ := hw.hm_eq
  have hR := h7 x'
  have hpos : 0 < (metsOf x O.Φ c none ((h.man c).ε a) (O.ex x')).h (prodPow t (O.ex x')) (c'.finChart.symm v) :=
    (Var.Met.mem_posSet_iff heq).1 (Set.eq_univ_iff_forall.1 (posSet_metsOf x O.Φ c none _ _) _)
  rw [hsymm, lnN, hpn, hm, hR]
  rw [hR] at hpos
  have hg : ‖g x' v‖ ≠ 0 := norm_ne_zero_iff.2 (hnv x')
  rw [Real.log_mul (pow_ne_zero 2 hg) hpos.ne', Real.log_pow]
  push_cast
  ring

end GlobalTheory.HodgeLocGeo
