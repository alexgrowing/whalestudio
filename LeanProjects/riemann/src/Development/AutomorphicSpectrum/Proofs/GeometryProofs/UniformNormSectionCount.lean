import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompLawsModelRootBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginExistsFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginWeightSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOrbitBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscRatioGrowthStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscComponentGrowthStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem cusp_mem_chartLatNm : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw), ∀ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), ∃ N : ℕ, 0 < N ∧ (N : (T.M B b).Ω) * (gauge Rd u * Rd.φ (evC h Z f)) ∈ chartLatNm (T.M B b).y (degOf (T.M B b) u) 1 := by
  intro hG E _ _ _ H Dw l Xo c r U h e hL x hx Y _ T o B b Fr Z Rd u f hf
  obtain ⟨R, w, hw, hval⟩ := GlobalTheory.T.comp_laws_model_root_bound hG E H Dw l Xo c r U h e hL x hx _ _ Y _ _ _ _ _ Fr Z Rd u f hf
  obtain ⟨f₀, hf₀, hint⟩ := GlobalTheory.T.root_origin_exists_form E H Dw l Xo c _ _ Y _ _ _ _ (o.toTowerOrigin.Or B b)
  obtain ⟨hJ, inst, hsm⟩ := o.smooth B b
  refine GlobalTheory.T.holomorphic_disc_component_growth GlobalTheory.T.holomorphic_disc_ratio_growth _ _ _ (T.M B b).y (degOf (T.M B b) u) _
    (fun z => R * ∏ r, ((o.toTowerOrigin.Or B b).sing r).h z ^ nOf u (some r)) w f₀ (T.M B b).birational hsm hw hf₀
    hval ?_
  intro Zf hol hmem hne
  have hJ' : (o.toTowerOrigin.Or B b).Re.J = ⊤ := hJ
  obtain ⟨C₁, ρ₁, hρ₁, hb⟩ := GlobalTheory.T.holomorphic_disc_orbit_bound _ _ _ _ _ _ (o.toTowerOrigin.Or B b).Re hJ' Zf hol hmem
    (fun z hz hz0 x' hx' => hint _ (hmem z hz) (hne z hz hz0) x' hx')
  obtain ⟨C₂, M, hC₂, hev⟩ := GlobalTheory.T.root_origin_weight_section E H Dw l Xo c _ _ Y _ _ _ _ (o.toTowerOrigin.Or B b)
    (fun r => nOf u (some r)) (Zf 0) (hmem 0 (by simp))
  have hcont : ContinuousAt Zf 0 := by
    refine continuousAt_pi.2 fun p => ?_
    exact (hol p).continuousOn.continuousAt (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨ρ₂, hρ₂, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually hev)
  refine ⟨|R| * C₂ * C₁ ^ M, min ρ₁ (min ρ₂ 1), M, lt_min hρ₁ (lt_min hρ₂ one_pos), fun z hz0 hz => ?_⟩
  have hz₁ : ‖z‖ < ρ₁ := hz.trans_le (min_le_left _ _)
  have hz₂ : ‖z‖ < ρ₂ := hz.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hz₃ : ‖z‖ < 1 := hz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hzb : z ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz₃
  have hz00 : z ≠ 0 := norm_pos_iff.1 hz0
  have hnot : Zf z ∉ mcPts (o.toTowerOrigin.Or B b).Re.J := by
    rw [hJ']
    intro hm
    have := hm.2 1 trivial
    simp at this
  obtain ⟨x', hx'⟩ := (o.toTowerOrigin.Or B b).Re.R.surj (Zf z) (hmem z hzb) hnot
  have hop := hint _ (hmem z hzb) (hne z hzb hz00) x' hx'
  have h1 := hball (by simpa using hz₂) (hmem z hzb) x' hx' hop
  have h2 := hb z hz0 hz₁ x' hx'
  have h3 : 0 ≤ ReciprocityTheory.AnForm.P.rW ((o.toTowerOrigin.Sys b).L) ((o.toTowerOrigin.Sys b).s)
      ((o.toTowerOrigin.Or B b).Re.π x') := by
    have := (o.toTowerOrigin.Sys b).norm_le ((o.toTowerOrigin.Or B b).Re.π x')
    have he := Real.exp_pos 1
    unfold ReciprocityTheory.AnForm.P.rW
    linarith
  have hpos : 0 ≤ ∏ r, ((o.toTowerOrigin.Or B b).sing r).h (Zf z) ^ nOf u (some r) :=
    Finset.prod_nonneg fun r _ => (zpow_pos (((o.toTowerOrigin.Or B b).sing r).pos _ (hmem z hzb).1) _).le
  calc R * ∏ r, ((o.toTowerOrigin.Or B b).sing r).h (Zf z) ^ nOf u (some r)
      ≤ |R| * ∏ r, ((o.toTowerOrigin.Or B b).sing r).h (Zf z) ^ nOf u (some r) :=
        mul_le_mul_of_nonneg_right (le_abs_self R) hpos
    _ ≤ |R| * (C₂ * (C₁ * (1 + |Real.log ‖z‖|)) ^ M) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (abs_nonneg R)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 M) hC₂
    _ = |R| * C₂ * C₁ ^ M * (1 + |Real.log ‖z‖|) ^ M := by rw [mul_pow]; ring

end GlobalTheory.CompanionTheory.Ar.Plug
