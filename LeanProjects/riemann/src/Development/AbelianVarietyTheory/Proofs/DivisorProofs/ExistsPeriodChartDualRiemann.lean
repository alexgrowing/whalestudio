import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPeriodMapExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannDataLinearChartStatement

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat transl IsFactor IsMetric)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Real CategoryTheory.Obj
open GlobalTheory GlobalTheory.TorsionForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeriodChartExists

open GlobalTheory.TorsionForm

theorem exists_periodChart : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S)
    (h : VMetric p (omega P.A) P.g), P.IsDualRiemann (1 / 2) h → ∀ (σ : k →+* ℂ) (y : CxPts p σ),
    ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ)
      (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ),
      y ∈ c.e.source ∧ Convex ℝ c.e.target ∧ IsPeriodChart h c τ ex := by
  classical
  intro k _ S p hS P h hh σ y
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : AlgChart p σ 1, y ∈ c₀.e.source := by
    obtain ⟨R⟩ := (GlobalTheory.RegGenSmooth.genSmooth_of_isRegSurf k S p hS).1 σ
    obtain ⟨i, hi⟩ := R.cover y
    exact ⟨R.chart i, hi⟩
  obtain ⟨r, hr, hball, τ, ex', hτ, hex', hfib⟩ := GlobalTheory.T.local_period_map_exists S P c₀.e.target (fun v => (c₀.e.symm v).1)
    (c₀.e y) c₀.e.open_target (c₀.e.map_source hc₀) (GlobalTheory.TrueCx.TorHolo.isHolTo_symm c₀)
    (fun v _ => (hh σ _).1)
  set Bl := Metric.ball (c₀.e y) r with hBl
  have hS' : IsOpen (c₀.e.source ∩ c₀.e ⁻¹' Bl) := c₀.e.isOpen_inter_preimage Metric.isOpen_ball
  set c := c₀.restr _ hS' with hc
  have htgt : c.e.target = Bl := by
    ext v
    simp only [hc, AlgChart.restr, Set.mem_inter_iff,
      Set.mem_preimage]
    constructor
    · rintro ⟨hv, -, hv'⟩
      have hv'' := Set.mem_preimage.1 hv'
      rwa [c₀.e.right_inv hv] at hv''
    · intro hv
      exact ⟨hball hv, c₀.e.map_target (hball hv), Set.mem_preimage.2 (by rwa [c₀.e.right_inv (hball hv)])⟩
  have hov : ∀ P' : Pt (V 1) P.g, P'.1 ∈ Bl → ex' P' ≫ (P.A.hom ≫ p) = spMap σ := fun P' hP' => by
    rw [← Category.assoc, (hfib P'.1 hP').1 P'.2]
    exact (c₀.e.symm P'.1).2
  let ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ := fun P' =>
    if hP' : P'.1 ∈ Bl then ⟨ex' P', hov P' hP'⟩
    else ⟨ex' (c₀.e y, 0), hov _ (Metric.mem_ball_self hr)⟩
  have hexeq : ∀ v ∈ Bl, ∀ z, (ex (v, z)).1 = ex' (v, z) := fun v hv z => by
    simp only [ex, dif_pos hv]
  refine ⟨c, τ, ex, ?_, ?_, ?_⟩
  · simp only [hc, AlgChart.restr_source]
    exact ⟨hc₀, hc₀, Metric.mem_ball_self hr⟩
  · rw [htgt]; exact convex_ball _ _
  · unfold IsPeriodChart
    rw [htgt]
    refine ⟨hτ, ?_, fun v hv => ?_⟩
    · intro U f
      have e₁ : {b ∈ cov Bl P.g | ⊤ ≤ (ex b).1 ⁻¹ᵁ U} = {b ∈ cov Bl P.g | ⊤ ≤ ex' b ⁻¹ᵁ U} := by
        ext b
        simp only [Set.mem_setOf_eq]
        exact and_congr_right fun hb => by
          rw [show (ex b).1 = ex' b from hexeq b.1 hb.1 b.2]
      rw [e₁]
      exact ⟨(hex' U f).1, (hex' U f).2.congr fun b hb => by
        simp only [show (ex b).1 = ex' b from hexeq b.1 hb.1.1 b.2]⟩
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hfib v hv
    refine ⟨fun z => by rw [hexeq v hv]; exact h₁ z, fun z w x x' hx hx' => ?_, fun x => ?_,
      fun z => by rw [hexeq v hv]; exact h₄ z, fun U W hU f f' hs => ?_⟩
    · rw [hexeq v hv] at hx hx' ⊢
      exact h₂ z w x x' hx hx'
    · obtain ⟨z, hz⟩ := h₃ x
      exact ⟨z, hz.trans (hexeq v hv z).symm⟩
    · exact GlobalTheory.T.riemann_data_linear_chart k S p P h hh σ (c.e.symm v) (τ v) (fun z => ex (v, z)) (hτ.2.2 v hv).1
        (hτ.2.2 v hv).2 (fun d => by
          obtain ⟨F, hF₁, hF₂⟩ := h₅ d
          exact ⟨F, fun z => (hF₁ z).trans (hexeq v hv z).symm, hF₂⟩) U W hU f f' hs

end GlobalTheory.PeriodChartExists
