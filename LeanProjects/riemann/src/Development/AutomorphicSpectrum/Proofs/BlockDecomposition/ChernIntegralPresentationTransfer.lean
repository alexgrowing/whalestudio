import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory GlobalTheory.Points GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.ChartGlue GlobalTheory.ProjVar.Var

namespace GlobalTheory.CompanionTheory.ChernTransport

section Chart

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {B B' : LB X} {φ : Weight p σ B} {ψ : Weight p σ B'}

theorem hess_eq_of_unit (c : AlgChart p σ D) (h : φ.IsCInf) {y : CxPts p σ} (hy : y ∈ c.e.source)
    {i : B.ι} {j : B'.ι} (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B'.U j))
    (a : Γ(X, B.U i ⊓ B'.U j)ˣ)
    (ha : ∀ z ∈ ptsIn p σ (B.U i ⊓ B'.U j),
      ψ.φ j z = φ.φ i z + Real.log (‖ev p σ _ a.val z‖ ^ 2)) :
    c.hess ψ j y = c.hess φ i y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i ⊓ B'.U j))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨hi, hj⟩)
  have hg := c.holo _ a.val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ B'.U j),
      (ev p σ _ a.val ∘ c.e.symm) v ≠ 0 := fun v hv => ev_ne_zero hv.2 a.isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h i) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun w => ((Real.log (‖(ev p σ _ a.val ∘ c.e.symm) w‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext s t
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 s t
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [ha _ hv.2, one_mul]
  rfl

theorem chartMeas_congr_source {n : ℕ} {T : Type} [TopologicalSpace T] [MeasurableSpace T]
    (e : OpenPartialHomeomorph T (V n)) {ρ ρ' : T → ENNReal} (h : ∀ y ∈ e.source, ρ y = ρ' y) :
    chartMeas e ρ = chartMeas e ρ' := by
  have hae : (ρ ∘ e.symm) =ᵐ[volume.restrict e.target] (ρ' ∘ e.symm) :=
    (ae_restrict_iff' e.open_target.measurableSet).2
      (Filter.Eventually.of_forall fun v hv => h _ (e.map_target hv))
  show Measure.map e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm)) =
    Measure.map e.symm ((volume.restrict e.target).withDensity (ρ' ∘ e.symm))
  rw [withDensity_congr_ae hae]

theorem chernPart_eq_of_chernDens (h : ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source,
    c.chernDens ψ y = c.chernDens φ y) (ε : ℤˣ) : ψ.chernPart D ε = φ.chernPart D ε := by
  show (⨆ c : AlgChart p σ D, chartMeas c.e fun y => ENNReal.ofReal (↑↑ε * c.chernDens ψ y)) =
    ⨆ c : AlgChart p σ D, chartMeas c.e fun y => ENNReal.ofReal (↑↑ε * c.chernDens φ y)
  exact iSup_congr fun c => chartMeas_congr_source _ fun y hy => by rw [h c y hy]

end Chart

variable {Y : Var ℂ} {Δ : Y.Dv} {L L' : LB Y.X} {r : L.ι → Y.Fnˣ} {r' : L'.ι → Y.Fnˣ}

theorem exists_unit_tv (hp : Presents Δ L r) (hp' : Presents Δ L' r') (i : L.ι) (j : L'.ι) :
    ∃ a : Γ(Y.X, L.U i ⊓ L'.U j)ˣ, ∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
      tv (σ := RingHom.id ℂ) (r i) (r' j) z = ev Y.str (RingHom.id ℂ) _ a.val z := by
  obtain ⟨a, ha⟩ := exists_unit_fnOf_eq (U := L.U i ⊓ L'.U j)
    (f := (r' j : Y.Fn) / (r i : Y.Fn))
    fun x hx => (hp.isEqn i x hx.1).iff_unitAt.1 (hp'.isEqn j x hx.2)
  refine ⟨a, fun z hz => ?_⟩
  have hb := mem_ptsIn_iff.1 hz
  rw [tv, ← ha (gen_mem hb), val_cx_fnOf hb]

theorem exists_transport (hp : Presents Δ L r) (hp' : Presents Δ L' r')
    (φ : Weight Y.str (RingHom.id ℂ) L) (hφ : φ.IsCInf) :
    ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧
      ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  have hs : mSmooth Y (RingHom.id ℂ) Δ (ofWeight Y (RingHom.id ℂ) Δ L r hp φ) :=
    (mSmooth_ofWeight_iff hp φ).2 ((Weight.isCInf_iff_isSmooth (Y.an _)).1 hφ)
  set m := ofWeight Y (RingHom.id ℂ) Δ L r hp φ with hm
  let ψ : Weight Y.str (RingHom.id ℂ) L' := m.toWeight hs.posSet_eq hp'
  have hψ : ψ.IsCInf := (Weight.isCInf_iff_isSmooth (Y.an _)).2 (hs.isSmooth_toWeight hp')
  have key : ∀ (i : L.ι) (j : L'.ι) (a : Γ(Y.X, L.U i ⊓ L'.U j)ˣ),
      (∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
        tv (σ := RingHom.id ℂ) (r i) (r' j) z = ev Y.str (RingHom.id ℂ) _ a.val z) →
      ∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
        ψ.φ j z = φ.φ i z + Real.log (‖ev Y.str (RingHom.id ℂ) _ a.val z‖ ^ 2) := by
    intro i j a ha z hz
    obtain ⟨hi, hj⟩ := mem_ptsIn_inf.1 hz
    have hw : m.wt (r i) z = φ.φ i z := by
      rw [Met.wt, hm, ofWeight_h hp φ hi, Real.log_exp, neg_neg]
    have := Met.wt_trans (hs.posSet_eq ▸ mem_univ z) (ptsIn_subset_eqnSet hp i hi)
      (ptsIn_subset_eqnSet hp' j hj)
    rw [hw, ha z hz] at this
    exact this
  have hd : ∀ (c : AlgChart Y.str (RingHom.id ℂ) Y.dim), ∀ y ∈ c.e.source,
      c.chernDens ψ y = c.chernDens φ y := by
    intro c y hy
    have hi := mem_pick φ.isLB y
    have hj := mem_pick ψ.isLB y
    obtain ⟨a, ha⟩ := exists_unit_tv hp hp' _ _
    rw [c.chernDens_eq hψ hy hj, c.chernDens_eq hφ hy hi,
      hess_eq_of_unit c hφ hy hi hj a (key _ _ a ha)]
  refine ⟨ψ, hψ, ?_⟩
  rw [Weight.chernInt, Weight.chernInt, chernPart_eq_of_chernDens hd, chernPart_eq_of_chernDens hd]

theorem transport : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ) (r' : L'.ι → Y.Fnˣ),
    Presents Δ L r → Presents Δ L' r' → ∀ φ : Weight Y.str (RingHom.id ℂ) L, φ.IsCInf →
      ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧
        ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  intro Y Δ L L' r r' hp hp' φ hφ
  exact exists_transport hp hp' φ hφ

end GlobalTheory.CompanionTheory.ChernTransport
