import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DdcLogNormBoundedByKaehler

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory GlobalTheory.CxPts GlobalTheory.ShFam
open Filter Topology

namespace GlobalTheory.KaehlerCmp

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

theorem continuousAt_form {R : AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) (c : AlgChart p σ d)
    {z : V d} (hz : z ∈ c.e.target) (ξ : V d) :
    ContinuousAt (fun q : V d × V d => a c (c.e.symm q.1) q.2.ofLp) (z, ξ) := by
  obtain ⟨W, φ, hW, ho, hs, eφ⟩ := ha.1 (c.e.symm z)
  have hy : c.e.symm z ∈ c.e.source := c.e.map_target hz
  have h1 := CurvBound.continuousAt_ddcForm hy (hs.contDiffAt_two ho hy hW) ξ.ofLp
  have h2 : ContinuousAt (fun q : V d × V d => (c.e.symm q.1, q.2.ofLp)) (z, ξ) :=
    ((c.e.continuousAt_symm hz).comp (f := Prod.fst) continuousAt_fst).prodMk (by fun_prop)
  have h3 := h1.comp (x := (z, ξ)) h2
  refine h3.congr ?_
  have h4 : ∀ᶠ w in 𝓝 z, w ∈ c.e.target ∧ c.e.symm w ∈ W :=
    (show ∀ᶠ w in 𝓝 z, w ∈ c.e.target from c.e.open_target.mem_nhds hz).and
      (show ∀ᶠ w in 𝓝 z, c.e.symm w ∈ W from (c.e.continuousAt_symm hz).preimage_mem_nhds (ho.mem_nhds hW))
  have h5 : ∀ᶠ q : V d × V d in 𝓝 (z, ξ), q.1 ∈ c.e.target ∧ c.e.symm q.1 ∈ W :=
    (continuous_fst.tendsto (z, ξ)).eventually h4
  filter_upwards [h5] with q hq
  exact (eφ _ _ (c.e.map_target hq.1) hq.2 _).symm

theorem exists_bounds : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    {R : AnRead p σ d} {a : ChartForm p σ d}, IsKaehlerForm R a → ∀ (c : AlgChart p σ d) {Kc : Set (V d)},
    IsCompact Kc → Kc ⊆ c.e.target → ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ y ∈ c.e.source, c.e y ∈ Kc → ∀ v : V d,
      m * ‖v‖ ^ 2 ≤ a c y v.ofLp ∧ a c y v.ofLp ≤ M * ‖v‖ ^ 2 := by
  intro k _ Y p σ d R a ha c Kc hK hKt
  have hS : IsCompact (Kc ×ˢ Metric.sphere (0 : V d) 1) := hK.prod (isCompact_sphere _ _)
  have hc : ContinuousOn (fun q : V d × V d => a c (c.e.symm q.1) q.2.ofLp) (Kc ×ˢ Metric.sphere (0 : V d) 1) :=
    fun q hq => (continuousAt_form ha c (hKt hq.1) q.2).continuousWithinAt
  obtain ⟨m, hm, hmle⟩ := hS.exists_forall_le' hc (a := 0) fun q hq => by
    have h0 : q.2 ≠ 0 := fun h => by have := hq.2; simp [h] at this
    have h0' : q.2.ofLp ≠ 0 := fun h => h0 (by simpa using congrArg (WithLp.toLp 2) h)
    exact ha.2 c _ (c.e.map_target (hKt hq.1)) _ h0'
  obtain ⟨B, hB⟩ := hS.bddAbove_image hc
  refine ⟨m, max B 1, hm, lt_max_of_lt_right one_pos, fun y hy hyK v => ?_⟩
  have hsm := (ChernReg.continuous_and_smul ha hy).2
  rcases eq_or_ne v 0 with rfl | hv
  · have h := hsm 0 0
    simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h
    simp [h]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V d) 1 := by simp [norm_smul, hn]
    have e : v.ofLp = ‖v‖ • (‖v‖⁻¹ • v).ofLp := by
      rw [WithLp.ofLp_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have hq : (c.e y, ‖v‖⁻¹ • v) ∈ Kc ×ˢ Metric.sphere (0 : V d) 1 := ⟨hyK, hw⟩
    have h1 := hmle _ hq
    have h2 : a c (c.e.symm (c.e y)) (‖v‖⁻¹ • v).ofLp ≤ B := hB ⟨_, hq, rfl⟩
    rw [c.e.left_inv hy] at h1 h2
    rw [e, hsm]
    have h3 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    constructor
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left h1 h3
    · rw [mul_comm (max B 1)]
      exact mul_le_mul_of_nonneg_left (h2.trans (le_max_left _ _)) h3

end GlobalTheory.KaehlerCmp
