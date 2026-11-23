import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenClosureSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMatrixSmoothInvertible
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.ExphOn

open Set

theorem exists_mul_norm_sq_le {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    {R : AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) (c : AlgChart p σ d)
    {L : Set (CxPts p σ)} (hL : IsCompact L) (hLs : L ⊆ c.e.source) :
    ∃ m > 0, ∀ y ∈ L, ∀ η : ReciprocityTheory.L2DbarEstimates.V d, m * ‖η‖ ^ 2 ≤ a c y η.ofLp := by
  obtain ⟨hM, -, hform⟩ := GlobalTheory.ChernReg.MatSmooth.matIn_smooth_unit_form k Y p σ d R a ha c
  have hG : ContinuousOn (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => a c (c.e.symm q.1) q.2.ofLp)
      (c.e.target ×ˢ univ) := by
    have hij : ∀ i j, ContinuousOn (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => matIn a c q.1 i j)
        (c.e.target ×ˢ univ) :=
      fun i j => (hM i j).continuousOn.comp continuous_fst.continuousOn fun q hq => hq.1
    have h1 : ContinuousOn (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d =>
        ((q.2.ofLp ᵥ* matIn a c q.1) ⬝ᵥ star q.2.ofLp).re) (c.e.target ×ˢ univ) := by
      simp only [dotProduct, vecMul, Pi.star_apply]
      fun_prop
    refine h1.congr fun q hq => ?_
    have := hform q.1 hq.1 q.2
    simp only
    rw [← this, Complex.ofReal_re]
  have hK : IsCompact ((c.e '' L) ×ˢ Metric.sphere (0 : ReciprocityTheory.L2DbarEstimates.V d) 1) :=
    (hL.image_of_continuousOn (c.e.continuousOn.mono hLs)).prod (isCompact_sphere 0 1)
  have hsub : (c.e '' L) ×ˢ Metric.sphere (0 : ReciprocityTheory.L2DbarEstimates.V d) 1 ⊆ c.e.target ×ˢ univ := by
    rintro ⟨v, ξ⟩ ⟨⟨y, hy, rfl⟩, -⟩
    exact ⟨c.e.map_source (hLs hy), trivial⟩
  have hpos : ∀ q ∈ (c.e '' L) ×ˢ Metric.sphere (0 : ReciprocityTheory.L2DbarEstimates.V d) 1, 0 < a c (c.e.symm q.1) q.2.ofLp := by
    rintro ⟨v, ξ⟩ ⟨⟨y, hy, rfl⟩, hξ⟩
    simp only
    rw [c.e.left_inv (hLs hy)]
    refine ha.2 c y (hLs hy) _ fun h => ?_
    rw [mem_sphere_zero_iff_norm] at hξ
    have : ξ = 0 := by simpa using h
    simp [this] at hξ
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' (hG.mono hsub) hpos
  refine ⟨m, hm, fun y hy η => ?_⟩
  obtain ⟨-, hs⟩ := continuous_and_smul ha (hLs hy)
  rcases eq_or_ne η 0 with rfl | hη
  · have h0 : a c y 0 = 0 := by simpa using hs 0 0
    simp [h0]
  · have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
    have hu := hmK (c.e y, ‖η‖⁻¹ • η) ⟨mem_image_of_mem _ hy, by simp [norm_smul, hn.ne']⟩
    simp only [c.e.left_inv (hLs hy)] at hu
    have e : η.ofLp = ‖η‖ • (‖η‖⁻¹ • η).ofLp := by
      rw [WithLp.ofLp_smul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [e, hs, mul_comm]
    exact mul_le_mul_of_nonneg_left hu (by positivity)

theorem short_vectors_near_base : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) (a : ChartForm p σ d), IsKaehlerForm R a → ∀ (E : ChartMap p σ d) (W : Set (CxPts p σ)) (ε : ℝ), 0 < ε → ExphOn.IsExphOn a E W ε → ∀ (c : AlgChart p σ d) (L : Set (CxPts p σ)) (r : ℝ), IsCompact L → L ⊆ W → L ⊆ c.e.source → 0 < r → ∃ δ > 0, ∀ c₀ : AlgChart p σ d, ∀ y ∈ L, y ∈ c₀.e.source → ∀ ξ, a c₀ y ξ < δ → E c₀ y ξ ∈ c.e.source ∧ c.e (E c₀ y ξ) ∈ Metric.ball (c.e y) r := by
  intro k _ Y p σ d R a ha E W ε hε hE c L r hL hLW hLs hr
  obtain ⟨m, hm, hmL⟩ := exists_mul_norm_sq_le ha c hL hLs
  have hP : ∀ v ∈ c.e '' L, ∀ᶠ z : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d in 𝓝 ((0 : ReciprocityTheory.L2DbarEstimates.V d), v),
      E c (c.e.symm z.2) z.1.ofLp ∈ c.e.source ∧ dist (c.e (E c (c.e.symm z.2) z.1.ofLp)) z.2 < r := by
    rintro v ⟨y, hy, rfl⟩
    have hyc := hLs hy
    have hs := (continuous_and_smul ha hyc).2
    have h0 : a c y 0 = 0 := by simpa using hs 0 0
    have hF := hE.cont c (c.e y) (c.e.map_source hyc) (by rw [c.e.left_inv hyc]; exact hLW hy) 0
      (by rw [c.e.left_inv hyc]; simpa [h0] using hε)
    have hF' : ContinuousAt (fun z : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => E c (c.e.symm z.2) z.1.ofLp)
        (0, c.e y) := ContinuousAt.comp (f := Prod.swap) (x := ((0 : ReciprocityTheory.L2DbarEstimates.V d), c.e y)) hF continuous_swap.continuousAt
    have hval : E c (c.e.symm (c.e y)) (0 : ReciprocityTheory.L2DbarEstimates.V d).ofLp = y := by
      rw [c.e.left_inv hyc, WithLp.ofLp_zero]
      exact hE.zero c y hyc (hLW hy)
    have h1 : ∀ᶠ z : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d in 𝓝 ((0 : ReciprocityTheory.L2DbarEstimates.V d), c.e y),
        E c (c.e.symm z.2) z.1.ofLp ∈ c.e.source :=
      hF'.preimage_mem_nhds (by rw [hval]; exact c.e.open_source.mem_nhds hyc)
    have hce : ContinuousAt c.e (E c (c.e.symm (c.e y)) (0 : ReciprocityTheory.L2DbarEstimates.V d).ofLp) := by
      rw [hval]
      exact c.e.continuousAt hyc
    have hd := (ContinuousAt.comp (x := ((0 : ReciprocityTheory.L2DbarEstimates.V d), c.e y))
      (f := fun z : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => E c (c.e.symm z.2) z.1.ofLp) hce hF').dist continuousAt_snd
    have h2 := hd.eventually_lt continuousAt_const (show _ < r by
      simp only [Function.comp_apply]
      rw [hval, dist_self]
      exact hr)
    exact h1.and h2
  obtain ⟨s, hs0, hsball⟩ := Metric.eventually_nhds_iff.1
    ((hL.image_of_continuousOn (c.e.continuousOn.mono hLs)).eventually_forall_of_forall_eventually
      (P := fun (η : ReciprocityTheory.L2DbarEstimates.V d) v =>
        E c (c.e.symm v) η.ofLp ∈ c.e.source ∧ dist (c.e (E c (c.e.symm v) η.ofLp)) v < r) hP)
  refine ⟨m * s ^ 2, by positivity, fun c₀ y hy hy₀ ξ hξ => ?_⟩
  have hyc := hLs hy
  have ha' : a c₀ y ξ = a c y (c₀.dtrans c y ξ) := ha.trans hy₀ hyc ξ
  have h1 := hmL y hy (WithLp.toLp 2 (c₀.dtrans c y ξ))
  simp only [WithLp.ofLp_toLp] at h1
  have hns : ‖(WithLp.toLp 2 (c₀.dtrans c y ξ) : ReciprocityTheory.L2DbarEstimates.V d)‖ < s := by
    have h2 : m * ‖(WithLp.toLp 2 (c₀.dtrans c y ξ) : ReciprocityTheory.L2DbarEstimates.V d)‖ ^ 2 < m * s ^ 2 := by linarith
    exact lt_of_pow_lt_pow_left₀ 2 hs0.le (lt_of_mul_lt_mul_left h2 hm.le)
  have hP' := hsball (y := WithLp.toLp 2 (c₀.dtrans c y ξ)) (by rw [dist_zero_right]; exact hns) (c.e y)
    (mem_image_of_mem _ hy)
  simp only [WithLp.ofLp_toLp, c.e.left_inv hyc] at hP'
  rw [hE.trans c₀ c y hy₀ hyc ξ]
  exact ⟨hP'.1, hP'.2⟩

end GlobalTheory.ChernReg.ExphOn
