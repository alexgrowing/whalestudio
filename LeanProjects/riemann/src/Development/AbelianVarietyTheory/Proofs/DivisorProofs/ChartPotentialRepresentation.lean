import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentProjectionSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentsLocalSncStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSncPullbackSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorNormPullbackComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorPotentialIsSNCBoundary
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallBd
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology
open CategoryTheory Limits IsDedekindDomain TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems Formalism.L2.Pj Formalism.L2.Geo GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop

theorem sum_match_eq_sum_filter {m d : ℕ} (τ : Fin m → Option (Fin d))
    (hinj : ∀ k k' i, τ k = some i → τ k' = some i → k = k') (g : Fin d → ℝ) :
    ∑ k, (match τ k with
      | some i => g i
      | none => 0) = ∑ i ∈ Finset.univ.filter (fun i => ∃ k, τ k = some i), g i := by
  classical
  rw [Finset.sum_filter]
  have e1 : ∀ i : Fin d, (if ∃ k, τ k = some i then g i else 0) = ∑ k, (if τ k = some i then g i else 0) := by
    intro i
    by_cases h : ∃ k, τ k = some i
    · obtain ⟨k, hk⟩ := h
      rw [if_pos ⟨k, hk⟩, Finset.sum_eq_single k (fun k' _ hk' => if_neg fun h' => hk' (hinj k' k i h' hk))
        (fun h0 => absurd (Finset.mem_univ k) h0), if_pos hk]
    · rw [if_neg h]
      exact (Finset.sum_eq_zero fun k _ => if_neg fun h' => h ⟨k, h'⟩).symm
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases h : τ k with
  | none => simp
  | some i0 => simp

theorem log_norm_prod_match {m d : ℕ} (τ : Fin m → Option (Fin d))
    (hinj : ∀ k k' i, τ k = some i → τ k' = some i → k = k') (w : Fin d → ℂ)
    (hw : ∀ i, (∃ k, τ k = some i) → w i ≠ 0) :
    Real.log (‖∏ k, (match τ k with
      | some i => w i ^ (1 : ℕ)
      | none => 1)‖ ^ 2) = ∑ i ∈ Finset.univ.filter (fun i => ∃ k, τ k = some i), Real.log (‖w i‖ ^ 2) := by
  have hne : ∀ k, ‖(match τ k with
      | some i => w i ^ (1 : ℕ)
      | none => (1 : ℂ))‖ ^ 2 ≠ 0 := by
    intro k
    cases h : τ k with
    | none => simp
    | some i => simpa using hw i ⟨k, h⟩
  rw [norm_prod, ← Finset.prod_pow, Real.log_prod (fun k _ => hne k), ← sum_match_eq_sum_filter τ hinj]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases h : τ k with
  | none => simp
  | some i => simp

theorem log_norm_prod_of {m d : ℕ} (τ : Fin m → Option (Fin d))
    (hinj : ∀ k k' i, τ k = some i → τ k' = some i → k = k') (w : Fin d → ℂ)
    (hw : ∀ i, (∃ k, τ k = some i) → w i ≠ 0) (g : Fin m → ℂ) (hs : ∀ k i, τ k = some i → g k = w i)
    (h1 : ∀ k, τ k = none → g k = 1) :
    Real.log (‖∏ k, g k‖ ^ 2) = ∑ i ∈ Finset.univ.filter (fun i => ∃ k, τ k = some i), Real.log (‖w i‖ ^ 2) := by
  have e : ∀ k, g k = (match τ k with
      | some i => w i ^ (1 : ℕ)
      | none => 1) := by
    intro k
    cases h : τ k with
    | none => simpa using h1 k h
    | some i => simpa using hs k i h
  rw [Finset.prod_congr rfl fun k _ => e k]
  exact log_norm_prod_match τ hinj w hw

theorem prod_ne_zero_of {m d : ℕ} (τ : Fin m → Option (Fin d)) (w : Fin d → ℂ)
    (hw : ∀ i, (∃ k, τ k = some i) → w i ≠ 0) (g : Fin m → ℂ) (hs : ∀ k i, τ k = some i → g k = w i)
    (h1 : ∀ k, τ k = none → g k = 1) : ‖∏ k, g k‖ ^ 2 ≠ 0 := by
  refine pow_ne_zero 2 (norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => ?_))
  cases h : τ k with
  | none => rw [h1 k h]; exact one_ne_zero
  | some i => rw [hs k i h]; exact hw i ⟨k, h⟩

end GlobalTheory.CovTop

theorem GlobalTheory.CovTop.r_eq_sub_log_chart : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (D : D7) (O : Setup D) (x : GlobalTheory.ShFam.ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P → 2 < D.R.f * (O.N - 1) → (∃ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), Nonempty (O.Reads A T H)) → ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (y₀ : GlobalTheory.TrueGeo.Pts (O.var c) σ), ∃ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (ReciprocityTheory.L2DbarEstimates.V (O.var c).dim)) (Φ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim → (Fin (O.var c).dim → ℂ)) (H : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim → ℝ) (I : Finset (Fin (O.var c).dim)), y₀ ∈ ch.e.source ∧ IsOpen U ∧ ch.e y₀ ∈ U ∧ U ⊆ ch.e.target ∧ ContDiffOn ℝ 1 Φ U ∧ Function.Bijective (fderiv ℝ Φ (ch.e y₀)) ∧ ContinuousOn H U ∧ ∀ v ∈ U, (∀ i ∈ I, Φ v i ≠ 0) → O.met.r c σ (ch.e.symm v) = H v - ∑ i ∈ I, Real.log (‖Φ v i‖ ^ 2) := by
  intro _ _ D O x P hC _ _ c σ y₀
  classical
  have hπ := GlobalTheory.T.flag_component_projection_smooth D _ _ _ _ _ O.s O.Φ c
  have : Smooth (genStr O.s.T.Z) := SmoothOfRelativeDimension.smooth O.S.Dw.dim _
  have : IsLocallyNoetherian (gen O.s.T.Z : Scheme.{0}) := LocallyOfFiniteType.isLocallyNoetherian (genStr O.s.T.Z)
  have := isProper_genStr O.s.T.Z
  have : CompactSpace (gen O.s.T.Z : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace (genStr O.s.T.Z)
  have : IsNoetherian (gen O.s.T.Z : Scheme.{0}) := {}
  let C : Fin x.m → Closeds (O.var c).X := fun i => (x.cpt i).preimage (O.Φ.C c).π.continuous
  let n : Fin x.m → Pts (O.var c) σ → ℝ := fun i z => x.nrm _ i ((O.Φ.C c).down z)
  have hn : ∀ i, IsDivNorm ((O.var c).an σ) (C i) (n i) := fun i =>
    GlobalTheory.DivPullback.isDivNorm_flag D _ _ _ _ _ O.s O.Φ c σ _ _ hπ (x.nrm_div _ i)
  have hsnc : ∀ y : (O.var c).X, LSncAt (O.var c).X C y := fun y =>
    GlobalTheory.T.local_snc_pullback_smooth _ _ _ (genStr O.s.T.Z) _ _ _ y (GlobalTheory.T.snc_components_local_snc _ _ _ _ O.s.T.snc x.cpt_list _)
  obtain ⟨ψ, hc, hx, hsub, τ, hinj, -, u, hu, hu0, he⟩ :=
    GlobalTheory.DivSec.isSNC_divSec _ (O.var c) σ x.m C n hn (atlasOf (O.var c) σ) (isAlgAtlas_atlasOf (Y := O.var c) σ) hsnc y₀
  obtain ⟨j, hj⟩ := (atlasOf (O.var c) σ).cover y₀
  obtain ⟨ch, hch⟩ := isAlgAtlas_atlasOf (Y := O.var c) σ j
  obtain ⟨h1, h2⟩ := hc j
  rw [hch] at h1 h2 hj
  have hj' : y₀ ∈ ch.e.source := hj
  let E := EuclideanSpace.equiv (Fin (O.var c).dim) ℂ
  have hEv : ∀ v, FinChart.toV _ (E v) = v := fun v => rfl
  have hEy : ∀ y, ch.e y = E.symm (ch.finChart y) := fun y => rfl
  let U : Set (ReciprocityTheory.L2DbarEstimates.V (O.var c).dim) := ch.e.target ∩ ch.e.symm ⁻¹' ψ.source
  let Φ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim → (Fin (O.var c).dim → ℂ) := fun v => ψ (ch.e.symm v)
  let I : Finset (Fin (O.var c).dim) := Finset.univ.filter (fun i => ∃ k, τ k = some i)
  let H : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim → ℝ := fun v => Real.exp 1 - Real.log (‖u (ch.e.symm v)‖ ^ 2) +
    2 * (GlobalTheory.DivSec.divPot hn).φ y₀ (ch.e.symm v)
  have hU : IsOpen U := ch.e.isOpen_inter_preimage_symm ψ.open_source
  have ha : ch.e y₀ ∈ U := ⟨ch.e.map_source hj', by simp only [Set.mem_preimage, ch.e.left_inv hj']; exact hx⟩
  have hΦE : Φ = (ψ ∘ ch.finChart.symm) ∘ E := funext fun v => by
    simp only [Φ, Function.comp_apply, AlgChart.finChart_symm_apply, hEv]
  have hΦan : AnalyticOnNhd ℂ Φ U := by
    intro v hv
    rw [hΦE]
    refine AnalyticAt.comp (h1 (E v) ⟨hv.1, ?_⟩) (E.analyticAt v)
    simpa [AlgChart.finChart_symm_apply, hEv] using hv.2
  have hΦy : Φ (ch.e y₀) = ψ y₀ := by simp only [Φ, ch.e.left_inv hj']
  let Ψ : (Fin (O.var c).dim → ℂ) → ReciprocityTheory.L2DbarEstimates.V (O.var c).dim := fun w => ch.e (ψ.symm w)
  have hΨE : Ψ = E.symm ∘ (ch.finChart ∘ ψ.symm) := funext fun w => hEy _
  have hΨan : AnalyticAt ℂ Ψ (ψ y₀) := by
    rw [hΨE]
    refine AnalyticAt.comp (E.symm.analyticAt _) (h2 (ψ y₀) ⟨ψ.map_source hx, ?_⟩)
    simp only [Set.mem_preimage, ψ.left_inv hx]
    exact hj
  have hΨy : Ψ (ψ y₀) = ch.e y₀ := by simp only [Ψ, ψ.left_inv hx]
  have hΦd := (hΦan _ ha).differentiableAt.hasFDerivAt
  have hΨd := hΨan.differentiableAt.hasFDerivAt
  have hL : (fderiv ℂ Ψ (ψ y₀)).comp (fderiv ℂ Φ (ch.e y₀)) = ContinuousLinearMap.id ℂ _ := by
    have e : Ψ ∘ Φ =ᶠ[nhds (ch.e y₀)] id := Filter.eventually_of_mem (hU.mem_nhds ha) fun v hv => by
      simp only [Function.comp_apply, Ψ, Φ, ψ.left_inv hv.2, ch.e.right_inv hv.1, id]
    have hc' : HasFDerivAt (Ψ ∘ Φ) ((fderiv ℂ Ψ (ψ y₀)).comp (fderiv ℂ Φ (ch.e y₀))) (ch.e y₀) :=
      HasFDerivAt.comp (ch.e y₀) (hΦy ▸ hΨd) hΦd
    exact (hc'.congr_of_eventuallyEq e.symm).unique (hasFDerivAt_id _)
  have hR : (fderiv ℂ Φ (ch.e y₀)).comp (fderiv ℂ Ψ (ψ y₀)) = ContinuousLinearMap.id ℂ _ := by
    have hV : IsOpen (ψ.target ∩ ψ.symm ⁻¹' ch.e.source) := ψ.isOpen_inter_preimage_symm ch.e.open_source
    have hm : ψ y₀ ∈ ψ.target ∩ ψ.symm ⁻¹' ch.e.source :=
      ⟨ψ.map_source hx, by simp only [Set.mem_preimage, ψ.left_inv hx]; exact hj'⟩
    have e : Φ ∘ Ψ =ᶠ[nhds (ψ y₀)] id := Filter.eventually_of_mem (hV.mem_nhds hm) fun w hw => by
      simp only [Function.comp_apply, Ψ, Φ, ch.e.left_inv hw.2, ψ.right_inv hw.1, id]
    have hc' : HasFDerivAt (Φ ∘ Ψ) ((fderiv ℂ Φ (ch.e y₀)).comp (fderiv ℂ Ψ (ψ y₀))) (ψ y₀) :=
      HasFDerivAt.comp (ψ y₀) (hΨy ▸ hΦd) hΨd
    exact (hc'.congr_of_eventuallyEq e.symm).unique (hasFDerivAt_id _)
  have hfd : fderiv ℝ Φ (ch.e y₀) = (fderiv ℂ Φ (ch.e y₀)).restrictScalars ℝ :=
    (hΦd.restrictScalars ℝ).fderiv
  have hbij : Function.Bijective (fderiv ℝ Φ (ch.e y₀)) := by
    rw [hfd]
    refine ⟨fun a b hab => ?_, fun w => ⟨fderiv ℂ Ψ (ψ y₀) w, ?_⟩⟩
    · have := congrArg (fderiv ℂ Ψ (ψ y₀)) hab
      simpa using (congrArg (· a) hL).symm.trans (this.trans (congrArg (· b) hL))
    · simpa using congrArg (· w) hR
  have hHc : ContinuousOn H U := by
    have hu' : DifferentiableOn ℂ (u ∘ ch.e.symm) (ch.e.target ∩ ch.e.symm ⁻¹' ψ.source) :=
      (((isAlgAtlas_atlasOf (Y := O.var c) σ).holoOn_iff ((O.var c).an σ) ψ.open_source).1 hu) ch
    have hn0 : ∀ v ∈ U, ‖u (ch.e.symm v)‖ ^ 2 ≠ 0 := fun v hv => by
      simpa using hu0 _ hv.2
    refine (continuousOn_const.sub ((hu'.continuousOn.norm.pow 2).log hn0)).add
      (continuousOn_const.mul ?_)
    simp only [GlobalTheory.DivSec.divPot]
    refine continuousOn_finset_sum _ fun i _ => ?_
    refine (((GlobalTheory.DivSec.eq_spec hn i y₀).2.2.1 ch).continuousOn.mono fun v hv =>
      ⟨hv.1, GlobalTheory.DivSec.mem_eqV hn (hsub hv.2) i⟩).div_const _
  refine ⟨ch, U, Φ, H, I, hj', hU, ha, Set.inter_subset_left, ((hΦan.contDiffOn (n := 1) hU.uniqueDiffOn).restrict_scalars ℝ), hbij, hHc,
    fun v hv hI => ?_⟩
  have hz : ch.e.symm v ∈ ψ.source := hv.2
  have key := GlobalTheory.DivSec.norm_divSec_mul hn (hsub hz)
  rw [he _ hz] at key
  beta_reduce at key
  have hw : ∀ i, (∃ k, τ k = some i) → ψ (ch.e.symm v) i ≠ 0 := fun i hi =>
    hI i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  have hu1 : ‖u (ch.e.symm v)‖ ^ 2 ≠ 0 := by simpa using hu0 _ hz
  rw [hC.r_eq]
  change Real.exp 1 - Real.log ((∏ i, n i (ch.e.symm v)) ^ 2) = H v - ∑ i ∈ I, Real.log (‖ψ (ch.e.symm v) i‖ ^ 2)
  rw [← key, norm_mul, mul_pow, mul_pow, Real.log_mul (mul_ne_zero hu1 (GlobalTheory.CovTop.prod_ne_zero_of τ _ hw _
      (fun k i h => by simp [h]) (fun k h => by simp [h]))) (by positivity),
    Real.log_mul hu1 (GlobalTheory.CovTop.prod_ne_zero_of τ _ hw _ (fun k i h => by simp [h]) (fun k h => by simp [h])),
    GlobalTheory.CovTop.log_norm_prod_of τ hinj _ hw _ (fun k i h => by simp [h]) (fun k h => by simp [h]),
    Real.log_pow (n := 2) (Real.exp (-(GlobalTheory.DivSec.divPot hn).φ y₀ (ch.e.symm v))), Real.log_exp]
  simp only [H]
  push_cast
  ring

end
