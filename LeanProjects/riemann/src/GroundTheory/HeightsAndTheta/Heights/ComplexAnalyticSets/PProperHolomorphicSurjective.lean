import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperHolomorphicSurjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCompactHolomorphicFibreFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRankDeficientFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicZeroSetDimH
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHausdorffNullComplementConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric MeasureTheory
open scoped ENNReal NNReal

namespace ProperHolomorphicSurjective

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

noncomputable def jac {k : ℕ} (g : (Fin k → ℂ) → Fin k → ℂ) (v : Fin k → ℂ) : ℂ :=
  LinearMap.det (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)

theorem jac_ne_zero_iff {k : ℕ} (g : (Fin k → ℂ) → Fin k → ℂ) (v : Fin k → ℂ) :
    jac g v ≠ 0 ↔ Function.Injective (fderiv ℂ g v) := by
  rw [jac, ← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, LinearMap.injective_iff_surjective.1 h⟩

theorem differentiableOn_jac {k : ℕ} {Ω : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → Fin k → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) : DifferentiableOn ℂ (jac g) Ω := by
  have hfd : DifferentiableOn ℂ (fderiv ℂ g) Ω :=
    (analyticOnNhd_of_differentiableOn hΩ hg).fderiv.differentiableOn
  have hentry : ∀ i j : Fin k,
      DifferentiableOn ℂ (fun v => fderiv ℂ g v (Pi.single j 1) i) Ω := fun i j =>
    differentiableOn_pi.1 (hfd.clm_apply (differentiableOn_const _)) i
  have hjac : jac g = fun v => ∑ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, fderiv ℂ g v (Pi.single i 1) (σ i) := by
    funext v
    rw [jac, ← LinearMap.det_toMatrix', Matrix.det_apply']
    simp [LinearMap.toMatrix'_apply]
  rw [hjac]
  refine DifferentiableOn.fun_sum fun σ _ => (differentiableOn_const _).mul ?_
  intro x hx
  exact (HasFDerivWithinAt.finsetProd (u := Finset.univ)
    (g := fun i v => fderiv ℂ g v (Pi.single i 1) (σ i))
    fun i _ => ((hentry (σ i) i) x hx).hasFDerivWithinAt).differentiableWithinAt

theorem proof (hFin : CompactHolomorphicFibreFinite.Statement) (hInf : RankDeficientFibreInfinite.Statement)
    (hDim : HolomorphicZeroSetDimH.Statement) (hConn : HausdorffNullComplementConnected.Statement) :
    ProperHolomorphicSurjective.Statement := by
  intro k Ω D g hΩ hΩne hD hDc hg hmaps hprop
  refine Set.Subset.antisymm (Set.image_subset_iff.2 hmaps) ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro y _
    obtain ⟨v, hv⟩ := hΩne
    exact ⟨v, hv, Subsingleton.elim _ _⟩
  have han := analyticOnNhd_of_differentiableOn hΩ hg
  have hfr : Module.finrank ℝ (Fin k → ℂ) = 2 * k := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

  have hopen : ∀ v ∈ Ω, jac g v ≠ 0 → g '' Ω ∈ 𝓝 (g v) := by
    intro v hv hdet
    have he : ((LinearMap.equivOfDetNeZero (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)
        hdet).toContinuousLinearEquiv : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) = fderiv ℂ g v := by
      ext1 u
      rfl
    have hs : HasStrictFDerivAt g ((LinearMap.equivOfDetNeZero
        (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) hdet).toContinuousLinearEquiv :
          (Fin k → ℂ) →L[ℂ] Fin k → ℂ) v := by
      rw [he]
      exact (han v hv).hasStrictFDerivAt
    rw [← hs.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hΩ.mem_nhds hv)

  have hreg : ∀ W ⊆ Ω, IsOpen W → W.Nonempty → ∃ w ∈ W, jac g w ≠ 0 := by
    intro W hW hWo hWne
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    obtain ⟨y, hy⟩ := hInf k k W g hWo hWne (hg.mono hW)
      fun v hv hinj => (jac_ne_zero_iff g v).2 hinj (hcon v hv)
    obtain ⟨t, htW, hty⟩ := hy.nonempty
    have hyD : y ∈ D := hty ▸ hmaps (hW htW)
    have hcpt : IsCompact {v | v ∈ Ω ∧ g v = y} :=
      hprop {y} (Set.singleton_subset_iff.2 hyD) isCompact_singleton
    exact hy ((hFin k k Ω g y hΩ hg hcpt).subset fun t ht => ⟨hW ht.1, ht.2⟩)

  set C : Set (Fin k → ℂ) := g '' {v | v ∈ Ω ∧ jac g v = 0} with hC
  have hdimC : dimH C ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
    refine le_trans ?_ (hDim k Ω (jac g) hΩ (differentiableOn_jac hΩ hg) hreg)
    refine dimH_image_le_of_locally_lipschitzOn fun x hx => ?_
    obtain ⟨K, t, ht, hL⟩ := ((han x hx.1).contDiffAt (n := 1)).exists_lipschitzOnWith
    exact ⟨K, t, nhdsWithin_le_nhds ht, hL⟩
  have hnull : μH[(Module.finrank ℝ (Fin k → ℂ) : ℝ) - 1] C = 0 := by
    have hlt : dimH C < (((2 * k - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_natCast]
      calc dimH C ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := hdimC
        _ = ((2 * (k - 1) : ℕ) : ℝ≥0∞) := by push_cast; ring
        _ < ((2 * k - 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : 2 * (k - 1) < 2 * k - 1)
    have h0 := hausdorffMeasure_of_dimH_lt hlt
    have hexp : ((((2 * k - 1 : ℕ) : ℝ≥0)) : ℝ) = (Module.finrank ℝ (Fin k → ℂ) : ℝ) - 1 := by
      rw [hfr, NNReal.coe_natCast, Nat.cast_sub (by omega)]
      push_cast
      ring
    rwa [hexp] at h0
  have hR : IsPreconnected (D \ C) := hConn (Fin k → ℂ) D C hD hDc hnull

  have hclosed : ∀ y ∈ D, y ∈ closure (g '' Ω) → y ∈ g '' Ω := by
    intro y hyD hycl
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 hD y hyD
    have hLD : closedBall y (r / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hrD
    have hK := hprop (closedBall y (r / 2)) hLD (isCompact_closedBall y (r / 2))
    have hgK : IsCompact (g '' (Ω ∩ g ⁻¹' closedBall y (r / 2))) :=
      hK.image_of_continuousOn (hg.continuousOn.mono Set.inter_subset_left)
    refine Set.image_mono Set.inter_subset_left (hgK.isClosed.closure_subset ?_)
    rw [mem_closure_iff_nhds] at hycl ⊢
    intro U hU
    obtain ⟨z, ⟨hzU, hzB⟩, v, hv, rfl⟩ :=
      hycl (U ∩ ball y (r / 2)) (Filter.inter_mem hU (ball_mem_nhds y (by linarith)))
    exact ⟨g v, hzU, v, ⟨hv, ball_subset_closedBall hzB⟩, rfl⟩

  have hne : ((D \ C) ∩ interior (g '' Ω)).Nonempty := by
    obtain ⟨w, hwΩ, hw⟩ := hreg Ω subset_rfl hΩ hΩne
    have hN : g '' Ω ∈ 𝓝 (g w) := hopen w hwΩ hw
    by_contra hcon
    have hsubC : interior (g '' Ω) ⊆ C := by
      intro z hz
      by_contra hzC
      exact hcon ⟨z, ⟨Set.image_subset_iff.2 hmaps (interior_subset hz), hzC⟩, hz⟩
    have h1 : dimH (interior (g '' Ω)) = Module.finrank ℝ (Fin k → ℂ) :=
      Real.dimH_of_nonempty_interior (by rw [interior_interior]; exact ⟨g w, mem_interior_iff_mem_nhds.2 hN⟩)
    have h2 := (dimH_mono hsubC).trans hdimC
    rw [h1, hfr, show (2 : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞) = ((2 * (k - 1) : ℕ) : ℝ≥0∞) by push_cast; ring]
      at h2
    have h3 : 2 * k ≤ 2 * (k - 1) := by exact_mod_cast h2
    omega

  have hRsub : D \ C ⊆ interior (g '' Ω) ∪ (closure (g '' Ω))ᶜ := by
    rintro y ⟨hyD, hyC⟩
    by_cases hyE : y ∈ g '' Ω
    · left
      obtain ⟨v, hv, rfl⟩ := hyE
      have hjv : jac g v ≠ 0 := fun h0 => hyC ⟨v, ⟨hv, h0⟩, rfl⟩
      exact mem_interior_iff_mem_nhds.2 (hopen v hv hjv)
    · right
      exact fun hcl => hyE (hclosed y hyD hcl)
  have hdisj : Disjoint (interior (g '' Ω)) (closure (g '' Ω))ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 (interior_subset.trans subset_closure)
  have hRE := hR.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj hRsub hne
  intro y hyD
  by_cases hyC : y ∈ C
  · exact Set.image_mono (fun v hv => hv.1) hyC
  · exact interior_subset (hRE ⟨hyD, hyC⟩)

end ProperHolomorphicSurjective

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
