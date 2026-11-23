import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtendAeLinearOfLocalSqBoundDenseStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AeEqOfDenseOfLocalSqBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBesselCoefficientCompactLeStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.BesselExt

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp]
  {σ : Mat k r → (H →L[ℂ] H)} {w : H} {a : ℝ} {μG : Measure (Mt k r)} {d : ℝ}
  {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {μS : Measure (Mt k r)}

theorem afun_add (hStd : Std σ w a μG d) (hSide : Side z π μS) {v : H} (hv : v ∈ DD σ w) (ξ : Wp)
    {u u' : H} (hu : u ∈ DD σ w) (hu' : u' ∈ DD σ w) {x : Mat k r} (hx : x ∈ GG k r) :
    Afun (psiGen k r z c) π μS σ (u + u') v ξ x =
      Afun (psiGen k r z c) π μS σ u v ξ x + Afun (psiGen k r z c) π μS σ u' v ξ x := by
  have hst := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hStd.2.1).1
  have h1 := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u) (hst x hx u hu) v hv).1
  have h2 := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u') (hst x hx u' hu') v hv).1
  simp only [Afun, be, map_add, coef_add_left, add_smul]
  rw [integral_add h1 h2, ContinuousLinearMap.add_apply]

theorem afun_smul (b : ℂ) (u v : H) (ξ : Wp) (x : Mat k r) :
    Afun (psiGen k r z c) π μS σ (b • u) v ξ x = b • Afun (psiGen k r z c) π μS σ u v ξ x := by
  simp only [Afun, be, map_smul, coef_smul_left, mul_smul]
  rw [integral_smul, ContinuousLinearMap.smul_apply]

theorem afun_mul_right (hσ : IsURepOn (GG k r) σ) (u v : H) (ξ : Wp) {x y : Mat k r}
    (hx : x ∈ GG k r) (hy : y ∈ GG k r) :
    Afun (psiGen k r z c) π μS σ (σ y u) v ξ x = Afun (psiGen k r z c) π μS σ u v ξ (x * y) := by
  simp only [Afun, hσ.1.2 x hx y hy, ContinuousLinearMap.comp_apply]

theorem afun_mul_left (hStd : Std σ w a μG d) (hSide : Side z π μS) {v : H} (hv : v ∈ DD σ w) (ξ : Wp)
    {u : H} (hu : u ∈ DD σ w) {s x : Mat k r} (hs : s ∈ Sset k r z) (hx : x ∈ GG k r)
    (hSG : Sset k r z ⊆ GG k r) :
    Afun (psiGen k r z c) π μS σ u v ξ (s * x) =
      PiS (psiGen k r z c) π s (Afun (psiGen k r z c) π μS σ u v ξ x) := by
  have hst := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hStd.2.1).1
  have h := ((GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u) (hst x hx u hu) v hv).2.1 s hs).1
  simp only [Afun]
  rw [hStd.2.1.1.2 s (hSG hs) x hx, ContinuousLinearMap.comp_apply, h, ContinuousLinearMap.comp_apply]

theorem continuous_lmulM' (s : Mat k r) : Continuous (lmulM s : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem lintegral_comp_le_image {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] {μ : Measure X} {φ : X → X} (hmp : MeasurePreserving φ μ μ) (hφ : Continuous φ)
    (f : X → ENNReal) {K : Set X} (hK : IsCompact K) (hf : AEMeasurable f μ) :
    ∫⁻ x in K, f (φ x) ∂μ ≤ ∫⁻ x in φ '' K, f x ∂μ := by
  have hm : MeasurableSet (φ '' K) := (hK.image hφ).isClosed.measurableSet
  have hmap : μ.map φ = μ := hmp.map_eq
  calc ∫⁻ x in K, f (φ x) ∂μ ≤ ∫⁻ x, (φ '' K).indicator f (φ x) ∂μ := by
        rw [← lintegral_indicator hK.isClosed.measurableSet]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K
        · simp [Set.indicator, hx, Set.mem_image_of_mem φ hx]
        · simp [Set.indicator, hx]
    _ = ∫⁻ y, (φ '' K).indicator f y ∂μ := by
        have := lintegral_map' (μ := μ) (f := (φ '' K).indicator f) (g := φ)
          (by rw [hmap]; exact hf.indicator hm) hφ.aemeasurable
        rw [hmap] at this
        exact this.symm
    _ = ∫⁻ y in φ '' K, f y ∂μ := lintegral_indicator hm _

end GlobalTheory.SgInf.BesselExt

open GlobalTheory.SgInf.BesselExt in

theorem GlobalTheory.SgInf.bessel_ext_bounded : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∃ T : H → Mat k r → Wp, (∀ u ∈ DD σ w, T u = Afun (psiGen k r z c) π μS σ u v ξ) ∧ (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x) + T u' (Matrix.of x)) ∧ (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) ∧ (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) ∧ (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x * y)) ∧ (∀ s ∈ Sset k r z, ∀ u : H, (fun x : Mt k r => T u (s * Matrix.of x)) =ᵐ[μG] fun x => PiS (psiGen k r z c) π s (T u (Matrix.of x))) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide v hv ξ
  have hσ : IsURepOn (GG k r) σ := hStd.2.1
  have hHaar : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hw0 : w ≠ 0 := by
    intro h; have h1 := hStd.2.2.2.1; rw [h, norm_zero] at h1; exact zero_ne_one h1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hSG : Sset k r z ⊆ GG k r := hcl.2.2.2.1.1
  have hDD := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hσ
  have hst : ∀ g ∈ GG k r, ∀ u ∈ DD σ w, σ g u ∈ DD σ w := hDD.1
  have hdense : Dense (DD σ w : Set H) := hDD.2.1 hStd.2.2.1 hw0
  have hconc : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := by
    rw [ae_iff]; exact hHaar.2.2.1
  let F : H → Mt k r → Wp := fun u x => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)
  let K : ℕ → Set (Mt k r) := fun n => Metric.closedBall 0 n
  have hKm : ∀ n, MeasurableSet (K n) := fun n => Metric.isClosed_closedBall.measurableSet
  have hKc : ∀ n, IsCompact (K n) := fun n => isCompact_closedBall 0 n
  have hcov : ⋃ n, K n = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨⌈‖x‖⌉₊, ?_⟩
    simp only [K, Metric.mem_closedBall, dist_zero_right]; exact Nat.le_ceil _
  have hsub : ∀ L : Set (Mt k r), IsCompact L → ∃ n, L ⊆ K n := by
    intro L hL
    obtain ⟨R, hR⟩ := hL.isBounded.subset_closedBall 0
    exact ⟨⌈R⌉₊, hR.trans (Metric.closedBall_subset_closedBall (Nat.le_ceil R))⟩
  have hadd : ∀ u ∈ DD σ w, ∀ u' ∈ DD σ w, F (u + u') =ᵐ[μG] fun x => F u x + F u' x := by
    intro u hu u' hu'
    filter_upwards [hconc] with x hx
    exact afun_add hStd hSide hv ξ hu hu' hx
  have hsmul : ∀ (b : ℂ), ∀ u ∈ DD σ w, F (b • u) =ᵐ[μG] fun x => b • F u x :=
    fun b u _ => Filter.Eventually.of_forall fun x => afun_smul b u v ξ _
  obtain ⟨T0, hT0D, hT0add, hT0smul, hT0b⟩ := GlobalTheory.T.extend_ae_linear_of_local_sq_bound_dense μG K hKm hcov (DD σ w) hdense F hadd hsmul
    (fun n => GlobalTheory.T.lintegral_besselCoefficient_compact_le k r σ w a μG d z c π μS hStd hSide v hv ξ (K n) (hKc n))
  have hT0m : ∀ u, AEStronglyMeasurable (T0 u) μG := by
    intro u
    have h : AEStronglyMeasurable (T0 u) (μG.restrict (⋃ n, K n)) :=
      aestronglyMeasurable_iUnion_iff.2 fun n => ((hT0b n).choose_spec u).1
    rwa [hcov, Measure.restrict_univ] at h
  have hT0bK : ∀ L : Set (Mt k r), IsCompact L → ∃ C : ℝ, ∀ u,
      ∫⁻ x in L, (‖T0 u x‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2) := by
    intro L hL
    obtain ⟨n, hn⟩ := hsub L hL
    obtain ⟨C, hC⟩ := hT0b n
    exact ⟨C, fun u => (lintegral_mono_set hn).trans (hC u).2⟩
  have hT0sub : ∀ u u', (fun x => T0 u x - T0 u' x) =ᵐ[μG] T0 (u - u') := by
    intro u u'
    filter_upwards [hT0add (u - u') u'] with x hx
    rw [sub_add_cancel] at hx
    rw [hx]; simp
  have hmeasn : ∀ u, AEMeasurable (fun x => (‖T0 u x‖₊ : ENNReal) ^ 2) μG := fun u =>
    (hT0m u).nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2
  refine ⟨fun u M => T0 u (Matrix.of.symm M), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; funext M; show T0 u _ = _; rw [hT0D u hu]; rfl
  · intro u u'; exact hT0add u u'
  · intro b u; exact hT0smul b u
  · intro L hL
    obtain ⟨n, hn⟩ := hsub L hL
    obtain ⟨C, hC⟩ := hT0b n
    exact ⟨C, fun u => ⟨(hC u).1.mono_measure (Measure.restrict_mono hn le_rfl),
      (lintegral_mono_set hn).trans (hC u).2⟩⟩
  · intro y hy u
    have hmp : MeasurePreserving (rmulM y) μG μG :=
      ⟨(continuous_rmulM y).measurable, (GlobalTheory.T.isUnimodular_besselModelUnitaryGroup k r μG hHaar).1 y hy⟩
    refine GlobalTheory.T.ae_eq_of_dense_of_local_sq_bound_alt μG K hKm hcov (DD σ w : Set H) hdense
      (fun u x => T0 (σ y u) x) (fun u x => T0 u (rmulM y x)) ?_ ?_ ?_ ?_ ?_ u
    · intro u u'
      filter_upwards [hT0sub (σ y u) (σ y u')] with x hx
      rw [hx, map_sub]
    · intro u u'; exact hmp.quasiMeasurePreserving.ae (hT0sub u u')
    · intro n
      obtain ⟨C, hC⟩ := hT0b n
      refine ⟨C, fun u => ⟨(hC (σ y u)).1, ?_⟩⟩
      rw [← hσ.2.1 y hy u]; exact (hC (σ y u)).2
    · intro n
      obtain ⟨C, hC⟩ := hT0bK _ ((hKc n).image (continuous_rmulM y))
      refine ⟨C, fun u => ⟨((hT0m u).comp_measurePreserving hmp).restrict, ?_⟩⟩
      exact (lintegral_comp_le_image hmp (continuous_rmulM y) _ (hKc n) (hmeasn u)).trans (hC u)
    · intro u hu
      show (fun x => T0 (σ y u) x) =ᵐ[μG] fun x => T0 u (rmulM y x)
      rw [hT0D _ (hst y hy u hu), hT0D u hu]
      filter_upwards [hconc] with x hx
      exact afun_mul_right hσ u v ξ hx hy
  · intro s hs u
    have hmp : MeasurePreserving (lmulM s : Mt k r → Mt k r) μG μG :=
      ⟨(continuous_lmulM' s).measurable, hHaar.2.2.2 s (hSG hs)⟩
    have hPi := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hSide.1 hSide.2.1 hSide.2.2.1
    have hPin : ‖PiS (psiGen k r z c) π s‖ ≤ 1 := (hPi.2.2.1 s hs).1
    have hnorm : ∀ e : Wp, ‖PiS (psiGen k r z c) π s e‖₊ ≤ ‖e‖₊ := fun e => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
      exact ((PiS (psiGen k r z c) π s).le_opNorm e).trans
        (mul_le_of_le_one_left (norm_nonneg _) hPin)
    refine GlobalTheory.T.ae_eq_of_dense_of_local_sq_bound_alt μG K hKm hcov (DD σ w : Set H) hdense
      (fun u x => T0 u (lmulM s x)) (fun u x => PiS (psiGen k r z c) π s (T0 u x)) ?_ ?_ ?_ ?_ ?_ u
    · intro u u'; exact hmp.quasiMeasurePreserving.ae (hT0sub u u')
    · intro u u'
      filter_upwards [hT0sub u u'] with x hx
      rw [← map_sub, hx]
    · intro n
      obtain ⟨C, hC⟩ := hT0bK _ ((hKc n).image (continuous_lmulM' s))
      refine ⟨C, fun u => ⟨((hT0m u).comp_measurePreserving hmp).restrict, ?_⟩⟩
      exact (lintegral_comp_le_image hmp (continuous_lmulM' s) _ (hKc n) (hmeasn u)).trans (hC u)
    · intro n
      obtain ⟨C, hC⟩ := hT0b n
      refine ⟨C, fun u => ⟨(PiS (psiGen k r z c) π s).continuous.comp_aestronglyMeasurable (hC u).1, ?_⟩⟩
      refine le_trans (lintegral_mono fun x => ?_) (hC u).2
      exact pow_le_pow_left₀ (by positivity) (ENNReal.coe_le_coe.2 (hnorm _)) 2
    · intro u hu
      show (fun x => T0 u (lmulM s x)) =ᵐ[μG] fun x => PiS (psiGen k r z c) π s (T0 u x)
      rw [hT0D u hu]
      filter_upwards [hconc] with x hx
      exact afun_mul_left hStd hSide hv ξ hu hs hx hSG
