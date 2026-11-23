import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicVanishingDivisibleCoordStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseMapCoordDerivativeNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSmoothPotentialGlueStatement

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.SecFactor

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holo_chart {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {U : Set X} (hU : IsOpen U) {g : X → ℂ} (hg : A.HoloOn U g) :
    AnalyticOnNhd ℂ (g ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' U) := by
  obtain ⟨B, hAB, j, hj⟩ := PLC.exists_atlas_with A ψ hψ
  have := holoOn_of_compatible hAB hU hg j
  rwa [hj] at this

theorem smooth_chart {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {U : Set X} (hU : IsOpen U) {g : X → ℝ} (hg : A.SmoothOn U g) :
    ContDiffOn ℝ ∞ (g ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' U) := by
  obtain ⟨B, hAB, j, hj⟩ := PLC.exists_atlas_with A ψ hψ
  have := smoothOn_of_compatible hAB hU hg j
  rwa [hj] at this

theorem holo_coord {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) (i : Fin e) : A.HoloOn ψ.source (fun y => ψ y i) := fun j z hz =>
  ((ContinuousLinearMap.proj i : (Fin e → ℂ) →L[ℂ] ℂ).analyticAt _).comp ((hψ j).1 z hz)

theorem transition {A : FinHolAtlas e X} {ψ ψ' : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) (hψ' : IsCompatChart A ψ') :
    AnalyticOnNhd ℂ (ψ' ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' ψ'.source) := fun z hz => by
  rw [analyticAt_pi_iff]
  intro i
  exact holo_chart hψ ψ'.open_source (holo_coord hψ' i) z hz

theorem sq_norm_exp (a b : ℝ) (ha : 0 ≤ a) : (a * Real.exp (-b)) ^ 2 = a ^ 2 * Real.exp (-2 * b) := by
  rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring

theorem key_factor (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ)
    (D : Fin m → Set X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e))
    (hB : IsBoundary A L s D) (hP : IsAdaptedPolydisc A D ψ σ) (i : Fin m)
    (z0 : Fin e → ℂ) (hz0 : z0 ∈ Metric.ball (0 : Fin e → ℂ) 1) :
    ∃ V : Set (Fin e → ℂ), IsOpen V ∧ z0 ∈ V ∧ ∃ F : (Fin e → ℂ) → ℝ, ContDiffOn ℝ ∞ F V ∧
      ∀ z ∈ V ∩ Metric.ball (0 : Fin e → ℂ) 1,
        normSec (L i) (s i) (ψ.symm z) ^ 2 = Option.elim (σ i) 1 (fun k => ‖z k‖ ^ 2) * Real.exp (-F z) := by
  obtain ⟨hPot, hSec, hSNC, -⟩ := hB i
  obtain ⟨hcψ, hball, -, hD⟩ := hP
  set y0 := ψ.symm z0 with hy0def
  obtain ⟨ψ', hc', hy0, hsub, σ', -, hW, u, hu, hu0, hs⟩ := hSNC y0
  set Ω := ψ.target ∩ ψ.symm ⁻¹' ψ'.source ∩ Metric.ball (0 : Fin e → ℂ) 1 with hΩdef
  have hΩ : IsOpen Ω := (ψ.isOpen_inter_preimage_symm ψ'.open_source).inter Metric.isOpen_ball
  have hz0Ω : z0 ∈ Ω := ⟨⟨hball hz0, hy0⟩, hz0⟩
  set mf : (Fin e → ℂ) → ℂ := fun z => Option.elim (σ' i) 1 (fun j => ψ' (ψ.symm z) j) with hmf
  have hs' : ∀ y ∈ ψ'.source, s i y0 y = u y * Option.elim (σ' i) 1 (fun j => ψ' y j) := by
    intro y hy
    rw [hs y hy]
    congr 1
    rw [Finset.prod_eq_single i]
    · cases h : σ' i <;> simp [h]
    · intro k' _ hk'
      cases h : σ' k' <;> simp [h, Pi.single_apply, hk']
    · simp

  have hnorm : ∀ z ∈ Ω, normSec (L i) (s i) (ψ.symm z) ^ 2 =
      (‖u (ψ.symm z)‖ ^ 2 * ‖mf z‖ ^ 2) * Real.exp (-2 * (L i).φ y0 (ψ.symm z)) := by
    intro z hz
    have hy : ψ.symm z ∈ ψ'.source := hz.1.2
    have hg := hSec.2 (ψ.symm z) y0 (ψ.symm z) ⟨(L i).mem_U _, hsub hy⟩
    unfold normSec
    rw [hg, hs' _ hy, sq_norm_exp _ _ (norm_nonneg _), norm_mul, mul_pow]

  have hΦ : ContDiffOn ℝ ∞ (fun z => (L i).φ y0 (ψ.symm z)) Ω :=
    (smooth_chart hcψ ((L i).isOpen_U y0) (hPot.1 y0)).mono fun z hz => ⟨hz.1.1, hsub hz.1.2⟩
  have hU' : AnalyticOnNhd ℂ (fun z => u (ψ.symm z)) Ω :=
    (holo_chart hcψ ψ'.open_source hu).mono fun z hz => hz.1
  have hT : AnalyticOnNhd ℂ (fun z => ψ' (ψ.symm z)) Ω :=
    (transition hcψ hc').mono fun z hz => hz.1
  have hTj : ∀ j, AnalyticOnNhd ℂ (fun z => ψ' (ψ.symm z) j) Ω := fun j z hz =>
    ((ContinuousLinearMap.proj j : (Fin e → ℂ) →L[ℂ] ℂ).analyticAt _).comp (hT z hz)
  have hm : AnalyticOnNhd ℂ mf Ω := by
    cases h : σ' i with
    | none => simp only [hmf, h]; exact analyticOnNhd_const
    | some j => simp only [hmf, h]; exact hTj j

  have hmne : ∀ z ∈ Ω, ψ.symm z ∉ D i → mf z ≠ 0 := by
    intro z hz hzD hzero
    apply hzD
    cases h : σ' i with
    | none => simp [hmf, h] at hzero
    | some j =>
      simp only [hmf, h, Option.elim] at hzero
      have := (Set.ext_iff.1 (hW i) (ψ.symm z)).2 ⟨hz.1.2, j, h, hzero⟩
      exact this.1

  have key : ∃ V ⊆ Ω, IsOpen V ∧ z0 ∈ V ∧ ∃ a : (Fin e → ℂ) → ℂ, ContDiffOn ℝ ∞ a V ∧
      (∀ z ∈ V, a z ≠ 0) ∧ ∀ z ∈ V, ‖mf z‖ ^ 2 = Option.elim (σ i) 1 (fun k => ‖z k‖ ^ 2) * ‖a z‖ ^ 2 := by
    have hmC : ContDiffOn ℝ ∞ mf Ω := (hm.contDiffOn hΩ.uniqueDiffOn).restrict_scalars ℝ
    cases hσ : σ i with
    | none =>
      refine ⟨Ω, subset_rfl, hΩ, hz0Ω, mf, hmC, fun z hz => hmne z hz ?_, fun z _ => by simp⟩
      intro hzD
      obtain ⟨k, hk, -⟩ := (hD z hz.2 i).1 hzD
      simp [hσ] at hk
    | some k =>
      by_cases hk0 : z0 k = 0
      · have hy0D : y0 ∈ D i := (hD z0 hz0 i).2 ⟨k, hσ, hk0⟩
        obtain ⟨j, hj⟩ : ∃ j, σ' i = some j := by
          have := (Set.ext_iff.1 (hW i) y0).1 ⟨hy0D, hy0⟩
          obtain ⟨j, hj, -⟩ := this.2
          exact ⟨j, hj⟩
        have hvan : ∀ z ∈ Ω, z k = 0 → ψ' (ψ.symm z) j = 0 := by
          intro z hz hzk
          have hzD : ψ.symm z ∈ D i := (hD z hz.2 i).2 ⟨k, hσ, hzk⟩
          obtain ⟨j', hj', hzero⟩ := ((Set.ext_iff.1 (hW i) (ψ.symm z)).1 ⟨hzD, hz.1.2⟩).2
          rw [hj] at hj'
          cases hj'
          exact hzero
        obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hΩ z0 hz0Ω
        obtain ⟨g, hg, hg0, hgeq⟩ := GlobalTheory.T.holomorphic_vanishing_divisible_coord (fun z => ψ' (ψ.symm z) j) z0 r k hr hk0
          ((hTj j).mono hrV) (fun z hz hzk => hvan z (hrV hz) hzk)
        have hS : AnalyticOnNhd ℂ (fun w => ψ (ψ'.symm w)) (ψ'.target ∩ ψ'.symm ⁻¹' ψ.source) :=
          transition hc' hcψ
        have hy0ψ : y0 ∈ ψ.source := ψ.map_target (hball hz0)
        have hTz0 : ψ' y0 ∈ ψ'.target ∩ ψ'.symm ⁻¹' ψ.source :=
          ⟨ψ'.map_source hy0, by simp only [Set.mem_preimage, ψ'.left_inv hy0]; exact hy0ψ⟩
        have hne := GlobalTheory.T.inverse_map_coord_derivative_ne_zero (fun z => ψ' (ψ.symm z)) (fun w => ψ (ψ'.symm w)) z0 j k
          ((hT z0 hz0Ω).differentiableAt) ((hS _ hTz0).differentiableAt)
          (by show ψ (ψ'.symm (ψ' y0)) = z0; rw [ψ'.left_inv hy0, hy0def, ψ.right_inv (hball hz0)])
          (by
            filter_upwards [(ψ'.isOpen_inter_preimage_symm ψ.open_source).mem_nhds hTz0] with w hw
            show ψ' (ψ.symm (ψ (ψ'.symm w))) = w
            rw [ψ.left_inv hw.2, ψ'.right_inv hw.1])
          hk0
          (by filter_upwards [hΩ.mem_nhds hz0Ω] with z hz hzk using hvan z hz hzk)
        rw [← hg0] at hne
        refine ⟨Metric.ball z0 r ∩ g ⁻¹' {0}ᶜ, fun z hz => hrV hz.1,
          hg.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton,
          ⟨Metric.mem_ball_self hr, hne⟩, g, hg.mono Set.inter_subset_left, fun z hz => hz.2,
          fun z hz => ?_⟩
        simp only [hmf, hj, hσ, Option.elim]
        rw [hgeq z hz.1, norm_mul, mul_pow]
      · have hVo : IsOpen (Ω ∩ {z | z k ≠ 0}) :=
          hΩ.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
        have hcoord : AnalyticOnNhd ℂ (fun z : Fin e → ℂ => z k) (Ω ∩ {z | z k ≠ 0}) := fun z _ =>
          (ContinuousLinearMap.proj k : (Fin e → ℂ) →L[ℂ] ℂ).analyticAt z
        have hdiv : AnalyticOnNhd ℂ (fun z => mf z / z k) (Ω ∩ {z | z k ≠ 0}) :=
          (hm.mono Set.inter_subset_left).div hcoord fun z hz => hz.2
        refine ⟨Ω ∩ {z | z k ≠ 0}, Set.inter_subset_left, hVo, ⟨hz0Ω, hk0⟩, fun z => mf z / z k,
          (hdiv.contDiffOn hVo.uniqueDiffOn).restrict_scalars ℝ, fun z hz => ?_, fun z hz => ?_⟩
        · refine div_ne_zero (hmne z hz.1 fun hzD => ?_) hz.2
          obtain ⟨k', hk', hzk'⟩ := (hD z hz.1.2 i).1 hzD
          rw [hσ] at hk'
          cases hk'
          exact hz.2 hzk'
        · have h2 : z k ≠ 0 := hz.2
          simp only [hσ, Option.elim]
          rw [norm_div, div_pow]
          field_simp
  obtain ⟨V, hVΩ, hV, hz0V, a, ha, ha0, hma⟩ := key
  refine ⟨V, hV, hz0V, fun z => -Real.log (‖u (ψ.symm z)‖ ^ 2 * ‖a z‖ ^ 2) + 2 * (L i).φ y0 (ψ.symm z), ?_, ?_⟩
  · have hu2 : ContDiffOn ℝ ∞ (fun z => ‖u (ψ.symm z)‖ ^ 2) V :=
      (contDiff_norm_sq ℝ).comp_contDiffOn (((hU'.contDiffOn hΩ.uniqueDiffOn).restrict_scalars ℝ).mono hVΩ)
    have ha2 : ContDiffOn ℝ ∞ (fun z => ‖a z‖ ^ 2) V := (contDiff_norm_sq ℝ).comp_contDiffOn ha
    refine ((hu2.mul ha2).log fun z hz => ?_).neg.add ((hΦ.mono hVΩ).const_smul (2 : ℝ) |>.congr fun z _ => ?_)
    · exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (hu0 _ (hVΩ hz).1.2))) (pow_ne_zero _ (norm_ne_zero_iff.2 (ha0 z hz)))
    · simp [smul_eq_mul]
  · intro z hz
    rw [hnorm z (hVΩ hz.1), hma z hz.1]
    have hpos : 0 < ‖u (ψ.symm z)‖ ^ 2 * ‖a z‖ ^ 2 :=
      mul_pos (pow_pos (norm_pos_iff.2 (hu0 _ (hVΩ hz.1).1.2)) _) (pow_pos (norm_pos_iff.2 (ha0 z hz.1)) _)
    rw [neg_add, neg_neg, Real.exp_add, Real.exp_log hpos]
    have : Real.exp (-(2 * (L i).φ y0 (ψ.symm z))) = Real.exp (-2 * (L i).φ y0 (ψ.symm z)) := by ring_nf
    rw [this]; ring

theorem factor_on_polydisc : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ}
    (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)),
    IsBoundary A L s D → IsAdaptedPolydisc A D ψ σ → ∀ i, ∃ f : (Fin e → ℂ) → ℝ,
      ContDiffOn ℝ ∞ f (Metric.ball (0 : Fin e → ℂ) 1) ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1,
        normSec (L i) (s i) (ψ.symm z) ^ 2 = Option.elim (σ i) 1 (fun k => ‖z k‖ ^ 2) * Real.exp (-f z) := by
  intro e X _ A m L s D ψ σ hB hP i
  refine GlobalTheory.T.local_smooth_potential_glue (fun z => normSec (L i) (s i) (ψ.symm z) ^ 2)
    (fun z => Option.elim (σ i) 1 (fun k => ‖z k‖ ^ 2)) _ Metric.isOpen_ball ?_
    (fun z0 hz0 => key_factor A L s D ψ σ hB hP i z0 hz0)
  cases h : σ i with
  | none => simp
  | some k =>
    have : {z : Fin e → ℂ | Option.elim (some k) (1 : ℝ) (fun k => ‖z k‖ ^ 2) ≠ 0} =
        (fun z : Fin e → ℂ => z k) ⁻¹' {0}ᶜ := by
      ext z; simp
    rw [this]
    exact (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval k)

end GlobalTheory.SecFactor
