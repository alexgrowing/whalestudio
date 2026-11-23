import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPosFiniteDensityOfAlmostTranslationInvaria
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateChartBallDistortion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReImMapSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactSpaceUpqTZeroRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpBallUMemNhds

open Formalism.BasicNotions MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompactDualExists

theorem exists_density_of_chart (V M G : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (lam : Measure V) [lam.IsAddHaarMeasure] (μ : Measure G) [μ.IsHaarMeasure]
    (e : V → G) (m : G → M) (ι : V →ₗᵢ[ℝ] M) (L : G → M →L[ℝ] M) (he : Continuous e)
    (h0 : e 0 = 1) (hd : HasStrictFDerivAt (fun x => m (e x)) ι.toContinuousLinearMap 0)
    (hL : ContinuousAt L 1) (hL1 : L 1 = ContinuousLinearMap.id ℝ M)
    (hm : ∀ g h, m (g * h) = L g (m h)) (hn : ∀ r : ℝ, 0 < r → e '' ball 0 r ∈ 𝓝 (1 : G)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto (fun r : ℝ => μ (e '' ball 0 r) / lam (ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  haveI : ProperSpace V := FiniteDimensional.proper_real V

  obtain ⟨δ₀, hδ₀, hinj⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ InjOn e (closedBall 0 δ₀) := by
    obtain ⟨s, hs, ha⟩ := hd.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
    obtain ⟨δ, hδ, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hs
    refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
    have h1 := ha x (hsub hx) y (hsub hy)
    simp only [hxy, sub_self, zero_sub, norm_neg, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map] at h1
    have h2 : ‖x - y‖ ≤ 0 := by
      have h3 : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
      rw [h3] at h1
      linarith
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)

  have hK : MeasurableSet (closedBall (0 : V) δ₀) := measurableSet_closedBall
  have hemb := ContinuousOn.measurableEmbedding hK he.continuousOn hinj
  set ν : Measure V := (μ.comap ((closedBall (0 : V) δ₀).domRestrict e)).map Subtype.val with hν
  have hνS : ∀ S : Set V, MeasurableSet S → ν S = μ (e '' (S ∩ closedBall 0 δ₀)) := by
    intro S hS
    rw [hν, Measure.map_apply measurable_subtype_coe hS, hemb.comap_apply]
    congr 1
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have hνB : ∀ (x : V) (r : ℝ), ‖x‖ + r ≤ δ₀ → ν (ball x r) = μ (e '' ball x r) := by
    intro x r h
    rw [hνS _ measurableSet_ball, inter_eq_left.2]
    intro y hy
    rw [mem_ball_iff_norm] at hy
    rw [mem_closedBall_zero_iff]
    have := norm_le_norm_add_norm_sub' y x
    linarith
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνS _ MeasurableSet.univ, univ_inter]
    exact ((isCompact_closedBall _ _).image he).measure_lt_top
  have hpos : ∀ r : ℝ, 0 < r → ν (ball 0 r) ≠ 0 := by
    intro r hr
    have h1 : ν (ball 0 (min r δ₀)) ≠ 0 := by
      rw [hνB _ _ (by simp)]
      exact (μ.measure_pos_of_mem_nhds (hn _ (lt_min hr hδ₀))).ne'
    exact fun h => h1 (measure_mono_null (ball_subset_ball (min_le_left _ _)) h)
  obtain ⟨c, hc0, hct, hc⟩ := GlobalTheory.exists_pos_finite_density_of_almost_translation_invariant V lam ν hpos (by
    intro κ hκ
    obtain ⟨δ, hδ, H⟩ := GlobalTheory.translate_chart_ball_distortion V M G e m ι L he h0 hd hL hL1 hm hn κ hκ
    have hκ0 : 0 < κ + 1 := by linarith
    refine ⟨min δ (δ₀ / (κ + 1)), lt_min hδ (div_pos hδ₀ hκ0), fun x hx r hr => ?_⟩
    rw [mem_ball_zero_iff, lt_min_iff, lt_div_iff₀ hκ0] at hx
    obtain ⟨hr0, hr⟩ := hr
    rw [lt_min_iff, lt_div_iff₀ hκ0] at hr
    obtain ⟨H1, H2⟩ := H x (mem_ball_zero_iff.2 hx.1) r ⟨hr0, hr.1⟩
    have hx0 := norm_nonneg x
    have hb : ‖x‖ + κ * r ≤ δ₀ := by
      rcases le_total ‖x‖ r with h | h <;> nlinarith [hx.2, hr.2]
    have himg : ∀ S : Set G, μ ((fun g => e x * g) '' S) = μ S := fun S => by
      rw [image_mul_left, measure_preimage_mul]
    rw [hνB 0 r (by rw [norm_zero]; nlinarith), hνB x (κ * r) hb, hνB x r (by nlinarith),
      hνB 0 (κ * r) (by rw [norm_zero]; linarith)]
    exact ⟨(himg _).symm.trans_le (measure_mono H1), (measure_mono H2).trans_eq (himg _)⟩)
  refine ⟨c, hc0, hct, hc.congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with r hr
  rw [hνB 0 r (by rw [norm_zero]; linarith [hr.2])]

section Matrices

variable {n : Type} [Fintype n] [DecidableEq n]

@[instance_reducible] def sumNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℂ) :=
  fast_instance% @PiLp.normedAddCommGroupToPi 1 _ _ _ _ (fun _ ↦ PiLp.normedAddCommGroupToPi 1 _)

attribute [local instance] sumNormedAddCommGroup

@[instance_reducible] def sumNormedSpace : NormedSpace ℝ (Matrix n n ℂ) :=
  fast_instance%
  letI := PiLp.seminormedAddCommGroupToPi 1 (fun _ : n ↦ ℂ)
  letI := PiLp.normedSpaceSeminormedAddCommGroupToPi (R := ℝ) 1 (fun _ : n ↦ ℂ)
  PiLp.normedSpaceSeminormedAddCommGroupToPi 1 _

attribute [local instance] sumNormedSpace

omit [DecidableEq n] in
theorem sum_norm_def (A : Matrix n n ℂ) : ‖A‖ = ∑ i, ∑ j, ‖A i j‖ := by
  change ‖WithLp.toLp 1 fun i => WithLp.toLp 1 fun j => A i j‖ = _
  simp [PiLp.norm_eq_of_L1]

end Matrices

theorem exp_strict {n : Type} [Fintype n] [DecidableEq n] :
    HasStrictFDerivAt (𝕜 := ℝ) (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      (ContinuousLinearMap.id ℝ (Matrix n n ℂ)) 0 := by
  letI := Matrix.linftyOpNormedRing (n := n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := n) (R := ℝ) (α := ℂ)
  exact @hasStrictFDerivAt_exp_zero ℝ (Matrix n n ℂ) _ _ _ (FiniteDimensional.complete ℝ _)

theorem exp_cont {n : Type} [Fintype n] [DecidableEq n] :
    Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by
  letI := Matrix.linftyOpNormedRing (n := n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := n) (R := ℚ) (α := ℂ)
  exact @NormedSpace.exp_continuous (Matrix n n ℂ) _ _
    (inferInstanceAs (CompleteSpace (n → n → ℂ)))

theorem exp_neg_mul {n : Type} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero]

theorem Jpq_mul_self (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem exp_mem {P Q : ℕ} (X : lieU P Q) :
    (NormedSpace.exp X.1).conjTranspose * Formalism.UG.Jpq P Q * NormedSpace.exp X.1 =
      Formalism.UG.Jpq P Q := by
  have hJ := Jpq_mul_self P Q
  have hinv : (Formalism.UG.Jpq P Q)⁻¹ = Formalism.UG.Jpq P Q := Matrix.inv_eq_left_inv hJ
  have hu : IsUnit (Formalism.UG.Jpq P Q) := ⟨⟨_, _, hJ, hJ⟩, rfl⟩
  have hX : X.1.conjTranspose * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X.1 = 0 := X.2
  have hYh : X.1.conjTranspose = Formalism.UG.Jpq P Q * (-X.1) * (Formalism.UG.Jpq P Q)⁻¹ := by
    rw [hinv, Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left hX, Matrix.mul_assoc, hJ,
      Matrix.mul_one]
  rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hu, hinv,
    Matrix.mul_assoc (Formalism.UG.Jpq P Q * NormedSpace.exp (-X.1)), hJ, Matrix.mul_one,
    Matrix.mul_assoc, exp_neg_mul, Matrix.mul_one]

def expU {P Q : ℕ} (X : lieU P Q) : UpqT P Q :=
  (⟨⟨NormedSpace.exp X.1, NormedSpace.exp (-X.1), by simpa using exp_neg_mul (-X.1),
    exp_neg_mul X.1⟩, exp_mem X⟩ : Formalism.UG.Upq P Q)

theorem mat_expU {P Q : ℕ} (X : lieU P Q) : (expU X).mat = NormedSpace.exp X.1 := rfl

theorem mat_injective {P Q : ℕ} : Function.Injective (UpqT.mat (P := P) (Q := Q)) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem continuous_expU {P Q : ℕ} : Continuous (expU (P := P) (Q := Q)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact exp_cont.comp continuous_subtype_val
  · exact exp_cont.comp continuous_subtype_val.neg

theorem continuous_mat {P Q : ℕ} : Continuous (UpqT.mat (P := P) (Q := Q)) :=
  Units.continuous_val.comp continuous_subtype_val

theorem image_expU {P Q : ℕ} (S : Set (lieU P Q)) :
    expU '' S = {g : UpqT P Q | ∃ X ∈ S, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} := by
  ext g
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX, rfl⟩
  · rintro ⟨X, hX, h⟩
    exact ⟨X, hX, mat_injective h.symm⟩

attribute [local instance] sumNormedAddCommGroup sumNormedSpace in

theorem exists_omegaDensity {P Q : ℕ} (μ : Measure (UpqT P Q)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ OmegaDensity μ c := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI : T2Space (UpqT P Q) := inferInstanceAs (T2Space (Formalism.UG.Upq P Q))
  obtain ⟨lam, hlam⟩ := GlobalTheory.CompactDualOmega.exists_isOmegaLeb P Q
  have hball : ∀ r : ℝ, ball (0 : lieU P Q) r = ballU P Q r := by
    intro r
    ext X
    rw [mem_ball_zero_iff, Submodule.coe_norm, sum_norm_def]
    rfl
  let L₀ : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →ₗ[ℝ]
      (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →L[ℝ] Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  obtain ⟨c, hc0, hct, hc⟩ := @exists_density_of_chart (lieU P Q)
    (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (UpqT P Q) _ _ _ _ ⟨rfl⟩ _ _ _ _ _ _ _ _
    lam hlam.1 μ _ expU UpqT.mat
    (lieU P Q).subtypeₗᵢ (fun g => L₀ g.mat) continuous_expU
    (mat_injective (by rw [mat_expU]; exact (NormedSpace.exp_zero (𝔸 := Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))))
    (HasStrictFDerivAt.comp (0 : lieU P Q) (g := NormedSpace.exp) (f := Subtype.val)
      exp_strict (lieU P Q).subtypeL.hasStrictFDerivAt)
    (hL₀.comp continuous_mat).continuousAt
    (by ext1 A; exact Matrix.one_mul A) (fun g h => rfl)
    (fun r hr => by rw [image_expU, hball]; exact GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds P Q r hr)
  refine ⟨c, hc0, hct, lam, hlam, ?_⟩
  simp only [image_expU, hball] at hc
  exact hc

theorem exists_haar_of_density (P Q : ℕ) (c : ℝ≥0∞) (h0 : c ≠ 0) (ht : c ≠ ⊤) :
    ∃ μ : Measure (UpqT P Q), μ.IsHaarMeasure ∧ OmegaDensity μ c := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI : LocallyCompactSpace (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  obtain ⟨d, hd0, hdt, hd⟩ := exists_omegaDensity (Measure.haar : Measure (UpqT P Q))
  have hq : c / d ≠ ⊤ := ENNReal.div_ne_top ht hd0
  have hq0 : c / d ≠ 0 := ENNReal.div_ne_zero.2 ⟨h0, hdt⟩
  refine ⟨(c / d).toNNReal • Measure.haar,
    Measure.IsHaarMeasure.nnreal_smul _ (ENNReal.toNNReal_ne_zero.2 ⟨hq0, hq⟩), ?_⟩
  have := CompactDualUnique.omegaDensity_smul (c / d).toNNReal hd
  rwa [ENNReal.coe_toNNReal hq, ENNReal.div_mul_cancel hd0 hdt] at this

theorem exists_prob_haar (N : ℕ) :
    ∃ μ : Measure (UpqT N 0), μ.IsHaarMeasure ∧ IsProbabilityMeasure μ := by
  haveI : IsTopologicalGroup (UpqT N 0) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq N 0))
  haveI : BorelSpace (UpqT N 0) := ⟨rfl⟩
  haveI : CompactSpace (UpqT N 0) := GlobalTheory.compactSpace_UpqT_zero_right N
  exact ⟨Measure.haarMeasure ⊤, inferInstance,
    ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (UpqT N 0)))⟩⟩

theorem nonempty_cdHaar : Nonempty CDHaar := by
  choose p hp hp1 using exists_prob_haar
  choose c hc0 hct hc using fun N => haveI := hp N; exists_omegaDensity (p N)
  choose q hq hqc using fun P Q => exists_haar_of_density P Q (c (P + Q)) (hc0 _) (hct _)
  let cd : ∀ P Q : ℕ, Measure (UpqT P Q) := fun P Q =>
    match Q with
    | 0 => p P
    | Q + 1 => q P (Q + 1)
  refine ⟨⟨cd, fun P Q => ?_, hp1, fun P Q => ⟨c (P + Q), hc0 _, hct _, ?_, hc _⟩⟩⟩
  · cases Q with
    | zero => exact hp P
    | succ Q => exact hq P (Q + 1)
  · cases Q with
    | zero => exact hc P
    | succ Q => exact hqc P (Q + 1)

end GlobalTheory.CompactDualExists
