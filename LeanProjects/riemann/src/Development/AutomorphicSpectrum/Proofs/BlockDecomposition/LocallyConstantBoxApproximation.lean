import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureLocalBallStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorSandwichApprox
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherSide
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi.LocApprox

variable {F : Type} [Field F] [NumberField F]

theorem zero_mem_ball (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : (0 : Fv F v) ∈ ballV v k := by
  simp [ballV]

theorem neg_mem_ball (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) {x : Fv F v} (hx : x ∈ ballV v k) :
    -x ∈ ballV v k := by
  have : Valued.v (-x) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [Valuation.map_neg]; exact hx
  exact this

theorem add_mem_ball (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) {x y : Fv F v} (hx : x ∈ ballV v k)
    (hy : y ∈ ballV v k) : x + y ∈ ballV v k := by
  have : Valued.v (x + y) ≤ WithZero.exp (-(k : ℤ)) :=
    Valuation.map_add_le _ hx hy
  exact this

theorem isOpen_ball (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : IsOpen (ballV v k) :=
  (GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.isClopen_ballV v k).isOpen

theorem isClosed_ball (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : IsClosed (ballV v k) :=
  (GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.isClopen_ballV v k).isClosed

theorem isCompact_ball (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : IsCompact (ballV v k) :=
  (Formalism.L2.S.S7.AdeleLC.isCompact_integers v).of_isClosed_subset (isClosed_ball v k)
    (GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.ballV_subset v k)

def box0 (v : HeightOneSpectrum (𝓞 F)) (ι : Type) (k : ℕ) : Set (ι → Fv F v) :=
  Set.pi Set.univ fun _ => ballV v k

theorem small_box (v : HeightOneSpectrum (𝓞 F)) (ι : Type) [Fintype ι] {U : Set (ι → Fv F v)}
    (hU : U ∈ 𝓝 (0 : ι → Fv F v)) : ∃ k, box0 v ι k ⊆ U := by
  refine exists_subset_nhds_of_isCompact' (V := box0 v ι) ?_ ?_ ?_ ?_
  · intro a b
    refine ⟨max a b, fun y hy i hi => ?_, fun y hy i hi => ?_⟩
    · exact GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.antitone_ballV v (le_max_left a b) (hy i hi)
    · exact GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.antitone_ballV v (le_max_right a b) (hy i hi)
  · intro k
    exact isCompact_univ_pi fun _ => isCompact_ball v k
  · intro k
    exact isClosed_set_pi fun _ _ => isClosed_ball v k
  · intro y hy
    have : y = 0 := by
      funext i
      have h : y i ∈ ⋂ n, GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.ballV (F := F) v n :=
        Set.mem_iInter.2 fun n => (Set.mem_iInter.1 hy n) i (Set.mem_univ i)
      rw [GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.iInter_ballV] at h
      exact h
    rw [this]; exact hU

theorem exists_k_unif (v : HeightOneSpectrum (𝓞 F)) (ι : Type) [Fintype ι]
    (ψ : (ι → Fv F v) → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, ∀ y c : ι → Fv F v, (∀ i, y i - c i ∈ ballV v k) → |ψ y - ψ c| ≤ δ := by
  have hu : UniformContinuous ψ := hc.uniformContinuous_of_continuous hψ
  have h1 : {p : (ι → Fv F v) × (ι → Fv F v) | dist (ψ p.1) (ψ p.2) < δ} ∈ uniformity (ι → Fv F v) :=
    hu (Metric.dist_mem_uniformity hδ)
  rw [uniformity_eq_comap_nhds_zero (ι → Fv F v)] at h1
  obtain ⟨U, hU, hsub⟩ := h1
  obtain ⟨k, hk⟩ := small_box v ι hU
  refine ⟨k, fun y c h => ?_⟩
  have h2 : (c, y) ∈ (fun x : (ι → Fv F v) × (ι → Fv F v) => x.2 - x.1) ⁻¹' U :=
    hk fun i _ => h i
  have h3 := hsub h2
  have h4 : dist (ψ c) (ψ y) < δ := h3
  rw [Real.dist_eq, abs_sub_comm] at h4
  exact h4.le

theorem exists_reps {α : Type} (r : α → α → Prop) (hs : ∀ a b, r a b → r b a)
    (ht : ∀ a b c, r a b → r b c → r a c) (t : Finset α) :
    ∃ C ⊆ t, (∀ a ∈ C, ∀ b ∈ C, r a b → a = b) ∧ ∀ x ∈ t, x ∈ C ∨ ∃ c ∈ C, r x c :=
  _root_.UpperTheory.Reformulated.B.Rc5.exists_reps r hs ht t

theorem exists_centres (v : HeightOneSpectrum (𝓞 F)) (ι : Type) [Fintype ι] (k : ℕ)
    {K : Set (ι → Fv F v)} (hK : IsCompact K) :
    ∃ C : Finset (ι → Fv F v), (∀ c ∈ C, c ∈ K) ∧
      (∀ a ∈ C, ∀ b ∈ C, (∀ i, a i - b i ∈ ballV v k) → a = b) ∧
      ∀ y ∈ K, ∃ c ∈ C, ∀ i, y i - c i ∈ ballV v k := by
  have hnh : ∀ x ∈ K, {y : ι → Fv F v | ∀ i, y i - x i ∈ ballV v k} ∈ 𝓝[K] x := by
    intro x _
    refine mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds ?_ ?_)
    · have : {y : ι → Fv F v | ∀ i, y i - x i ∈ ballV v k} =
          ⋂ i, (fun y : ι → Fv F v => y i - x i) ⁻¹' ballV v k := by
        ext y; simp
      rw [this]
      refine isOpen_iInter_of_finite fun i => (isOpen_ball v k).preimage ?_
      exact (continuous_apply i).sub continuous_const
    · intro i; simpa using zero_mem_ball v k
  obtain ⟨t, hcov⟩ := hK.elim_nhdsWithin_subcover' _ hnh
  obtain ⟨C, hCt, hC, hCc⟩ := exists_reps (fun a b : ι → Fv F v => ∀ i, a i - b i ∈ ballV v k)
    (fun a b h i => by simpa using neg_mem_ball v k (h i))
    (fun a b c h h' i => by simpa using add_mem_ball v k (h i) (h' i)) (t.image Subtype.val)
  refine ⟨C, ?_, hC, ?_⟩
  · intro c hc
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 (hCt hc)
    exact x.2
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (hcov hy)
    rcases hCc x (Finset.mem_image_of_mem _ hxt) with h | ⟨c, hc, hr⟩
    · exact ⟨x, h, hyx⟩
    · exact ⟨c, hc, fun i => by simpa using add_mem_ball v k (hyx i) (hr i)⟩

theorem pointwise (v : HeightOneSpectrum (𝓞 F)) (ι : Type) [Fintype ι] (k : ℕ)
    (ψ : (ι → Fv F v) → ℝ) {δ : ℝ} (hδ : 0 < δ) (C : Finset (ι → Fv F v))
    (hunif : ∀ y c : ι → Fv F v, (∀ i, y i - c i ∈ ballV v k) → |ψ y - ψ c| ≤ δ)
    (hdisj : ∀ a ∈ C, ∀ b ∈ C, (∀ i, a i - b i ∈ ballV v k) → a = b)
    (hcov : ∀ y, ψ y ≠ 0 → ∃ c ∈ C, ∀ i, y i - c i ∈ ballV v k) (y : ι → Fv F v) :
    |ψ y - ∑ c ∈ C, ψ c * boxInd v k c y| ≤ δ * ∑ c ∈ C, boxInd v k c y := by
  by_cases h : ∃ c ∈ C, ∀ i, y i - c i ∈ ballV v k
  · obtain ⟨c, hc, hcy⟩ := h
    have key : ∀ c' ∈ C, boxInd v k c' y = if c' = c then 1 else 0 := by
      intro c' hc'
      by_cases hne : c' = c
      · subst hne
        simp [boxInd, hcy]
      · rw [if_neg hne]
        refine if_neg fun h' => hne (hdisj c' hc' c hc fun i => ?_)
        simpa using add_mem_ball v k (hcy i) (neg_mem_ball v k (h' i))
    have s1 : ∑ c' ∈ C, ψ c' * boxInd v k c' y = ψ c := by
      rw [Finset.sum_congr rfl fun c' hc' => by rw [key c' hc']]
      simp [hc]
    have s2 : ∑ c' ∈ C, boxInd v k c' y = 1 := by
      rw [Finset.sum_congr rfl key]
      simp [hc]
    rw [s1, s2, mul_one]
    exact hunif y c hcy
  · have hz : ∀ c ∈ C, boxInd v k c y = 0 := by
      intro c hc
      exact if_neg fun h' => h ⟨c, hc, h'⟩
    have hy : ψ y = 0 := by
      by_contra h0
      exact h (hcov y h0)
    rw [Finset.sum_eq_zero fun c hc => by rw [hz c hc, mul_zero],
      Finset.sum_eq_zero hz, hy]
    simp

theorem sigmaFinite_lam {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (hstd : IsStdV v lam) :
    SigmaFinite lam := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  obtain ⟨-, h1, h2, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  infer_instance

def boxS (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (k : ℕ) (c : ι → Fv F v) : Set (ι → Fv F v) :=
  Set.pi Set.univ fun i => (fun z => z - c i) ⁻¹' ballV v k

theorem mem_boxS (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (k : ℕ) (c y : ι → Fv F v) :
    y ∈ boxS v k c ↔ ∀ i, y i - c i ∈ ballV v k := by
  simp [boxS, Set.mem_pi]

theorem boxInd_eq (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (k : ℕ) (c : ι → Fv F v) :
    boxInd v k c = (boxS v k c).indicator 1 := by
  funext y
  by_cases h : ∀ i, y i - c i ∈ ballV v k
  · rw [Set.indicator_of_mem ((mem_boxS v k c y).2 h)]
    simp [boxInd, h]
  · rw [Set.indicator_of_notMem (fun h' => h ((mem_boxS v k c y).1 h'))]
    exact if_neg h

theorem real_boxS {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (hstd : IsStdV v lam)
    {ι : Type} [Fintype ι] (k : ℕ) (c : ι → Fv F v) :
    (Measure.pi fun _ : ι => lam).real (boxS v k c) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ Fintype.card ι)⁻¹ := by
  haveI := sigmaFinite_lam hstd
  have hq : (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ k)⁻¹ := by positivity
  rw [Measure.real, boxS, Measure.pi_pi]
  simp only [GlobalTheory.T.haar_measure_local_ball F v lam hstd k, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hq, inv_pow]

theorem loc_approx : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (ι : Type) [Fintype ι] (ψ : (ι → Fv F v) → ℝ), Continuous ψ → HasCompactSupport ψ → ∃ B : ℝ, 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → ∃ (k : ℕ) (C : Finset (ι → Fv F v)), (∀ y, |ψ y - ∑ c ∈ C, ψ c * boxInd v k c y| ≤ δ * ∑ c ∈ C, boxInd v k c y) ∧ (C.card : ℝ) * (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ Fintype.card ι)⁻¹ ≤ B ∧ |(∫ y, ψ y ∂(Measure.pi fun _ => lam)) - ∑ c ∈ C, ψ c * (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ Fintype.card ι)⁻¹| ≤ δ * B := by
  intro F _ _ v lam hstd ι _ ψ hψ hc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  obtain ⟨-, h1, h2, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := sigmaFinite_lam hstd
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (ι → Fv F v), μ = Measure.pi fun _ => lam := ⟨_, rfl⟩
  haveI : μ.IsAddHaarMeasure := hμ ▸ inferInstance
  rw [← hμ]
  have hreal : ∀ k c, μ.real (boxS v k c) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ Fintype.card ι)⁻¹ := fun k c => by
    rw [hμ]; exact real_boxS hstd k c
  have hmeas : ∀ k (c : ι → Fv F v), MeasurableSet (boxS v k c) := fun k c =>
    MeasurableSet.univ_pi fun i =>
      ((isOpen_ball v k).preimage (continuous_id.sub continuous_const)).measurableSet
  obtain ⟨W, hW⟩ : ∃ W : Set (ι → Fv F v), W =
      (fun p : (ι → Fv F v) × (ι → Fv F v) => p.1 + p.2) '' (tsupport ψ ×ˢ box0 v ι 0) := ⟨_, rfl⟩
  have hWc : IsCompact W := by
    rw [hW]
    exact (hc.prod (isCompact_univ_pi fun _ => isCompact_ball v 0)).image
      (continuous_fst.add continuous_snd)
  have hWfin : μ W ≠ ⊤ := hWc.measure_lt_top.ne
  refine ⟨μ.real W, measureReal_nonneg, fun δ hδ => ?_⟩
  obtain ⟨k, hk⟩ := exists_k_unif v ι ψ hψ hc hδ
  obtain ⟨C, hCK, hdisj, hcov⟩ := exists_centres v ι k hc
  obtain ⟨vol, hvol⟩ : ∃ vol : ℝ, vol = (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ Fintype.card ι)⁻¹ :=
    ⟨_, rfl⟩
  have hr : ∀ c, μ.real (boxS v k c) = vol := fun c => by rw [hvol]; exact hreal k c
  have hfin : ∀ c, μ (boxS v k c) ≠ ⊤ := by
    intro c
    have hcomp : IsCompact (boxS v k c) := by
      refine isCompact_univ_pi fun i => ?_
      have : (fun z : Fv F v => z - c i) ⁻¹' ballV v k = (fun z => z + c i) '' ballV v k := by
        ext z
        simp only [Set.mem_preimage, Set.mem_image]
        exact ⟨fun h => ⟨z - c i, h, by simp⟩, by rintro ⟨w, hw, rfl⟩; simpa using hw⟩
      rw [this]
      exact (isCompact_ball v k).image (continuous_id.add continuous_const)
    exact hcomp.measure_lt_top.ne
  have hsub : ∀ c ∈ C, boxS v k c ⊆ W := by
    intro c hc' y hy
    rw [hW]
    refine ⟨(c, y - c), ⟨hCK c hc', fun i _ => ?_⟩, by simp⟩
    exact GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.antitone_ballV v (Nat.zero_le k)
      ((mem_boxS v k c y).1 hy i)
  have hpd : (C : Set (ι → Fv F v)).PairwiseDisjoint (boxS v k) := by
    intro a ha b hb hab
    refine Set.disjoint_left.2 fun y hya hyb => hab (hdisj a ha b hb fun i => ?_)
    have h3 := add_mem_ball v k ((mem_boxS v k b y).1 hyb i)
      (neg_mem_ball v k ((mem_boxS v k a y).1 hya i))
    simpa using h3
  have hcard : (C.card : ℝ) * vol ≤ μ.real W := by
    calc (C.card : ℝ) * vol = ∑ c ∈ C, μ.real (boxS v k c) := by
          simp [hr]
      _ = μ.real (⋃ c ∈ C, boxS v k c) :=
          (measureReal_biUnion_finset hpd (fun c _ => hmeas k c) (fun c _ => hfin c)).symm
      _ ≤ μ.real W := measureReal_mono (Set.iUnion₂_subset hsub) hWfin
  have hcov' : ∀ y, ψ y ≠ 0 → ∃ c ∈ C, ∀ i, y i - c i ∈ ballV v k :=
    fun y hy => hcov y (subset_tsupport ψ hy)
  have hpt := pointwise v ι k ψ hδ C hk hdisj hcov'
  refine ⟨k, C, hpt, ?_, ?_⟩
  · rw [← hvol]; exact hcard
  rw [← hvol]
  have hψi : Integrable ψ μ := hψ.integrable_of_hasCompactSupport hc
  have hbi : ∀ c, Integrable (boxInd v k c) μ := by
    intro c
    rw [boxInd_eq]
    exact (integrable_indicator_iff (hmeas k c)).2
      (integrableOn_const (hfin c))
  have hint : ∀ c, ∫ y, boxInd v k c y ∂μ = vol := by
    intro c
    rw [boxInd_eq, integral_indicator_one (hmeas k c), hr]
  have hg : Integrable (fun y => ∑ c ∈ C, ψ c * boxInd v k c y) μ :=
    integrable_finset_sum _ fun c _ => (hbi c).const_mul _
  have hs : Integrable (fun y => ∑ c ∈ C, boxInd v k c y) μ :=
    integrable_finset_sum _ fun c _ => hbi c
  have e1 : ∫ y, ∑ c ∈ C, ψ c * boxInd v k c y ∂μ = ∑ c ∈ C, ψ c * vol := by
    rw [integral_finset_sum _ fun c _ => (hbi c).const_mul _]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_const_mul, hint]
  have e2 : ∫ y, ∑ c ∈ C, boxInd v k c y ∂μ = (C.card : ℝ) * vol := by
    rw [integral_finset_sum _ fun c _ => hbi c]
    simp [hint]
  have hb := norm_integral_le_of_norm_le (hs.const_mul δ)
    (Eventually.of_forall fun y => (by simpa [Real.norm_eq_abs] using hpt y :
      ‖ψ y - ∑ c ∈ C, ψ c * boxInd v k c y‖ ≤ δ * ∑ c ∈ C, boxInd v k c y))
  rw [integral_sub hψi hg, e1, integral_const_mul, e2, Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hcard hδ.le)

end GlobalTheory.CompanionTheory.Equi.LocApprox
end
