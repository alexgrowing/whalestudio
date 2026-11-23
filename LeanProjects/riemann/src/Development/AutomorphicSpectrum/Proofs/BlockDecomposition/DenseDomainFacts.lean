import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal

namespace GlobalTheory.CompanionTheory.DenseCpt

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

theorem val_emb (n : ℕ) : IsOpenEmbedding (Units.val : G n → Mat n) := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℂ) (α := ℂ)
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact Units.isOpenEmbedding_val

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem val_mem {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem continuous_extend {n : ℕ} {V : Type} [NormedAddCommGroup V] {b : G n → V} (hb : Continuous b)
    (hs : HasCompactSupport b) : Continuous (Function.extend (Units.val : G n → Mat n) b 0) := by
  have he := val_emb n
  refine continuous_of_tsupport fun x h => ?_
  obtain ⟨u, -, rfl⟩ := hs.tsupport_extend_zero_subset he.continuous h
  rw [← he.continuousAt_iff]
  have : Function.extend (Units.val : G n → Mat n) b 0 ∘ Units.val = b :=
    funext fun y => he.injective.extend_apply _ _ _
  rw [this]
  exact hb.continuousAt

theorem exists_smooth {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {b : G n → V}
    (hb : Continuous b) (hs : HasCompactSupport b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : Mat n → V, ContDiff ℝ ∞ f ∧ (∀ y : G n, dist (b y) (f y.val) ≤ δ) ∧
      ∀ y, y ∉ (Units.val : G n → Mat n) '' tsupport b → f y = 0 := by
  have he := val_emb n
  obtain ⟨f, hf, hd, hsu⟩ := (continuous_extend hb hs).exists_contDiff_approx ⊤ (ε := fun _ => δ)
    continuous_const fun _ => hδ
  refine ⟨f, hf, fun y => ?_, fun y hy => ?_⟩
  · have := hd y.val
    rw [show Function.extend (Units.val : G n → Mat n) b 0 y.val = b y from he.injective.extend_apply _ _ _] at this
    rw [dist_comm]; exact this.le
  · by_contra hne
    have h1 := hsu (Function.mem_support.2 hne)
    exact hy (hs.tsupport_extend_zero_subset he.continuous (subset_tsupport _ h1))

theorem cpt_of {n : ℕ} {V : Type} [Zero V] (hL : LgFacts) {K : Set (G n)} (hK : IsCompact K) {f : Mat n → V}
    (hf : ∀ y, y ∉ (Units.val : G n → Mat n) '' K → f y = 0) : Cpt f := by
  have he := val_emb n
  have hc : IsCompact ((Units.val : G n → Mat n) '' K) := hK.image he.continuous
  have hsub : (Units.val : G n → Mat n) '' K ⊆ GLs n := by
    rintro _ ⟨u, -, rfl⟩; exact val_mem u
  have hcont : ContinuousOn (lg : Mat n → ℝ) ((Units.val : G n → Mat n) '' K) :=
    ((hL n).2.2.2.1.continuousOn).mono hsub
  obtain ⟨R, hR⟩ := (hc.image_of_continuousOn hcont).bddAbove
  refine ⟨R, fun y _ hy => hf y fun hm => ?_⟩
  exact absurd (hR ⟨y, hm, rfl⟩) (not_le.2 hy)

theorem denseD : DenseD := by
  intro n _ _ μ _ V _ _ hL
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (G n) := (val_emb n).isInducing.secondCountableTopology
  haveI : LocallyCompactSpace (G n) := (val_emb n).locallyCompactSpace
  intro x
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  have hp : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨b, hbs, hbd, hbc, hbm⟩ := (Lp.memLp x).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ε := ENNReal.ofReal (ε / 2)) (by simpa using hε2)
  set K := tsupport b with hKdef
  have hKc : IsCompact K := hbs
  set m : ℝ≥0∞ := μ K ^ (1 / (2 : ℝ≥0∞).toReal) with hm
  have hmt : m ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hKc.measure_lt_top.ne
  set c : ℝ := (ε / 2) / (m.toReal + 1) with hc
  have hm0 : 0 ≤ m.toReal := ENNReal.toReal_nonneg
  have hcpos : 0 < c := by positivity
  obtain ⟨f, hf, hd, hz⟩ := exists_smooth hbc hbs hcpos
  have hcf : Continuous fun y : G n => f y.val := hf.continuous.comp Units.continuous_val
  have hsupp : Function.support (fun y : G n => f y.val) ⊆ K := by
    intro y hy
    by_contra hyK
    exact hy (hz _ fun ⟨u, hu, he⟩ => hyK (Units.ext he ▸ hu))
  have hcs : HasCompactSupport fun y : G n => f y.val :=
    HasCompactSupport.of_support_subset_isCompact hKc hsupp
  have hg : MemLp (fun y : G n => f y.val) 2 μ := hcf.memLp_of_hasCompactSupport hcs
  have hbg : eLpNorm (b - fun y : G n => f y.val) 2 μ ≤ ENNReal.ofReal (ε / 2) := by
    refine (eLpNorm_sub_le_of_dist_bdd μ hp hKc.measurableSet hcpos.le hd (subset_tsupport b) hsupp).trans ?_
    change ENNReal.ofReal c * m ≤ _
    conv_lhs => rw [← ENNReal.ofReal_toReal hmt]
    rw [← ENNReal.ofReal_mul hcpos.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨hg.toLp _, ⟨f, hf.contDiffOn, cpt_of hL hKc hz, ?_⟩, ?_⟩
  · simp only [cls]; rw [dif_pos hg]
  · rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
      ← ENNReal.le_ofReal_iff_toReal_le ((Lp.memLp x).sub (Lp.memLp (hg.toLp _))).eLpNorm_ne_top hε.le]
    have h1 : eLpNorm (⇑x - ⇑(hg.toLp _)) 2 μ = eLpNorm (⇑x - fun y : G n => f y.val) 2 μ :=
      eLpNorm_congr_ae (by filter_upwards [hg.coeFn_toLp] with y hy; simp [hy])
    rw [h1]
    have h2 : (⇑x - fun y : G n => f y.val) = (⇑x - b) + (b - fun y : G n => f y.val) := by
      ext y; simp
    rw [h2]
    refine (eLpNorm_add_le ((Lp.memLp x).aestronglyMeasurable.sub hbm.aestronglyMeasurable)
      (hbm.aestronglyMeasurable.sub hg.aestronglyMeasurable) (by norm_num)).trans ?_
    calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hbd hbg
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hε2.le hε2.le]; congr 1; ring

end GlobalTheory.CompanionTheory.DenseCpt
