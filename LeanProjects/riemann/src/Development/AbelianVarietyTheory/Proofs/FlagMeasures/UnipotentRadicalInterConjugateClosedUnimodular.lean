import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass Metric
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.UnipUnimod

variable {k r : ℕ}

def Bd (a : Mat k r) (R : ℝ) : Prop := ∀ i j, ‖a i j‖ ≤ R

theorem Bd.mul {a b : Mat k r} {R R' : ℝ} (ha : Bd a R) (hb : Bd b R') :
    Bd (a * b) (((2 * r + k + 1 : ℕ) : ℝ) * (R * R')) := by
  intro i j
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))), ‖a i l * b l j‖ ≤ R * R' := fun l _ => by
    rw [norm_mul]
    exact mul_le_mul (ha i l) (hb l j) (norm_nonneg _) ((norm_nonneg _).trans (ha i l))
  simpa using Finset.sum_le_card_nsmul _ _ _ this

theorem bd_iff {x y : Mt k r} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ closedBall y R ↔ Bd (Matrix.of x - Matrix.of y) R := by
  rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hR]
  refine forall_congr' fun i => ?_
  rw [pi_norm_le_iff_of_nonneg hR]
  rfl

theorem mem_closedBall_zero_iff_matrixEntriesBoundedBy {x : Mt k r} {R : ℝ} (hR : 0 ≤ R) : x ∈ closedBall (0 : Mt k r) R ↔ Bd (Matrix.of x) R := by
  rw [bd_iff hR]
  exact Iff.of_eq (congrArg (Bd · R) (sub_zero _))

theorem bd_Hpk : Bd (Hpk k r) 1 := by
  intro i j
  unfold Hpk
  split_ifs <;> simp

theorem Bd.inv {g : Mat k r} (hg : g ∈ GG k r) {R : ℝ} (h : Bd g R) :
    Bd g⁻¹ (((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * R) := by
  rw [← GlobalTheory.BesselPeriodCompare.uinv_eq hg]
  have h1 : Bd gᴴ R := fun i j => by simpa [Matrix.conjTranspose_apply] using h j i
  have := (bd_Hpk.mul h1).mul bd_Hpk
  exact fun i j => (this i j).trans (le_of_eq (by ring))

theorem bd_pow {g : Mat k r} {n : ℕ} (hg : (g - 1) ^ n = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ, Bd (g ^ m) (B * ((m : ℝ) + 1) ^ (n + 1)) := by
  set X := g - 1 with hX
  have e : g = X + 1 := by simp [hX]
  refine ⟨∑ l ∈ Finset.range n, ∑ i, ∑ j, ‖(X ^ l) i j‖, by positivity, fun m i j => ?_⟩
  set B := ∑ l ∈ Finset.range n, ∑ i, ∑ j, ‖(X ^ l) i j‖ with hB
  have hB0 : 0 ≤ B := by positivity
  rw [e, (Commute.one_right X).add_pow, Matrix.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ Finset.range (m + 1), ‖(X ^ l * 1 ^ (m - l) * (m.choose l : Mat k r)) i j‖ ≤
      B * ((m : ℝ) + 1) ^ n := fun l _ => by
    by_cases hl : l < n
    · have h1 : ‖(X ^ l) i j‖ ≤ B :=
        ((Finset.single_le_sum (f := fun j => ‖(X ^ l) i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i => ∑ j, ‖(X ^ l) i j‖) (fun _ _ => by positivity)
            (Finset.mem_univ i))).trans
          (Finset.single_le_sum (f := fun l => ∑ i, ∑ j, ‖(X ^ l) i j‖) (fun _ _ => by positivity)
            (Finset.mem_range.2 hl))
      have h2 : (m.choose l : ℝ) ≤ ((m : ℝ) + 1) ^ n := by
        have h3 : (m.choose l : ℝ) ≤ (m : ℝ) ^ l := by exact_mod_cast Nat.choose_le_pow m l
        have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        exact h3.trans ((pow_le_pow_left₀ h4 (by linarith) l).trans (pow_le_pow_right₀ (by linarith) hl.le))
      rw [one_pow, mul_one, ← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul, norm_mul, Complex.norm_natCast,
        mul_comm]
      exact mul_le_mul h1 h2 (Nat.cast_nonneg _) hB0
    · rw [pow_eq_zero_of_le (not_lt.1 hl) hg]
      simp only [zero_mul, Matrix.zero_apply, norm_zero]
      positivity
  refine (Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)
  simp only [Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem finite_compact {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ)
    {K : Set (Mt k r)} (hK : IsCompact K) : μ K < ⊤ := by
  have h := (GlobalTheory.BesselPeriodCompare.isHaarOn_iff hS.isClosedSubgroup μ).1 hμ
  have hle : μ K ≤ μ (K ∩ {x | Matrix.of x ∈ S}) := by
    refine measure_mono_ae ?_
    have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S := by rw [ae_iff]; exact hμ.2.2.1
    filter_upwards [hae] with x hx hK using ⟨hK, hx⟩
  exact lt_of_le_of_lt hle (h.2.2.1 _ (hK.inter_right hS.2.1) fun x hx => hx.2)

theorem cont_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem small_ball {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (h : ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 * R * (2 * δ) ≤ 1) (x : Mt k r) :
    μ (closedBall 0 R ∩ closedBall x δ) ≤ μ (closedBall (Matrix.of.symm (1 : Mat k r) : Mt k r) 1) := by
  by_cases hex : ∃ s ∈ closedBall (0 : Mt k r) R ∩ closedBall x δ, Matrix.of s ∈ S
  · obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := hex
    have hi := hS.2.2.2.2 _ hs
    conv_rhs => rw [← hμ.2.2.2 _ hi]
    rw [Measure.map_apply (cont_lmul _).measurable measurableSet_closedBall]
    refine measure_mono fun t ht => ?_
    have h1 : t ∈ closedBall s (2 * δ) := by
      have := dist_triangle_right t s x
      have h2 := mem_closedBall.1 ht.2
      have h3 := mem_closedBall.1 hs2
      rw [mem_closedBall]; linarith
    have h2 := (((mem_closedBall_zero_iff_matrixEntriesBoundedBy hR).1 hs1).inv (hS.1 hs)).mul ((bd_iff (by linarith)).1 h1)
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG (hS.1 hs))] at h2
    have h3 : Bd ((Matrix.of s : Mat k r)⁻¹ * Matrix.of t - 1) 1 :=
      fun i j => (h2 i j).trans (le_trans (le_of_eq (by ring)) h)
    rw [Set.mem_preimage, bd_iff zero_le_one]
    exact h3
  · refine le_trans (le_of_eq ?_) zero_le
    refine measure_mono_null (fun s hs => ?_) hμ.2.2.1
    exact fun h' => hex ⟨s, hs, h'⟩

theorem growth {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ) :
    ∃ (C : ℝ) (D : ℕ), 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → (μ (closedBall 0 R)).toReal ≤ C * R ^ D := by
  have := hμ.1
  set M := μ (closedBall (Matrix.of.symm (1 : Mat k r) : Mt k r) 1) with hM
  have hMf : M ≠ ⊤ := (finite_compact hS hμ (isCompact_closedBall _ _)).ne
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast Nat.le_add_left 1 _
  set d := Module.finrank ℝ (Mt k r)
  let lam : Measure (Mt k r) := Measure.addHaar
  refine ⟨M.toReal * (4 * n ^ 3) ^ d, 2 * d, by positivity, fun R hR => ?_⟩
  set δ := (2 * n ^ 3 * R)⁻¹ with hδ
  have hp : 1 ≤ 2 * n ^ 3 * R := by
    have := one_le_pow₀ (n := 3) hn1
    nlinarith
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ hp
  let W : Set (Mt k r × Mt k r) := {p | p.1 ∈ closedBall 0 R ∧ dist p.1 p.2 ≤ δ}
  have hW : MeasurableSet W :=
    ((isClosed_closedBall.preimage continuous_fst).inter (isClosed_le continuous_dist continuous_const)).measurableSet
  have e1 : (μ.prod lam) W = lam (closedBall 0 δ) * μ (closedBall 0 R) := by
    rw [Measure.prod_apply hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ closedBall (0 : Mt k r) R
    · rw [Set.indicator_of_mem hs, ← Measure.addHaar_closedBall_center lam s]
      congr 1
      ext x
      exact ⟨fun h => mem_closedBall'.2 h.2, fun h => ⟨hs, mem_closedBall'.1 h⟩⟩
    · rw [Set.indicator_of_notMem hs]
      have : Prod.mk s ⁻¹' W = ∅ := by
        ext x
        simp only [W, Set.mem_preimage, Set.mem_ofPred_eq, hs, false_and, Set.mem_empty_iff_false]
      rw [this, measure_empty]
  have e2 : (μ.prod lam) W ≤ M * lam (closedBall 0 (2 * R)) := by
    rw [Measure.prod_apply_symm hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall (0 : Mt k r) (2 * R)
    · rw [Set.indicator_of_mem hx]
      refine small_ball hS hμ (by linarith) hδ0.le (le_of_eq ?_) x
      rw [← hn, hδ]
      field_simp
    · have : (fun s => (s, x)) ⁻¹' W = ∅ := by
        ext s
        simp only [W, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, mem_closedBall]
        rintro ⟨h1, h2⟩
        apply hx
        have := dist_triangle_left x 0 s
        rw [mem_closedBall]; linarith
      simp [this]
  rw [e1, Measure.addHaar_closedBall lam _ hδ0.le, Measure.addHaar_closedBall lam _ (by linarith)] at e2
  have hb0 : 0 < (lam (ball 0 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos lam _ one_pos).ne' measure_ball_lt_top.ne
  have e3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hMf
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)) e2
  simp only [ENNReal.toReal_mul] at e3
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at e3
  have e4 : δ ^ d * (μ (closedBall 0 R)).toReal ≤ M.toReal * (2 * R) ^ d := by
    refine le_of_mul_le_mul_right ?_ hb0
    calc _ = δ ^ d * (lam (ball 0 1)).toReal * (μ (closedBall 0 R)).toReal := by ring
      _ ≤ _ := e3
      _ = _ := by ring
  have e5 : M.toReal * (2 * R) ^ d = δ ^ d * (M.toReal * (4 * n ^ 3) ^ d * R ^ (2 * d)) := by
    have : 2 * R = δ * (4 * n ^ 3) * R ^ 2 := by rw [hδ]; field_simp; ring
    rw [this, mul_pow, mul_pow, pow_mul]; ring
  rw [e5] at e4
  exact le_of_mul_le_mul_left e4 (by positivity)

theorem rmul_rmul (a b : Mat k r) (μ : Measure (Mt k r)) :
    (μ.map (rmulM a)).map (rmulM b) = μ.map (rmulM (a * b)) := by
  rw [Measure.map_map (continuous_rmulM _).measurable (continuous_rmulM _).measurable]
  congr 1
  funext x
  exact Matrix.mul_assoc (Matrix.of x) a b

theorem rmul_one (μ : Measure (Mt k r)) : μ.map (rmulM (1 : Mat k r)) = μ := by
  have : (rmulM (1 : Mat k r) : Mt k r → Mt k r) = id := by
    funext x
    exact Matrix.mul_one (Matrix.of x)
  rw [this, Measure.map_id]

theorem haar_rmul {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ)
    {g : Mat k r} (hg : g ∈ S) : IsHaarOn S (μ.map (rmulM g)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hμ
  have hu := isUnit_det_of_mem_GG (hS.1 hg)
  have hm := (continuous_rmulM (k := k) (r := r) g).measurable
  refine ⟨?_, ?_, ?_, fun s hs => ?_⟩
  · refine SigmaFinite.of_map _ (continuous_rmulM g⁻¹).measurable.aemeasurable ?_
    rwa [rmul_rmul, Matrix.mul_nonsing_inv _ hu, rmul_one]
  · exact fun h0 => h2 ((Measure.map_eq_zero_iff hm.aemeasurable).1 h0)
  · have hc : IsClosed {x : Mt k r | Matrix.of x ∈ S} := hS.2.1
    rw [← ae_iff]
    refine (ae_map_iff hm.aemeasurable hc.measurableSet).2 ?_
    have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S := by rw [ae_iff]; exact h3
    filter_upwards [hae] with x hx using hS.2.2.2.1 _ hx _ hg
  · conv_rhs => rw [← h4 s hs]
    rw [Measure.map_map (cont_lmul _).measurable hm, Measure.map_map hm (cont_lmul _).measurable]
    congr 1
    funext x
    exact (Matrix.mul_assoc s (Matrix.of x) g).symm

theorem modulus_le_one {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ)
    {g h : Mat k r} (hgh : g * h = 1) {n : ℕ} (hh : (h - 1) ^ n = 0) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (e : μ.map (rmulM g) = c • μ) : c ≤ 1 := by
  obtain ⟨C, D, hC, hgr⟩ := growth hS hμ
  obtain ⟨B, hB, hpow⟩ := bd_pow hh
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, μ (closedBall 0 ρ) ≠ 0 := by
    by_contra! h0
    apply hμ.2.1
    rw [← Measure.measure_univ_eq_zero, ← iUnion_closedBall_nat (0 : Mt k r)]
    exact measure_iUnion_null h0
  have hv : 0 < (μ (closedBall 0 ρ)).toReal :=
    ENNReal.toReal_pos hρ (finite_compact hS hμ (isCompact_closedBall _ _)).ne
  have em : ∀ m : ℕ, μ.map (rmulM (g ^ m)) = c ^ m • μ := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, one_smul, rmul_one]
    | succ m ih => rw [pow_succ, ← rmul_rmul, ih, Measure.map_smul, e, smul_smul, pow_succ]
  have hgm : ∀ m : ℕ, g ^ m * h ^ m = 1 := fun m => by
    have hcm : Commute g h := by
      unfold Commute SemiconjBy
      rw [hgh, mul_eq_one_comm.1 hgh]
    rw [← hcm.mul_pow, hgh, one_pow]
  set K : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) * (ρ * B) + 1 with hK
  have hK0 : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (ρ * B) := by positivity
  have key : ∀ m : ℕ, c.toReal ^ m * (μ (closedBall 0 ρ)).toReal ≤
      C * K ^ D * ((m : ℝ) + 1) ^ ((n + 1) * D) := by
    intro m
    have hm1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ (n + 1) := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have h1 : (c ^ m • μ) (closedBall 0 ρ) ≤ μ (closedBall 0 (K * ((m : ℝ) + 1) ^ (n + 1))) := by
      rw [← em, Measure.map_apply (continuous_rmulM _).measurable measurableSet_closedBall]
      refine measure_mono fun x hx => ?_
      have h2 := ((mem_closedBall_zero_iff_matrixEntriesBoundedBy (Nat.cast_nonneg ρ)).1 hx).mul (hpow m)
      rw [of_rmulM, Matrix.mul_assoc, hgm, Matrix.mul_one] at h2
      refine (mem_closedBall_zero_iff_matrixEntriesBoundedBy (by positivity)).2 fun i j => (h2 i j).trans ?_
      rw [hK]
      nlinarith
    have h2 := (ENNReal.toReal_mono (finite_compact hS hμ (isCompact_closedBall _ _)).ne h1).trans
      (hgr _ (by rw [hK]; nlinarith))
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, mul_pow, ← pow_mul,
      ← mul_assoc] at h2
    exact h2
  by_contra! h1
  have h2 : 1 < c.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hc).2 h1
  have h3 := ((tendsto_pow_const_div_const_pow_of_one_lt ((n + 1) * D) h2).comp
    (Filter.tendsto_add_atTop_nat 1)).const_mul (C * K ^ D * c.toReal)
  rw [mul_zero] at h3
  obtain ⟨m, hm⟩ := (h3.eventually (gt_mem_nhds hv)).exists
  have h4 := key m
  have h5 : 0 < c.toReal ^ m := by positivity
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hm
  have h6 : C * K ^ D * c.toReal * (((m : ℝ) + 1) ^ ((n + 1) * D) / c.toReal ^ (m + 1)) =
      C * K ^ D * ((m : ℝ) + 1) ^ ((n + 1) * D) / c.toReal ^ m := by
    field_simp
    ring
  rw [h6, div_lt_iff₀ h5] at hm
  linarith

theorem isUnimod_of_subset_Nset {S : Set (Mat k r)} (hS : IsClosedSub k r S) (hN : S ⊆ Nset k r)
    {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ) : IsUnimod S μ := by
  have one : ∀ g ∈ S, ∃ c : ℝ≥0∞, c ≤ 1 ∧ μ.map (rmulM g) = c • μ := fun g hg => by
    obtain ⟨c, -, c1, e⟩ := GlobalTheory.BesselPeriodCompare.haar_unique hS.isClosedSubgroup (haar_rmul hS hμ hg) hμ
    exact ⟨c, modulus_le_one hS hμ (Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_GG (hS.1 hg)))
      (Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_unip (hN (hS.2.2.2.2 _ hg))) c1 e, e⟩
  have right : ∀ g ∈ S, μ.map (rmulM g) = μ := fun g hg => by
    obtain ⟨c, c1, e⟩ := one g hg
    obtain ⟨c', c1', e'⟩ := one _ (hS.2.2.2.2 _ hg)
    have h := rmul_rmul g g⁻¹ μ
    rw [Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_GG (hS.1 hg)), rmul_one, e, Measure.map_smul, e'] at h
    rw [e]
    ext t -
    have h1 := congrArg (fun m : Measure (Mt k r) => m t) h
    simp only [Measure.smul_apply, smul_eq_mul] at h1 ⊢
    refine le_antisymm ((mul_le_mul_left c1 _).trans (one_mul _).le) ?_
    calc μ t = c * (c' * μ t) := h1.symm
      _ ≤ c * (1 * μ t) := by gcongr
      _ = c * μ t := by rw [one_mul]
  refine (haar_unimod_of_biinv hS (μ := μ)
    { ne_zero := hμ.2.1, conc := hμ.2.2.1, left := hμ.2.2.2, right := right,
      finite_compact := fun K hK => finite_compact hS hμ hK }).2

theorem isClosedSub_Rset {γ : Mat k r} (hγ : γ ∈ GG k r) : IsClosedSub k r (Rset k r γ) := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  have hu := isUnit_det_of_mem_GG hγ
  refine ⟨fun x hx => n1 hx.1, ?_, ⟨n3, ?_⟩, fun a ha b hb => ⟨n4 _ ha.1 _ hb.1, ?_⟩, fun a ha => ⟨n5 _ ha.1, ?_⟩⟩
  · have hc : Continuous fun x : Mat k r => γ * x * γ⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := n2.inter (n2.preimage hc)
    exact this
  · rwa [Matrix.mul_one, Matrix.mul_nonsing_inv _ hu]
  · convert n4 _ ha.2 _ hb.2 using 1
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  · convert n5 _ ha.2 using 1
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc]

theorem rset_unimodular : ∀ (k r : ℕ) (γ : Mat k r), γ ∈ GG k r → IsClosedSub k r (Rset k r γ) ∧
    ∀ μ, IsHaarOn (Rset k r γ) μ → IsUnimod (Rset k r γ) μ :=
  fun _ _ _ hγ => ⟨isClosedSub_Rset hγ, fun _ hμ =>
    isUnimod_of_subset_Nset (isClosedSub_Rset hγ) (fun _ h => h.1) hμ⟩

end GlobalTheory.UnipUnimod
