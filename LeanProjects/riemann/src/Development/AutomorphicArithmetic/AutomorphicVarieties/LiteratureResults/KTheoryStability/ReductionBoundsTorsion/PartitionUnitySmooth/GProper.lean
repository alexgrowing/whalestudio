import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem qR_smul_VR {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) (c : ℝ)
    (z : VR L N) : qR h (c • z) = c ^ 2 * qR h z := by
  show ∑ w, (star ((c • z) w) ⬝ᵥ mat h w *ᵥ (c • z) w).re =
    c ^ 2 * ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (c • z) w = (c : ℂ) • z w := by
    ext i; simp [Complex.real_smul]
  rw [e, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp [smul_eq_mul, Complex.conj_ofReal]
  ring

private theorem qR_pos_of_mem_Pos_of_VR_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) (z : VR L N) (hz : z ≠ 0) : 0 < qR h z := by
  obtain ⟨w0, hw0⟩ : ∃ w, z w ≠ 0 := by
    by_contra hc; push_neg at hc; exact hz (funext hc)
  show 0 < ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re
  have hnn : ∀ w, 0 ≤ (star (z w) ⬝ᵥ mat h w *ᵥ z w).re := fun w => by
    have := (hp w).posSemidef.dotProduct_mulVec_nonneg (z w)
    exact (Complex.nonneg_iff.mp this).1
  have hpos : 0 < (star (z w0) ⬝ᵥ mat h w0 *ᵥ z w0).re := (hp w0).re_dotProduct_pos hw0
  exact Finset.sum_pos' (fun w _ => hnn w) ⟨w0, Finset.mem_univ _, hpos⟩

private theorem continuous_qR_comp {L : Type} [Field L] [NumberField L] {N : ℕ} {X : Type*}
    [TopologicalSpace X] {f : X → HS L N} {g : X → VR L N} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => qR (f x) (g x) := by
  show Continuous fun x => ∑ w, (star (g x w) ⬝ᵥ mat (f x) w *ᵥ g x w).re
  refine continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_
  have h1 : Continuous fun x => g x w := (continuous_apply w).comp hg
  have h2 : Continuous fun x => mat (f x) w :=
    (continuous_apply w).comp (continuous_subtype_val.comp hf)
  exact h1.star.dotProduct (h2.matrix_mulVec h1)

private theorem qR_zero_right {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) :
    qR h 0 = 0 := by
  simpa using qR_smul_VR h 0 0

private theorem exists_pos_smul_unit_sphere_eq_of_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ} (z : VR L N)
    (hz : z ≠ 0) : ∃ r : ℝ, 0 < r ∧ ∃ u ∈ Metric.sphere (0 : VR L N) 1, z = r • u := by
  refine ⟨‖z‖, norm_pos_iff.mpr hz, ‖z‖⁻¹ • z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

private theorem ne_zero_of_mem_unit_sphere_VR {L : Type} [Field L] [NumberField L] {N : ℕ}
    (u : VR L N) (hu : u ∈ Metric.sphere (0 : VR L N) 1) : u ≠ 0 := by
  rintro rfl
  simp at hu

private theorem exists_qR_le_mul_qR_on_compact_subset_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (K : Set (HS L N))
    (hK : IsCompact K) (hKP : K ⊆ Pos L N) (h0 : HS L N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ K, ∀ z, qR h0 z ≤ C * qR h z := by
  have hS : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have hc : ContinuousOn (fun p : HS L N × VR L N => qR h0 p.2 / qR p.1 p.2)
      (K ×ˢ Metric.sphere (0 : VR L N) 1) := by
    refine ContinuousOn.div ?_ (continuous_qR_comp continuous_fst continuous_snd).continuousOn ?_
    · exact (continuous_qR_comp continuous_const continuous_snd).continuousOn
    · rintro ⟨h, z⟩ ⟨hh, hz⟩
      exact (qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) z (ne_zero_of_mem_unit_sphere_VR z hz)).ne'
  obtain ⟨C, hC⟩ := (hK.prod hS).bddAbove_image hc
  refine ⟨max C 0, le_max_right _ _, fun h hh z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp [qR_zero_right]
  obtain ⟨r, -, u, hu, rfl⟩ := exists_pos_smul_unit_sphere_eq_of_ne_zero z hz
  have hpu : 0 < qR h u := qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) u (ne_zero_of_mem_unit_sphere_VR u hu)
  have hb : qR h0 u / qR h u ≤ C := hC ⟨(h, u), ⟨hh, hu⟩, rfl⟩
  have h1 : qR h0 u ≤ max C 0 * qR h u := by
    rw [div_le_iff₀ hpu] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpu.le)
  rw [qR_smul_VR, qR_smul_VR]
  calc r ^ 2 * qR h0 u ≤ r ^ 2 * (max C 0 * qR h u) := mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    _ = max C 0 * (r ^ 2 * qR h u) := by ring

private theorem eventually_nhds_unit_sphere_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) :
    ∀ᶠ k in nhds h, ∀ u ∈ Metric.sphere (0 : VR L N) 1,
      |qR k u - qR h u| - 1 / 2 * qR h u < 0 := by
  have hS : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have c1 : Continuous fun p : HS L N × VR L N => qR p.1 p.2 :=
    continuous_qR_comp continuous_fst continuous_snd
  have c2 : Continuous fun p : HS L N × VR L N => qR h p.2 :=
    continuous_qR_comp continuous_const continuous_snd
  refine hS.eventually_forall_of_forall_eventually fun u hu => ?_
  have hpu : 0 < qR h u := qR_pos_of_mem_Pos_of_VR_ne_zero h hp u (ne_zero_of_mem_unit_sphere_VR u hu)
  set f : HS L N × VR L N → ℝ := fun p => |qR p.1 p.2 - qR h p.2| - 1 / 2 * qR h p.2 with hf
  have hcont : Continuous f :=
    ((c1.sub c2).abs).sub (continuous_const.mul c2)
  have hv : f (h, u) < 0 := by
    show |qR h u - qR h u| - 1 / 2 * qR h u < 0
    rw [sub_self, abs_zero, zero_sub, neg_lt_zero]
    linarith
  have h2 : ∀ᶠ p in nhds (h, u), f p < 0 := hcont.continuousAt.eventually (Iio_mem_nhds hv)
  filter_upwards [h2] with p hp'
  exact hp'

private theorem eventually_nhds_abs_qR_sub_le_half_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) :
    ∀ᶠ k in nhds h, ∀ z : VR L N, |qR k z - qR h z| ≤ 1 / 2 * qR h z := by
  filter_upwards [eventually_nhds_unit_sphere_of_mem_Pos h hp] with k hk z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [qR_zero_right, qR_zero_right]
    norm_num
  obtain ⟨r, -, u, hu, rfl⟩ := exists_pos_smul_unit_sphere_eq_of_ne_zero z hz
  rw [qR_smul_VR, qR_smul_VR, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r)]
  have h1 : |qR k u - qR h u| ≤ 1 / 2 * qR h u := by linarith [hk u hu]
  calc r ^ 2 * |qR k u - qR h u| ≤ r ^ 2 * (1 / 2 * qR h u) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    _ = 1 / 2 * (r ^ 2 * qR h u) := by ring

theorem pf_GProper : GProper := by
  intro hB L _ _ N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨?_, ?_⟩
    · have hu : Pos L 0 = Set.univ := by
        ext h
        simp only [Set.mem_univ, iff_true]
        intro w
        refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => absurd (Subsingleton.elim x 0) hx
        exact h.2 w
      rw [hu]
      exact isOpen_univ
    · intro K _ _
      apply Set.Subsingleton.finite
      intro a _ b _
      exact Units.ext (Subsingleton.elim _ _)
  obtain ⟨hPos, hEq, -, hCl, -, -⟩ := hB L N hN
  refine ⟨?_, ?_⟩
  · refine isOpen_iff_mem_nhds.mpr fun h hh => ?_
    filter_upwards [eventually_nhds_abs_qR_sub_le_half_of_mem_Pos h hh] with k hk
    exact (hCl (1 / 2) (by norm_num) le_rfl h hh k hk).1
  intro K hK hKP
  rcases K.eq_empty_or_nonempty with rfl | ⟨h0, hh0⟩
  · simp
  obtain ⟨C, hC0, hC⟩ := exists_qR_le_mul_qR_on_compact_subset_Pos K hK hKP h0
  have hbd : ∀ i : Fin N, ∃ B : ℝ, ∀ h ∈ K, q h (Pi.single i 1 : UpperTheory.V.KT.Lat L N) ≤ B := by
    intro i
    have hc : Continuous fun h : HS L N => qR h (toR (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) :=
      continuous_qR_comp continuous_id continuous_const
    obtain ⟨B, hB'⟩ := hK.bddAbove_image hc.continuousOn
    exact ⟨B, fun h hh => hB' ⟨h, hh, rfl⟩⟩
  choose B hBd using hbd
  have hF : (⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i}).Finite :=
    Set.finite_iUnion fun i => (hPos h0 (hKP hh0)).2.2.2.2 _
  have hmaps : ∀ γ ∈ {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K},
      (fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ∈
        Set.pi Set.univ (fun _ => ⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i}) := by
    rintro γ ⟨h, hh, hγ⟩ i -
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    show q h0 (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ≤ C * B i
    calc q h0 (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N))
        ≤ C * q h (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) := hC h hh _
      _ = C * q (ac γ h) (Pi.single i 1 : UpperTheory.V.KT.Lat L N) := by rw [hEq]
      _ ≤ C * B i := mul_le_mul_of_nonneg_left (hBd i _ hγ) hC0
  have hinj : Set.InjOn (fun γ : Gm L N => fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N))
      {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K} := by
    intro a _ b _ hab
    have hinv : (a⁻¹ : Gm L N) = b⁻¹ := by
      apply Units.ext
      ext j i
      have e := congrFun (congrFun hab i) j
      change ((↑(a⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j =
        ((↑(b⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j at e
      simpa [Matrix.mulVec_single_one] using e
    exact inv_injective hinv
  exact Set.Finite.of_finite_image ((Set.Finite.pi fun _ => hF).subset (Set.image_subset_iff.mpr hmaps)) hinj

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
