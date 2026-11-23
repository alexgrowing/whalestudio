import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LcvBasis
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules

noncomputable section

namespace GlobalTheory.LatDetDeg

open NumberField IsDedekindDomain Module Formalism.BasicNotions GlobalTheory.FlatLine
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem locP_eq_of_locBasis {𝔓 : HeightOneSpectrum (𝓞 K)} {L : Submodule (𝓞 K) (Fin n → K)} {m : ℕ}
    {b : Fin m → Fin n → K} (hb : GlobalTheory.PtDeg.LocBasis 𝔓 L b) :
    Formalism.HermitianLatticesTheory.localization₂ 𝔓.asIdeal L = Formalism.HermitianLatticesTheory.localization₂ 𝔓.asIdeal (Submodule.span (𝓞 K) (Set.range b)) := by
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨d, hd, hdx⟩ := hb.2.2 _ hx
    exact ⟨d * s, fun h ↦ (𝔓.isPrime.mem_or_mem h).elim hd hs, by rw [mul_smul]; exact hdx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb.1 i) hx⟩

theorem det_ne_zero_of_comb {m : ℕ} {u b : Fin m → Fin n → K} (hu : LinearIndependent K u)
    {M : Matrix (Fin m) (Fin m) K} (hM : ∀ i, u i = ∑ j, M i j • b j) : M.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  apply hv
  have h1 : ∑ i, v i • u i = 0 := by
    simp only [hM, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [← Finset.sum_smul]
    have := congrFun hvM j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    rw [this, zero_smul]
  exact funext fun i ↦ Fintype.linearIndependent_iff.1 hu v h1 i

theorem index_formula {L : Submodule (𝓞 K) (Fin n → K)} (hL : L.FG) {m : ℕ} {w : Fin m → Fin n → K}
    (hw : ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K L w) (B : HeightOneSpectrum (𝓞 K) → Fin m → Fin n → K)
    (Mx : HeightOneSpectrum (𝓞 K) → Matrix (Fin m) (Fin m) K) (hB : ∀ 𝔓, GlobalTheory.PtDeg.LocBasis 𝔓 L (B 𝔓))
    (hM : ∀ 𝔓 i, w i = ∑ j, Mx 𝔓 i j • B 𝔓 j) :
    (Function.support fun 𝔓 ↦ (vAdd 𝔓 (Mx 𝔓).det : ℝ)).Finite ∧
      ∑ᶠ 𝔓, (vAdd 𝔓 (Mx 𝔓).det : ℝ) * lw K 𝔓 =
        Real.log ((Submodule.span (𝓞 K) (Set.range w)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) /
          finrank ℚ K := by
  classical
  have hle : Submodule.span (𝓞 K) (Set.range w) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hw.1 i)
  have hloc : ∀ 𝔓 : HeightOneSpectrum (𝓞 K),
      (vAdd 𝔓 (Mx 𝔓).det : ℝ) = (Formalism.HermitianLatticesTheory.locLen 𝔓.asIdeal L (Submodule.span (𝓞 K) (Set.range w)) : ℝ) := by
    intro 𝔓
    have hfam : Formalism.BasicNotions.SkeletonIndexLemmas.famOf (B 𝔓) (Mx 𝔓).transpose = w := by
      funext i
      simp only [Formalism.BasicNotions.SkeletonIndexLemmas.famOf, Matrix.transpose_apply]
      exact (hM 𝔓 i).symm
    have hdet : (Mx 𝔓).transpose.det ≠ 0 := by
      rw [Matrix.det_transpose]; exact det_ne_zero_of_comb hw.2.1 (hM 𝔓)
    have h1 := Formalism.BasicNotions.SkeletonIndexLemmas.lidx_latOf 𝔓 (B 𝔓) (hB 𝔓).2.1 _ hdet
    rw [hfam, Matrix.det_transpose] at h1
    have h2 : Formalism.HermitianLatticesTheory.lidx 𝔓.asIdeal L (Submodule.span (𝓞 K) (Set.range w)) =
        Formalism.HermitianLatticesTheory.lidx 𝔓.asIdeal (Formalism.BasicNotions.SkeletonIndexLemmas.latOf (B 𝔓)) (Formalism.BasicNotions.SkeletonIndexLemmas.latOf w) :=
      Formalism.BasicNotions.SkeletonIndexLemmas.lidx_congr 𝔓 (locP_eq_of_locBasis (hB 𝔓)) rfl
    rw [Formalism.EigenvalueLevelCeiling.idxRules_lidx_of_le _ hle, h1] at h2
    rw [← h2]; push_cast; rfl
  have hn := ReciprocityTheory.GeometryOfNumbersTheory.IsFrame.relIndex_ne_zero hL hw
  obtain ⟨-, hfin, hlog⟩ := Formalism.DivisionValues.LocalCovolumeBasis.key L _ _ hle rfl hn
  have hs : (Function.support fun 𝔓 ↦ (vAdd 𝔓 (Mx 𝔓).det : ℝ)).Finite := by
    refine hfin.subset fun 𝔓 h ↦ ?_
    rw [Function.mem_support, hloc] at h
    rw [Function.mem_support]; exact_mod_cast h
  refine ⟨hs, ?_⟩
  rw [hlog, div_eq_mul_inv, finsum_mul]
  refine finsum_congr fun 𝔓 ↦ ?_
  rw [hloc, lw]; ring

theorem exists_locBasis_comb {L : Submodule (𝓞 K) (Fin n → K)} (hL : L.FG) {m : ℕ} {u : Fin m → Fin n → K}
    (hu : LinearIndependent K u) (hsp : Submodule.span K (Set.range u) = Submodule.span K (L : Set (Fin n → K)))
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    ∃ (b : Fin m → Fin n → K) (M : Matrix (Fin m) (Fin m) K), GlobalTheory.PtDeg.LocBasis 𝔓 L b ∧
      ∀ i, u i = ∑ j, M i j • b j := by
  classical
  obtain ⟨a, ha, hloc⟩ := Formalism.BasicNotions.SkeletonIndexLemmas.exists_fam_locP 𝔓 hL
  have hr : finrank K (Submodule.span K (L : Set (Fin n → K))) = m := by
    rw [← hsp, finrank_span_eq_card hu, Fintype.card_fin]
  have hmem : ∀ i, ∃ s : 𝓞 K, s ∉ 𝔓.asIdeal ∧ s • a i ∈ L := by
    intro i
    have : a i ∈ Formalism.HermitianLatticesTheory.localization₂ 𝔓.asIdeal (Formalism.BasicNotions.SkeletonIndexLemmas.latOf a) :=
      ⟨1, fun h ↦ 𝔓.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
        rw [one_smul]; exact Submodule.subset_span ⟨i, rfl⟩⟩
    rw [hloc] at this
    exact this
  choose s hs hsa using hmem
  set t : 𝓞 K := ∏ i, s i with ht
  have htP : t ∉ 𝔓.asIdeal := by
    rw [ht]
    intro h
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := 𝔓.isPrime)).1 h
    exact hs i hi
  have ht0 : (t : K) ≠ 0 := by
    intro h
    have : t = 0 := by exact_mod_cast h
    exact htP (this ▸ 𝔓.asIdeal.zero_mem)
  have hta : ∀ i, t • a i ∈ L := by
    intro i
    rw [ht, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, mul_smul]
    exact L.smul_mem _ (hsa i)
  let b : Fin m → Fin n → K := fun j ↦ t • a (Fin.cast hr.symm j)
  have hbL : ∀ j, b j ∈ L := fun j ↦ hta _
  have hbsmul : ∀ j, b j = (t : K) • a (Fin.cast hr.symm j) := fun j ↦ (algebraMap_smul K t _).symm
  have hbli : LinearIndependent K b := by
    have h1 : LinearIndependent K (fun i ↦ (t : K) • a i) :=
      ha.units_smul (fun _ ↦ Units.mk0 (t : K) ht0)
    have h2 := h1.comp (Fin.cast hr.symm) (Fin.cast_injective _)
    convert h2 using 1
    funext j; exact hbsmul j
  have hrange : Set.range b = Set.range fun i ↦ t • a i := by
    ext x; constructor
    · rintro ⟨j, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨Fin.cast hr i, by simp [b]⟩
  have hloc' : ∀ x ∈ L, ∃ d : 𝓞 K, d ∉ 𝔓.asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro x hx
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ 𝔓.asIdeal L := ⟨1, fun h ↦ 𝔓.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h),
      by rw [one_smul]; exact hx⟩
    rw [← hloc] at hx'
    obtain ⟨r, hr0, hrx⟩ := hx'
    refine ⟨t * r, fun h ↦ (𝔓.isPrime.mem_or_mem h).elim htP hr0, ?_⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hrx
    rw [mul_smul, ← hc, Finset.smul_sum, hrange]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspb : Submodule.span K (Set.range b) = Submodule.span K (L : Set (Fin n → K)) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span (hbL j))
    · rw [finrank_span_eq_card hbli, Fintype.card_fin, hr]
  have hcomb : ∀ i, ∃ c : Fin m → K, ∑ j, c j • b j = u i := by
    intro i
    have : u i ∈ Submodule.span K (Set.range b) := by
      rw [hspb, ← hsp]; exact Submodule.subset_span ⟨i, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose c hc using hcomb
  exact ⟨b, Matrix.of fun i j ↦ c i j, ⟨hbL, hbli, hloc'⟩, fun i ↦ by simpa using (hc i).symm⟩

theorem exists_smul_mem {L : Submodule (𝓞 K) (Fin n → K)} {m : ℕ} {u : Fin m → Fin n → K}
    (hu : ∀ i, u i ∈ Submodule.span K (L : Set (Fin n → K))) : ∃ t : 𝓞 K, t ≠ 0 ∧ ∀ i, t • u i ∈ L := by
  classical
  have h1 : ∀ i, ∃ s : 𝓞 K, s ≠ 0 ∧ s • u i ∈ L := by
    intro i
    obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (𝓞 K)⁰ K (L : Set (Fin n → K)) (u i) (hu i)
    rw [Submodule.span_eq] at hs
    exact ⟨s, nonZeroDivisors.ne_zero s.2, hs⟩
  choose s hs hsu using h1
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.2 fun i _ ↦ hs i, fun i ↦ ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, mul_smul]
  exact L.smul_mem _ (hsu i)

theorem vAdd_mul' (𝔓 : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd 𝔓 (x * y) = vAdd 𝔓 x + vAdd 𝔓 y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem vAdd_pow' (𝔓 : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) (k : ℕ) :
    vAdd 𝔓 (x ^ k) = k * vAdd 𝔓 x := by
  induction k with
  | zero => simp [vAdd]
  | succ k ih =>
    rw [pow_succ, vAdd_mul' 𝔓 (pow_ne_zero _ hx) hx, ih]
    push_cast; ring

theorem form_smul_left (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (σ : K →+* ℂ) (c : K) (x y : Fin n → K) :
    h.form σ (c • x) y = starRingEnd ℂ (σ c) * h.form σ x y := by
  rw [← h.conj_symm σ y (c • x), h.smul_right, map_mul, h.conj_symm]

theorem det_gram_smul (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (σ : K →+* ℂ) (c : K) {m : ℕ}
    (u : Fin m → Fin n → K) :
    (h.gram σ fun i ↦ c • u i).det.re = (‖σ c‖ ^ 2) ^ m * (h.gram σ u).det.re := by
  have e : (h.gram σ fun i ↦ c • u i) = ((‖σ c‖ ^ 2 : ℝ) : ℂ) • h.gram σ u := by
    ext i j
    simp only [ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, form_smul_left,
      h.smul_right]
    rw [← mul_assoc, Complex.mul_conj']
    push_cast; ring
  rw [e, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem det_gram_re_pos (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (σ : K →+* ℂ) {m : ℕ}
    {u : Fin m → Fin n → K} (hu : LinearIndependent K u) : 0 < (h.gram σ u).det.re := by
  have := (h.posDef σ m u hu).det_pos
  exact (Complex.pos_iff.1 this).1

theorem lineDeg_frame (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) {L : Submodule (𝓞 K) (Fin n → K)} (hL : L.FG)
    {m : ℕ} {u : Fin m → Fin n → K} (hu : LinearIndependent K u)
    (hsp : Submodule.span K (Set.range u) = Submodule.span K (L : Set (Fin n → K)))
    (B : HeightOneSpectrum (𝓞 K) → Fin m → Fin n → K) (Mx : HeightOneSpectrum (𝓞 K) → Matrix (Fin m) (Fin m) K)
    (hB : ∀ 𝔓, GlobalTheory.PtDeg.LocBasis 𝔓 L (B 𝔓)) (hM : ∀ 𝔓 i, u i = ∑ j, Mx 𝔓 i j • B 𝔓 j) :
    (Function.support fun 𝔓 ↦ (vAdd 𝔓 (Mx 𝔓).det : ℝ)).Finite ∧
      lineDeg (fun σ ↦ Real.sqrt (h.gram σ u).det.re) (fun 𝔓 ↦ (vAdd 𝔓 (Mx 𝔓).det : ℝ)) =
        ReciprocityTheory.GeometryOfNumbersTheory.deg h L := by
  classical
  obtain ⟨t, ht0, htu⟩ := exists_smul_mem (L := L) (u := u) fun i ↦ hsp ▸ Submodule.subset_span ⟨i, rfl⟩
  set c : K := (t : K) with hc
  have hc0 : c ≠ 0 := fun h0 ↦ ht0 (by rw [hc] at h0; exact_mod_cast h0)
  set w : Fin m → Fin n → K := fun i ↦ c • u i with hwdef
  have hwL : ∀ i, w i ∈ L := fun i ↦ by
    simp only [hwdef, hc, algebraMap_smul]; exact htu i
  have hwli : LinearIndependent K w := hu.units_smul fun _ ↦ Units.mk0 c hc0
  have hw : ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K L w := by
    refine ⟨hwL, hwli, fun x hx ↦ ?_⟩
    have hx' : x ∈ Submodule.span K (Set.range u) := hsp ▸ Submodule.subset_span hx
    refine Submodule.span_le.2 ?_ hx'
    rintro _ ⟨i, rfl⟩
    have : u i = c⁻¹ • w i := by simp [hwdef, smul_smul, inv_mul_cancel₀ hc0]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hMw : ∀ 𝔓 i, w i = ∑ j, (c • Mx 𝔓) i j • B 𝔓 j := by
    intro 𝔓 i
    simp only [hwdef, hM 𝔓 i, Finset.smul_sum, smul_smul, Matrix.smul_apply, smul_eq_mul]
  obtain ⟨hfw, hsw⟩ := index_formula hL hw B (fun 𝔓 ↦ c • Mx 𝔓) hB hMw
  have hv : ∀ 𝔓, (vAdd 𝔓 (Mx 𝔓).det : ℝ) = (vAdd 𝔓 (c • Mx 𝔓).det : ℝ) - m * (vAdd 𝔓 c : ℝ) := by
    intro 𝔓
    rw [Matrix.det_smul, Fintype.card_fin, vAdd_mul' 𝔓 (pow_ne_zero _ hc0) (det_ne_zero_of_comb hu (hM 𝔓)),
      vAdd_pow' 𝔓 hc0]
    push_cast; ring
  have hfc := finite_vAdd hc0
  have hfin : (Function.support fun 𝔓 ↦ (vAdd 𝔓 (Mx 𝔓).det : ℝ)).Finite := by
    refine (hfw.union hfc).subset fun 𝔓 h ↦ ?_
    by_contra hn
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    exact h (show (vAdd 𝔓 (Mx 𝔓).det : ℝ) = 0 by rw [hv, hn.1, hn.2]; simp)
  refine ⟨hfin, ?_⟩
  have hnum := lineDeg_num hc0
  simp only [lineDeg] at hnum ⊢
  have hsum : ∑ᶠ 𝔓, (vAdd 𝔓 (Mx 𝔓).det : ℝ) * lw K 𝔓 =
      ∑ᶠ 𝔓, (vAdd 𝔓 (c • Mx 𝔓).det : ℝ) * lw K 𝔓 - m * ∑ᶠ 𝔓, (vAdd 𝔓 c : ℝ) * lw K 𝔓 := by
    rw [mul_finsum, ← finsum_sub_distrib (fin_mul hfw _)
      (hfc.subset fun 𝔓 h ↦ by
        rw [Function.mem_support] at h ⊢; intro h0; apply h; simp [h0])]
    refine finsum_congr fun 𝔓 ↦ ?_
    rw [hv]; ring
  rw [hsum, hsw, ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily h hL hw, ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily]
  have hpos := fun σ ↦ det_gram_re_pos h σ hu
  have hσ : ∀ σ : K →+* ℂ, 0 < ‖σ c‖ := fun σ ↦ norm_pos_iff.2 ((map_ne_zero σ).2 hc0)
  have hg : ∀ σ : K →+* ℂ, Real.log (h.gram σ w).det.re =
      2 * m * Real.log ‖σ c‖ + Real.log (h.gram σ u).det.re := by
    intro σ
    rw [hwdef, det_gram_smul, Real.log_mul (pow_pos (pow_pos (hσ σ) 2) m).ne' (hpos σ).ne', ← pow_mul, Real.log_pow]
    push_cast; ring
  have hq : ∀ σ : K →+* ℂ, Real.log (Real.sqrt (h.gram σ u).det.re) = Real.log (h.gram σ u).det.re / 2 :=
    fun σ ↦ Real.log_sqrt (hpos σ).le
  simp only [hg, hq, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  have hd : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  have hnum' : ∑ᶠ 𝔓, (vAdd 𝔓 c : ℝ) * lw K 𝔓 = (∑ σ : K →+* ℂ, Real.log ‖σ c‖) / finrank ℚ K := by
    linarith
  rw [hnum']
  field_simp
  ring

end GlobalTheory.LatDetDeg

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem GlobalTheory.LatDetDeg.lineDeg_det_line : ∀ (K : Type) [Field K] [NumberField K] {n : ℕ} (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (L L' : Submodule (𝓞 K) (Fin n → K)), L.FG → L'.FG → ∀ {m m' : ℕ} (u : Fin m → Fin n → K) (u' : Fin m' → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = Submodule.span K (L : Set (Fin n → K)) → LinearIndependent K u' → Submodule.span K (Set.range u') = Submodule.span K (L' : Set (Fin n → K)) → ∀ a : K, a ≠ 0 → ∀ ρK : HeightOneSpectrum (𝓞 K) → ℝ, (∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (b : Fin m → Fin n → K) (M : Matrix (Fin m) (Fin m) K) (b' : Fin m' → Fin n → K) (M' : Matrix (Fin m') (Fin m') K), GlobalTheory.PtDeg.LocBasis 𝔓 L b → (∀ i, u i = ∑ j, M i j • b j) → GlobalTheory.PtDeg.LocBasis 𝔓 L' b' → (∀ i, u' i = ∑ j, M' i j • b' j) → ρK 𝔓 = (vAdd 𝔓 a : ℝ) + (vAdd 𝔓 M.det : ℝ) - (vAdd 𝔓 M'.det : ℝ)) → (Function.support ρK).Finite ∧ lineDeg (fun σ : K →+* ℂ => ‖σ a‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re) ρK = ReciprocityTheory.GeometryOfNumbersTheory.deg h L - ReciprocityTheory.GeometryOfNumbersTheory.deg h L' := by
  intro K _ _ n h L L' hL hL' m m' u u' hu hsp hu' hsp' a ha ρK hρ
  choose B Mx hB hM using fun 𝔓 ↦ GlobalTheory.LatDetDeg.exists_locBasis_comb hL hu hsp 𝔓
  choose B' Mx' hB' hM' using fun 𝔓 ↦ GlobalTheory.LatDetDeg.exists_locBasis_comb hL' hu' hsp' 𝔓
  obtain ⟨hf, hd⟩ := GlobalTheory.LatDetDeg.lineDeg_frame h hL hu hsp B Mx hB hM
  obtain ⟨hf', hd'⟩ := GlobalTheory.LatDetDeg.lineDeg_frame h hL' hu' hsp' B' Mx' hB' hM'
  have hρ' : ρK = ((fun 𝔓 ↦ (vAdd 𝔓 a : ℝ)) + fun 𝔓 ↦ (vAdd 𝔓 (Mx 𝔓).det : ℝ)) +
      -(fun 𝔓 ↦ (vAdd 𝔓 (Mx' 𝔓).det : ℝ)) := funext fun 𝔓 ↦ by
    rw [hρ 𝔓 _ _ _ _ (hB 𝔓) (hM 𝔓) (hB' 𝔓) (hM' 𝔓)]
    simp only [Pi.add_apply, Pi.neg_apply]; ring
  have hr : (fun σ : K →+* ℂ ↦ ‖σ a‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re) =
      ((fun σ : K →+* ℂ ↦ ‖σ a‖) * fun σ ↦ Real.sqrt (h.gram σ u).det.re) *
        (fun σ : K →+* ℂ ↦ Real.sqrt (h.gram σ u').det.re)⁻¹ := funext fun σ ↦ by
    simp only [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
  have h1 : ∀ σ : K →+* ℂ, 0 < ‖σ a‖ := fun σ ↦ norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  have h2 : ∀ σ : K →+* ℂ, 0 < Real.sqrt (h.gram σ u).det.re :=
    fun σ ↦ Real.sqrt_pos.2 (GlobalTheory.LatDetDeg.det_gram_re_pos h σ hu)
  have h3 : ∀ σ : K →+* ℂ, 0 < Real.sqrt (h.gram σ u').det.re :=
    fun σ ↦ Real.sqrt_pos.2 (GlobalTheory.LatDetDeg.det_gram_re_pos h σ hu')
  have hfa := finite_vAdd ha
  have hf12 : (Function.support ((fun 𝔓 ↦ (vAdd 𝔓 a : ℝ)) + fun 𝔓 ↦ (vAdd 𝔓 (Mx 𝔓).det : ℝ))).Finite :=
    (hfa.union hf).subset (Function.support_add _ _)
  have hf3 : (Function.support (-(fun 𝔓 ↦ (vAdd 𝔓 (Mx' 𝔓).det : ℝ)))).Finite := by
    exact hf'.subset fun x hx ↦ by simpa using hx
  refine ⟨hρ' ▸ (hf12.union hf3).subset (Function.support_add _ _), ?_⟩
  rw [hρ', hr, lineDeg_mul (r := (fun σ : K →+* ℂ ↦ ‖σ a‖) * fun σ ↦ Real.sqrt (h.gram σ u).det.re)
    (r' := (fun σ : K →+* ℂ ↦ Real.sqrt (h.gram σ u').det.re)⁻¹) (fun σ ↦ mul_pos (h1 σ) (h2 σ))
    (fun σ ↦ inv_pos.2 (h3 σ)) hf12 hf3,
    lineDeg_mul (r := fun σ : K →+* ℂ ↦ ‖σ a‖) (r' := fun σ ↦ Real.sqrt (h.gram σ u).det.re) h1 h2 hfa hf,
    lineDeg_inv, lineDeg_num ha, hd, hd']
  ring
