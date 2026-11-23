import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockDefectMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockRealGramComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockComplexGramMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ATeleSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

section Telescoping

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def quotLine (C A : HermLine ι) (ha : A.a = C.a) : HermLine ι where
  a := 0
  h z := A.h z / C.h z
  pos z hz := div_pos (A.pos z hz) (C.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, C.smul c z hc, ha]
    have hne : (∏ k, ‖c k‖ ^ C.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    rw [mul_div_mul_left _ _ hne]
    simp

theorem tensor_quotLine (C A : HermLine ι) (ha : A.a = C.a) (hv : ∀ z, C.h z = 0 → A.h z = 0) :
    C.tensor (quotLine C A ha) = A := by
  apply tele_herm_ext
  · funext k
    simp [HermLine.tensor, quotLine, ha]
  · funext z
    show C.h z * (A.h z / C.h z) = A.h z
    by_cases h0 : C.h z = 0
    · rw [h0, hv z h0, zero_mul]
    · exact mul_div_cancel₀ _ h0

theorem isSmoothHerm_quotLine {C A : HermLine ι} (ha : A.a = C.a) (hC : IsSmoothHerm C) (hA : IsSmoothHerm A) :
    IsSmoothHerm (quotLine C A ha) :=
  hA.div hC fun z hz => (C.pos z hz).ne'

theorem fam_degZero_block (I : AllFam) (hI : I.IsFamily) {P : Ideal (MRing ι)} {n : ℕ}
    (hP : IsArithVar P (n + 1)) (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j))
    (B : HermLine ι) (hB : IsSmoothHerm B) (hB0 : B.a = 0) :
    I K ι P (n + 1) (Fin.snoc L B) = ptsIntegral P (pot L) fun z => Real.log (B.h z) := by
  classical
  have hR := (hI K ι).2.2 P n L B 1 0 hP hL hB (fun k => by simp [hB0])
    tele_one_homog (fun h1 => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h1))
  rw [hR]
  unfold recR
  rw [tele_divSupp_one, finsum_mem_empty, zero_sub]
  unfold arInt
  have hl : logNorm B 1 = fun z => - Real.log (B.h z) := by
    funext z
    simp [logNorm, Real.log_inv]
  rw [hl, tele_ptsIntegral_neg, neg_neg]
  rfl

theorem ptsIntegral_log_sub (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {e : ℕ}
    (hP : IsArithVar P (e + 1)) (L : Fin e → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j))
    (B₀ B₁ : HermLine ι) (h₀ : IsSmoothHerm B₀) (h₁ : IsSmoothHerm B₁) (h₀a : B₀.a = 0) (h₁a : B₁.a = 0)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (hg : ∀ z ∈ mcPts P, g z = Real.log (B₁.h z) - Real.log (B₀.h z)) :
    ptsIntegral P (pot L) (fun z => Real.log (B₁.h z)) - ptsIntegral P (pot L) (fun z => Real.log (B₀.h z)) =
      ptsIntegral P (pot L) g := by
  classical
  have hl : ∀ B : HermLine ι, (fun z => Real.log (B.h z)) = fun z => - logNorm B 1 z := by
    intro B
    funext z
    simp [logNorm, Real.log_inv]
  have hP1 : (1 : MRing ι) ∉ P := fun h1 => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  have hsec : ∀ B : HermLine ι, B.a = 0 → IsSectionOn P B 1 := fun B hB =>
    ⟨0, fun k => by simp [hB], tele_one_homog, hP1⟩
  rw [hl B₁, hl B₀, tele_ptsIntegral_neg, tele_ptsIntegral_neg]
  unfold ptsIntegral
  split_ifs with hΨ
  · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
    unfold ptsIntegralAt
    rw [neg_sub_neg, ← integral_sub (hInt K ι P e _ L B₀ 1 hP hΨg hL h₀ (hsec B₀ h₀a))
      (hInt K ι P e _ L B₁ 1 hP hΨg hL h₁ (hsec B₁ h₁a))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P e _ hP hΨg y)]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hz : hγ.choose y ∈ mcPts P := hγ.choose_spec.2.self_of_nhds.2.1
      rw [hg _ hz]
      simp only [logNorm, map_one, norm_one, one_div, Real.log_inv]
      ring
    · simp
  · simp

def blockTeleFam (A A' : HermLine ι) (N i : ℕ) : Fin N → HermLine ι :=
  fun j => if j.val < i then A' else A

theorem blockTeleFam_succAbove (A A' : HermLine ι) (D i : ℕ) (hi : i < D + 1) (k : ℕ) (hk : k = i ∨ k = i + 1) :
    blockTeleFam A A' (D + 1) k ∘ (⟨i, hi⟩ : Fin (D + 1)).succAbove = blockTeleFam A A' D i := by
  funext j
  simp only [Function.comp_apply, blockTeleFam]
  by_cases h : j.val < i
  · have h' : Fin.castSucc j < (⟨i, hi⟩ : Fin (D + 1)) := by
      rw [Fin.lt_def]
      exact h
    rw [Fin.succAbove_of_castSucc_lt _ _ h', if_pos (show (Fin.castSucc j).val < k by
      show j.val < k
      omega), if_pos h]
  · have h' : (⟨i, hi⟩ : Fin (D + 1)) ≤ Fin.castSucc j := by
      rw [Fin.le_def]
      show i ≤ j.val
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ h', if_neg (show ¬ (Fin.succ j).val < k by
      show ¬ j.val + 1 < k
      omega), if_neg h]

theorem blockTeleFam_smooth {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (N i : ℕ)
    (j : Fin N) : IsSmoothHerm (blockTeleFam A A' N i j) := by
  unfold blockTeleFam
  split_ifs
  · exact hA'
  · exact hA

theorem top_sub_top_blockMixPot (hInt : PtsIntegrableStatement) (I : AllFam) (hI : I.IsFamily)
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) {A A' C : HermLine ι} (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') (hC : IsSmoothHerm C) (ha : A.a = C.a) (ha' : A'.a = C.a)
    (hv : ∀ z, C.h z = 0 → A.h z = 0) (hv' : ∀ z, C.h z = 0 → A'.h z = 0) :
    I K ι P (D + 1) (fun _ => A') - I K ι P (D + 1) (fun _ => A) = ∑ i ∈ Finset.range (D + 1),
      ptsIntegral P (blockMixPot A A' D i) fun z => Real.log (A'.h z / A.h z) := by
  classical
  have hsymm := (hI K ι).1
  have hadd := (hI K ι).2.1
  have hB₀ := isSmoothHerm_quotLine ha hC hA
  have hB₁ := isSmoothHerm_quotLine ha' hC hA'
  have htel := Finset.sum_range_sub (fun i => I K ι P (D + 1) (blockTeleFam A A' (D + 1) i)) (D + 1)
  have hT0 : blockTeleFam A A' (D + 1) 0 = fun _ => A := by
    funext j
    simp [blockTeleFam]
  have hT1 : blockTeleFam A A' (D + 1) (D + 1) = fun _ => A' := by
    funext j
    simp [blockTeleFam, j.isLt]
  simp only [hT0, hT1] at htel
  rw [← htel]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hLs := blockTeleFam_smooth hA hA' D i
  have e1 : I K ι P (D + 1) (blockTeleFam A A' (D + 1) (i + 1)) =
      I K ι P (D + 1) (Fin.snoc (blockTeleFam A A' D i) A') := by
    have h := hsymm _ _ (blockTeleFam A A' (D + 1) (i + 1)) (tele_perm ⟨i, hi⟩) hP
      (blockTeleFam_smooth hA hA' _ _)
    have hv1 : blockTeleFam A A' (D + 1) (i + 1) ⟨i, hi⟩ = A' := by
      simp [blockTeleFam]
    rw [tele_comp_perm, blockTeleFam_succAbove A A' D i hi (i + 1) (Or.inr rfl), hv1] at h
    exact h.symm
  have e0 : I K ι P (D + 1) (blockTeleFam A A' (D + 1) i) =
      I K ι P (D + 1) (Fin.snoc (blockTeleFam A A' D i) A) := by
    have h := hsymm _ _ (blockTeleFam A A' (D + 1) i) (tele_perm ⟨i, hi⟩) hP
      (blockTeleFam_smooth hA hA' _ _)
    have hv0 : blockTeleFam A A' (D + 1) i ⟨i, hi⟩ = A := by
      simp [blockTeleFam]
    rw [tele_comp_perm, blockTeleFam_succAbove A A' D i hi i (Or.inl rfl), hv0] at h
    exact h.symm
  have hpot : pot (blockTeleFam A A' D i) = blockMixPot A A' D i := by
    funext j z
    simp only [pot, blockMixPot, blockTeleFam]
    split_ifs <;> rfl
  rw [e1, e0]
  have q1 : (Fin.snoc (α := fun _ => HermLine ι) (blockTeleFam A A' D i) A') =
      Fin.snoc (α := fun _ => HermLine ι) (blockTeleFam A A' D i) (C.tensor (quotLine C A' ha')) := by
    rw [tensor_quotLine C A' ha' hv']
  have q0 : (Fin.snoc (α := fun _ => HermLine ι) (blockTeleFam A A' D i) A) =
      Fin.snoc (α := fun _ => HermLine ι) (blockTeleFam A A' D i) (C.tensor (quotLine C A ha)) := by
    rw [tensor_quotLine C A ha hv]
  rw [q1, q0]
  rw [hadd _ _ _ _ _ hP hLs hC hB₁, hadd _ _ _ _ _ hP hLs hC hB₀, add_sub_add_left_eq_sub,
    fam_degZero_block I hI hP _ hLs _ hB₁ rfl, fam_degZero_block I hI hP _ hLs _ hB₀ rfl,
    ptsIntegral_log_sub hInt hP _ hLs _ _ hB₀ hB₁ rfl rfl (fun z => Real.log (A'.h z / A.h z)) ?_, hpot]
  intro z hz
  have hA0 := A.pos z hz.1
  have hA'0 := A'.pos z hz.1
  have hC0 := C.pos z hz.1
  show Real.log (A'.h z / A.h z) = Real.log (A'.h z / C.h z) - Real.log (A.h z / C.h z)
  rw [Real.log_div hA'0.ne' hA0.ne', Real.log_div hA'0.ne' hC0.ne', Real.log_div hA0.ne' hC0.ne']
  ring

end Telescoping

section Pivot

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem h_eq_zero_of_fs (k₀ : K) (A : HermLine ι) (hA : A.a = unitDeg k₀) (z : (Σ k, ι k) → ℂ)
    (hz : (HermLine.ofMetrics (fun k => fsMetric (ι k)) (unitDeg k₀)).h z = 0) : A.h z = 0 := by
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hz
  have hk0 : k = k₀ := by
    by_contra hne
    simp [unitDeg, hne] at hk
  subst hk0
  have hρ : (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) = 0 := by
    simpa [unitDeg] using hk
  have hzk : (fun i => z ⟨k, i⟩) = 0 := by
    by_contra hne
    exact ((fsMetric (ι k)).pos _ hne).ne' hρ
  set c : K → ℂ := fun k' => if k' = k then 2 else 1 with hc
  have hc0 : ∀ k', c k' ≠ 0 := fun k' => by
    simp only [hc]
    split_ifs <;> norm_num
  have hfix : (fun p : (Σ k, ι k) => c p.1 * z p) = z := by
    funext p
    by_cases hp : p.1 = k
    · obtain ⟨k', i⟩ := p
      simp only at hp
      subst hp
      have : z ⟨k', i⟩ = 0 := congrFun hzk i
      simp [this]
    · simp [hc, hp]
  have hs := A.smul c z hc0
  rw [hfix, hA] at hs
  have hprod : (∏ k', ‖c k'‖ ^ unitDeg k k') = 2 := by
    rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [unitDeg, hk']) (fun h => absurd (Finset.mem_univ k) h)]
    simp [hc, unitDeg]
  rw [hprod] at hs
  linarith

end Pivot

theorem BlockDefectMetricChange.proof (hR : BlockRealGramComparison.Statement)
    (hC : BlockComplexGramMetricChange.Statement) (hM : BlockResolutionMixedIntegral.Statement)
    (hInt : PtsIntegrableStatement) : BlockDefectMetricChange.Statement := by
  intro D K _ _ ι _ Ω _ _ I d A' P0' hdeg hc hle hp hI
  have h₁ := hR D K ι Ω (d.withMetric A' P0' hdeg hc hle hp)
  have h₀ := hR D K ι Ω d
  have hc₁ := hC D K ι Ω d A' P0' hdeg hc hle hp
  have hFS := GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) (unitDeg d.k₀)
  have htop : I K ι (mCoordIdeal d.y) (D + 1) (fun _ => A') =
      I K ι (mCoordIdeal d.y) (D + 1) (fun _ => d.A) + ((D : ℝ) + 1) * blockMetricInt d A' := by
    rw [← hM D K ι Ω d A' hdeg hp.1, ← top_sub_top_blockMixPot hInt I hI d.arith d.semipos.1 hp.1 hFS
      (d.deg.trans rfl) (hdeg.trans rfl) (h_eq_zero_of_fs d.k₀ d.A d.deg) (h_eq_zero_of_fs d.k₀ A' hdeg)]
    ring
  have hlog := isLittleO_pow_mul_log D
  refine (((h₁.trans_isLittleO hlog).sub (h₀.trans_isLittleO hlog)).add hc₁).congr_left fun n => ?_
  simp only [hsDefect, htop, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
