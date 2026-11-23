import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private theorem sm_rho_nonneg (x : ℝ) : 0 ≤ rho x := Real.smoothTransition.nonneg _

private theorem toR_zero : toR (0 : UpperTheory.V.KT.Lat L N) = 0 := by
  unfold toR
  funext w a
  simp

private theorem q_zero_right (h : HS L N) : q h 0 = 0 := by
  unfold q qR
  rw [toR_zero]
  simp

private theorem rk_zero_right (h : HS L N) : rk h 0 = 0 := by
  ext w i j
  unfold rk mkHS
  simp [toR_zero, vecMulVec]

private theorem contDiff_hs_entry (w : InfinitePlace L) (i j : Fin N) :
    ContDiff ℝ ⊤ (fun h : HS L N => (h : InfinitePlace L → Fin N → Fin N → ℂ) w i j) := by
  have hc : ContDiff ℝ ⊤ (fun h : HS L N => (h : InfinitePlace L → Fin N → Fin N → ℂ)) :=
    (HSsub L N).subtypeL.contDiff
  exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hc w) i) j

private theorem contDiff_qR_left (x : VR L N) : ContDiff ℝ ⊤ (fun h : HS L N => qR h x) := by
  unfold qR mat
  apply ContDiff.sum
  intro w _
  refine Complex.reCLM.contDiff.comp ?_
  simp only [dotProduct, mulVec, Matrix.of_apply]
  apply ContDiff.sum
  intro i _
  refine contDiff_const.mul ?_
  apply ContDiff.sum
  intro j _
  exact (contDiff_hs_entry w i j).mul contDiff_const

private theorem contDiff_rk_left (v : UpperTheory.V.KT.Lat L N) : ContDiff ℝ ⊤ (fun h : HS L N => rk h v) := by
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional (HSsub L N)
  have e : (fun h : HS L N => rk h v) =
      fun h => P ((rk h v : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) := by
    funext h
    rw [hP]
  rw [e]
  refine P.contDiff.comp ?_
  have hm : ∀ w i, ContDiff ℝ ⊤
      (fun h : HS L N => (of ((h : InfinitePlace L → Fin N → Fin N → ℂ) w) *ᵥ toR v w) i) := by
    intro w i
    simp only [mulVec, dotProduct, Matrix.of_apply]
    apply ContDiff.sum
    intro j _
    exact (contDiff_hs_entry w i j).mul contDiff_const
  unfold rk mkHS mat
  refine contDiff_pi.2 fun w => contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [vecMulVec, Matrix.of_apply, Pi.star_apply]
  exact (hm w i).mul (Complex.conjCLE.contDiff.comp (hm w j))

private theorem smoothTransition_eq_zero_of_four_mul_le (y t : ℝ) (ht : 0 < t) (hy : 4 * t ≤ y) :
    Real.smoothTransition ((4 - y / t) / 3) = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : 4 ≤ y / t := (le_div_iff₀ ht).2 (by linarith)
  linarith

private theorem contDiff_rho : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rho := by
  unfold rho
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem pf_GRSmooth : GRSmooth := by
  classical
  unfold GRSmooth Basic RSmooth
  intro hB L _ _ N hN μ hμ
  obtain ⟨h1, -, ⟨c, C, hc, hcmp⟩, -⟩ := hμ
  obtain ⟨hP, -⟩ := hB L N hN
  unfold ret
  apply contDiffOn_of_locally_contDiffOn
  intro h0 hh0
  have hl0 : 0 < lam h0 := (hP h0 hh0).1
  have hd0 : 0 < lamD h0 := by
    unfold lamD
    exact (hP _ (hP h0 hh0).2.2.2.1).1
  have hμ0 : 0 < μ h0 := lt_of_lt_of_le (mul_pos hc hd0) (hcmp h0 hh0).1
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (8 / μ h0) (by norm_num : (1:ℝ) < 4)
  obtain ⟨S, hSf, hS⟩ := locfin L N h0 hh0 (4 * (4:ℝ) ^ n1)
  have hq : ∀ᶠ k in nhds h0, ∀ v ∈ S, v ≠ 0 → lam h0 / 2 < q k v := by
    refine (Filter.eventually_all_finite hSf).2 ?_
    intro v _
    by_cases hv : v = 0
    · exact Filter.Eventually.of_forall (fun _ hne => absurd hv hne)
    · have hcont : ContinuousAt (fun k : HS L N => q k v) h0 :=
        (contDiff_qR_left (toR v)).continuous.continuousAt
      have hlt : lam h0 / 2 < q h0 v := by
        have := (hP h0 hh0).2.1 v hv
        linarith
      filter_upwards [hcont.eventually (lt_mem_nhds hlt)] with k hk _ using hk
  have hμe : ∀ᶠ k in nhdsWithin h0 (Pos L N), μ h0 / 2 < μ k :=
    (h1.continuousOn.continuousWithinAt hh0).eventually (lt_mem_nhds (by linarith))
  have hall : ∀ᶠ k in nhdsWithin h0 (Pos L N), μ h0 / 2 < μ k ∧
      (∀ y ∉ S, 4 * (4:ℝ) ^ n1 < q k y) ∧ (∀ v ∈ S, v ≠ 0 → lam h0 / 2 < q k v) :=
    hμe.and ((hS.filter_mono nhdsWithin_le_nhds).and (hq.filter_mono nhdsWithin_le_nhds))
  obtain ⟨u, hu, h0u, hsub⟩ := mem_nhdsWithin.1 hall
  refine ⟨u, hu, h0u, ?_⟩
  set m : ℝ := min (lam h0 / 2) (4 * (4:ℝ) ^ n1) with hmEq
  have hm : 0 < m := lt_min (by linarith) (by positivity)
  obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt (4 / m) (by norm_num : (1:ℝ) < 4)
  set S' : Finset (UpperTheory.V.KT.Lat L N) := insert 0 hSf.toFinset with hSEq
  have key : ∀ h ∈ Pos L N ∩ u,
      μ h • h + ∑ᶠ k : ℤ, rho ((4:ℝ) ^ k * μ h) • term ((4:ℝ) ^ k) h =
      μ h • h + ∑ k ∈ Finset.Icc (-(n0:ℤ)) (n1:ℤ), rho ((4:ℝ) ^ k * μ h) •
        ((((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k))⁻¹ •
          ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) • rk h v) := by
    intro h hh
    obtain ⟨hμh, hSq, hSq0⟩ := hsub ⟨hh.2, hh.1⟩
    have hfar : ∀ k : ℤ, k ≤ (n1:ℤ) → ∀ v ∉ S', 4 * (4:ℝ) ^ k ≤ qR h (toR v) := by
      intro k hk v hv
      have hvS : v ∉ S := fun hvS => hv (Finset.mem_insert_of_mem (hSf.mem_toFinset.2 hvS))
      have h2 := hSq v hvS
      have h3 : (4:ℝ) ^ k ≤ (4:ℝ) ^ (n1:ℤ) := zpow_le_zpow_right₀ (by norm_num) hk
      rw [zpow_natCast] at h3
      have h4 : q h v = qR h (toR v) := rfl
      linarith
    have hterm : ∀ k : ℤ, k ≤ (n1:ℤ) → term ((4:ℝ) ^ k) h =
        ((((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k))⁻¹ •
          ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) • rk h v) := by
      intro k hk
      have ht : (0:ℝ) < (4:ℝ) ^ k := by positivity
      unfold term zed
      rw [finsum_eq_sum_of_support_subset _ (s := S') ?_, finsum_eq_sum_of_support_subset _ (s := S') ?_]
      · rfl
      all_goals
        refine Function.support_subset_iff'.2 fun v hv => ?_
        have hrz : rho (qR h (toR v) / (4:ℝ) ^ k) = 0 := by
          unfold rho
          exact smoothTransition_eq_zero_of_four_mul_le _ _ ht (hfar k hk v hv)
        first
          | exact hrz
          | rw [show rho (q h v / (4:ℝ) ^ k) = 0 from hrz, zero_smul]
    have hsmall : ∀ k : ℤ, k < -(n0:ℤ) → term ((4:ℝ) ^ k) h = 0 := by
      intro k hk
      have ht : (0:ℝ) < (4:ℝ) ^ k := by positivity
      have hk4 : 4 * (4:ℝ) ^ k < m := by
        have h3 : (4:ℝ) ^ k ≤ (4:ℝ) ^ (-(n0:ℤ)) := zpow_le_zpow_right₀ (by norm_num) hk.le
        rw [_root_.zpow_neg, zpow_natCast] at h3
        have h5 : ((4:ℝ) ^ n0)⁻¹ < m / 4 := by
          rw [inv_lt_comm₀ (by positivity) (by positivity)]
          calc (m / 4)⁻¹ = 4 / m := by field_simp
            _ < 4 ^ n0 := hn0
        linarith
      unfold term
      rw [finsum_eq_zero_of_forall_eq_zero, smul_zero]
      intro v
      by_cases hv : v = 0
      · rw [hv, rk_zero_right, smul_zero]
      · have hqv : m ≤ q h v := by
          by_cases hvS : v ∈ S
          · exact le_trans (min_le_left _ _) (hSq0 v hvS hv).le
          · exact le_trans (min_le_right _ _) (hSq v hvS).le
        have hrz : rho (q h v / (4:ℝ) ^ k) = 0 := by
          unfold rho
          exact smoothTransition_eq_zero_of_four_mul_le _ _ ht (by linarith)
        rw [hrz, zero_smul]
    have hbig : ∀ k : ℤ, (n1:ℤ) < k → rho ((4:ℝ) ^ k * μ h) = 0 := by
      intro k hk
      unfold rho
      apply Real.smoothTransition.zero_of_nonpos
      have h3 : (4:ℝ) ^ (n1:ℤ) ≤ (4:ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hk.le
      rw [zpow_natCast] at h3
      have h6 : 8 / μ h0 * (μ h0 / 2) = 4 := by field_simp; ring
      have h7 : 8 / μ h0 * (μ h0 / 2) ≤ (4:ℝ) ^ k * μ h := by
        apply mul_le_mul (by linarith) hμh.le (by positivity) (by positivity)
      linarith
    congr 1
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-(n0:ℤ)) (n1:ℤ)) ?_]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [hterm k (Finset.mem_Icc.1 hk).2]
    · refine Function.support_subset_iff'.2 fun k hk => ?_
      simp only [Finset.coe_Icc, Set.mem_Icc, not_and_or, not_le] at hk
      rcases hk with hk | hk
      · show rho ((4:ℝ) ^ k * μ h) • term ((4:ℝ) ^ k) h = 0
        rw [hsmall k hk, smul_zero]
      · show rho ((4:ℝ) ^ k * μ h) • term ((4:ℝ) ^ k) h = 0
        rw [hbig k hk, zero_smul]
  refine ContDiffOn.congr ?_ key
  refine (h1.mono Set.inter_subset_left).smul contDiffOn_id |>.add ?_
  refine ContDiffOn.sum fun k _ => ?_
  have hr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun h : HS L N => rho ((4:ℝ) ^ k * μ h)) (Pos L N ∩ u) :=
    contDiff_rho.comp_contDiffOn (contDiffOn_const.mul (h1.mono Set.inter_subset_left))
  have hz : ∀ v : UpperTheory.V.KT.Lat L N, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun h : HS L N => rho (qR h (toR v) / (4:ℝ) ^ k)) (Pos L N ∩ u) := fun v =>
    (contDiff_rho.comp (((contDiff_qR_left (toR v)).of_le le_top).div_const _)).contDiffOn
  have hinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun h : HS L N => (((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k))⁻¹) (Pos L N ∩ u) := by
    refine ContDiffOn.inv (contDiffOn_const.mul (ContDiffOn.sum fun v _ => hz v)) ?_
    intro h _
    have ht : (0:ℝ) < (4:ℝ) ^ k := by positivity
    have hone : (1:ℝ) ≤ ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) := by
      have h0mem : (0 : UpperTheory.V.KT.Lat L N) ∈ S' := by
        rw [hSEq]
        exact Finset.mem_insert_self _ _
      have hle := Finset.single_le_sum (f := fun v => rho (qR h (toR v) / (4:ℝ) ^ k))
        (fun v _ => sm_rho_nonneg _) h0mem
      have hq0 : qR h (toR 0) = 0 := q_zero_right h
      have hr0 : rho 0 = 1 := by
        unfold rho
        exact Real.smoothTransition.one_of_one_le (by norm_num)
      simp only [hq0, zero_div, hr0] at hle
      exact hle
    have : 0 < ((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) := by positivity
    exact this.ne'
  have hsum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun h : HS L N => ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) • rk h v)
      (Pos L N ∩ u) := by
    refine ContDiffOn.sum fun v _ => ?_
    exact ContDiffOn.smul (hz v) (((contDiff_rk_left v).of_le le_top).contDiffOn)
  exact hr.smul (hinv.smul hsum)

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
