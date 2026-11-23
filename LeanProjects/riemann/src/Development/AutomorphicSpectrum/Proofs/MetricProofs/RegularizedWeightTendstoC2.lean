import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.NormIteratedFDerivCompLeOfIsOpen
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PPropertyF
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
set_option maxSynthPendingDepth 1

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

open Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink regMax coordDiv limsupExt)
open GroundTheory.Heights₂.Heights.AnalyticLimit
open GroundTheory.Heights₂.Heights.Regular (RegChartData PotentialCharts)

noncomputable section

theorem arg_C2_through_chart {D : ℕ} (ρ : Mollifier D) {O P L : Set (Fin D → ℂ)}
    (hO : IsOpen O) (hP : IsOpen P) (hL : IsCompact L) (hLO : L ⊆ O)
    {T : (Fin D → ℂ) → Fin D → ℂ} (hTO : ContDiffOn ℝ ∞ T O) (hTP : MapsTo T O P)
    {u f g H : (Fin D → ℂ) → ℝ} (hu : ContDiffOn ℝ ∞ u P)
    (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O) (hH : ContDiffOn ℝ ∞ H O)
    (hfeq : ∀ y ∈ O, f y = u (T y) - g y)
    {w : ℝ → (Fin D → ℂ) → ℝ}
    (hw : ∀ Q ⊆ P, IsCompact Q → ∀ᶠ t in 𝓝[>] (0 : ℝ), EqOn (w t) u Q)
    {e : ℝ → ℝ} (he : Tendsto e (𝓝[>] 0) (𝓝 0)) (het : ∀ t, 0 < t → t ≤ e t) :
    ∃ U : Set (Fin D → ℂ), IsOpen U ∧ L ⊆ U ∧ ContDiffOn ℝ 2 f U ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ),
        ContDiffOn ℝ 2 (fun y => molli ρ t (w t) (T y) - g y + 4 * e t * H y) U) ∧
      TendstoC2On (fun t y => molli ρ t (w t) (T y) - g y + 4 * e t * H y) f L ∧
      ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ L,
        ‖fderiv ℝ (fun y' => molli ρ t (w t) (T y') - g y' + 4 * e t * H y') y - fderiv ℝ f y‖ ≤
          M * (t + e t) := by
  have hTc : ContinuousOn T O := hTO.continuousOn
  obtain ⟨δ, hδ, hδO⟩ := hL.exists_cthickening_subset_open hO hLO
  have hKc : IsCompact (cthickening (δ / 2) L) := hL.cthickening
  have hKcO : cthickening (δ / 2) L ⊆ O := (cthickening_mono (by linarith) L).trans hδO
  have hLU : L ⊆ thickening (δ / 2) L := self_subset_thickening (by linarith) L
  have hUK : thickening (δ / 2) L ⊆ cthickening (δ / 2) L := thickening_subset_cthickening _ _
  have hK' : IsCompact (T '' cthickening (δ / 2) L) := hKc.image_of_continuousOn (hTc.mono hKcO)
  have hK'P : T '' cthickening (δ / 2) L ⊆ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact hTP (hKcO hy)
  obtain ⟨δ', hδ', hδ'P⟩ := hK'.exists_cthickening_subset_open hP hK'P
  obtain ⟨Q, hQ_def⟩ : ∃ Q, Q = cthickening δ' (T '' cthickening (δ / 2) L) := ⟨_, rfl⟩
  obtain ⟨P', hP'_def⟩ : ∃ P', P' = thickening δ' (T '' cthickening (δ / 2) L) := ⟨_, rfl⟩
  have hQc : IsCompact Q := hQ_def ▸ hK'.cthickening
  have hQP : Q ⊆ P := hQ_def ▸ hδ'P
  have hP' : IsOpen P' := hP'_def ▸ isOpen_thickening
  have hP'Q : P' ⊆ Q := by
    rw [hP'_def, hQ_def]
    exact thickening_subset_cthickening _ _
  have hK'P' : T '' cthickening (δ / 2) L ⊆ P' := hP'_def ▸ self_subset_thickening hδ' _
  have hu' : ContDiffOn ℝ ∞ u P' := hu.mono (hP'Q.trans hQP)
  have hle : ∀ m : ℕ, (m : WithTop ℕ∞) ≤ ∞ := fun m => by exact_mod_cast le_top
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := hle 3
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := hle 2
  obtain ⟨C₀, ε₀, hε₀, hmol⟩ := ReciprocityTheory.AnForm.A.mollification_second_order D ρ P' (T '' cthickening (δ / 2) L)
    u hP' (hu'.of_le h3) hK' hK'P'
  obtain ⟨BT, hBT⟩ := ArgumentConvergenceLemmas.exists_bound_iteratedFDeriv hO (hTO.of_le h2) hL hLO
  obtain ⟨BH, hBH⟩ := ArgumentConvergenceLemmas.exists_bound_iteratedFDeriv hO (hH.of_le h2) hL hLO
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = max 1 BT := ⟨_, rfl⟩
  have hd1 : 1 ≤ d := hd_def ▸ le_max_left _ _
  have hdBT : BT ≤ d := hd_def ▸ le_max_right _ _
  obtain ⟨C₁, hC₁_def⟩ : ∃ C₁ : ℝ, C₁ = max C₀ 0 := ⟨_, rfl⟩
  have hC₁ : 0 ≤ C₁ := hC₁_def ▸ le_max_right _ _
  have hC₀₁ : C₀ ≤ C₁ := hC₁_def ▸ le_max_left _ _
  obtain ⟨B₁, hB₁_def⟩ : ∃ B₁ : ℝ, B₁ = max BH 0 := ⟨_, rfl⟩
  have hB₁ : 0 ≤ B₁ := hB₁_def ▸ le_max_right _ _
  have hBH₁ : BH ≤ B₁ := hB₁_def ▸ le_max_left _ _
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = 2 * C₁ * d ^ 2 + 4 * B₁ := ⟨_, rfl⟩

  obtain ⟨Fm, hFm⟩ : ∃ Fm : ℝ → (Fin D → ℂ) → ℝ,
      Fm = fun t y => molli ρ t u (T y) - g y + 4 * e t * H y := ⟨_, rfl⟩
  have key : ∀ t ∈ Ioo 0 ε₀, ContDiffOn ℝ 2 (Fm t) (thickening (δ / 2) L) ∧
      ∀ y ∈ L, ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (fun y => Fm t y - f y) y‖ ≤ M * (t + e t) := by
    rintro t ⟨ht0, htε⟩
    have he1 : 0 < e t := ht0.trans_le (het t ht0)
    have hShr : IsOpen (shrink P' t) := ReciprocityTheory.AnForm.A.isOpen_shrink hP' ht0
    have hShrP : shrink P' t ⊆ P' := fun z hz => hz (mem_closedBall_self ht0.le)
    have hm : ContDiffOn ℝ ∞ (molli ρ t u) (shrink P' t) := fun z hz =>
      (ArgumentConvergenceLemmas.molli_contDiffAt ρ hP' hu'.continuousOn ht0 hz).contDiffWithinAt
    have hK'S : ∀ y ∈ cthickening (δ / 2) L, T y ∈ shrink P' t := fun y hy =>
      (hmol t ht0 htε (T y) ⟨y, hy, rfl⟩).1
    obtain ⟨s, hs_def⟩ : ∃ s, s = O ∩ T ⁻¹' shrink P' t := ⟨_, rfl⟩
    have hs : IsOpen s := hs_def ▸ hTc.isOpen_inter_preimage hO hShr
    have hsO : s ⊆ O := hs_def ▸ inter_subset_left
    have hsT : MapsTo T s (shrink P' t) := by
      rw [hs_def]
      exact fun y hy => hy.2
    have hKs : cthickening (δ / 2) L ⊆ s := fun y hy => by
      rw [hs_def]
      exact ⟨hKcO hy, hK'S y hy⟩
    have hTs : ContDiffOn ℝ ∞ T s := hTO.mono hsO
    have hmT : ContDiffOn ℝ ∞ (fun y => molli ρ t u (T y)) s := hm.comp hTs hsT
    have hFs : ContDiffOn ℝ ∞ (Fm t) s := by
      rw [hFm]
      exact (hmT.sub (hg.mono hsO)).add (contDiffOn_const.mul (hH.mono hsO))
    refine ⟨(hFs.of_le h2).mono (hUK.trans hKs), ?_⟩
    intro y hyL n hn
    have hyO : y ∈ O := hLO hyL
    have hyK : y ∈ cthickening (δ / 2) L := self_subset_cthickening L hyL
    have hys : y ∈ s := hKs hyK
    obtain ⟨G, hG_def⟩ : ∃ G : (Fin D → ℂ) → ℝ, G = fun z => molli ρ t u z - u z := ⟨_, rfl⟩
    have hGs : ContDiffOn ℝ ∞ G (shrink P' t) := by
      rw [hG_def]
      exact hm.sub (hu'.mono hShrP)
    have heq : (fun y => Fm t y - f y) =ᶠ[𝓝 y] (G ∘ T) + (4 * e t) • H := by
      filter_upwards [hO.mem_nhds hyO] with y' hy'
      simp only [Pi.add_apply, Function.comp, Pi.smul_apply, smul_eq_mul, hG_def, hFm]
      rw [hfeq y' hy']
      ring
    have hn' : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hGT : ContDiffAt ℝ n (G ∘ T) y :=
      ((hGs.comp hTs hsT).contDiffAt (hs.mem_nhds hys)).of_le hn'
    have hHy : ContDiffAt ℝ n H y := (hH.contDiffAt (hO.mem_nhds hyO)).of_le hn'
    have hcH : ContDiffAt ℝ n ((4 * e t) • H) y := hHy.const_smul (4 * e t)
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_add_apply hGT hcH,
      iteratedFDeriv_const_smul_apply hHy]

    have hmb := hmol t ht0 htε (T y) ⟨y, hyK, rfl⟩
    have hGC : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i G (T y)‖ ≤ C₁ * t := by
      have hCt : C₀ * t ≤ C₁ * t := mul_le_mul_of_nonneg_right hC₀₁ ht0.le
      have hGe : G = fun z => molli ρ t u z - u z := hG_def
      obtain ⟨e0, e1, e2⟩ := ArgumentConvergenceLemmas.norm_iteratedFDeriv_sub_eq hShr (hm.of_le h2)
        ((hu'.mono hShrP).of_le h2) (hK'S y hyK)
      rw [← hGe] at e0 e1 e2
      intro i hi
      interval_cases i
      · rw [e0, Real.norm_eq_abs]
        exact hmb.2.1.trans hCt
      · rw [e1]
        exact hmb.2.2.1.trans hCt
      · rw [e2]
        exact hmb.2.2.2.trans hCt
    have hTd : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i T y‖ ≤ d ^ i := by
      intro i hi1 hi2
      interval_cases i
      · rw [pow_one]
        exact (hBT 1 (by norm_num) y hyL).trans hdBT
      · exact (hBT 2 le_rfl y hyL).trans (hdBT.trans (le_self_pow₀ hd1 (by norm_num)))
    have hGb : ‖iteratedFDeriv ℝ n (G ∘ T) y‖ ≤ n.factorial * (C₁ * t) * d ^ n :=
      ArgumentConvergenceLemmas.norm_iteratedFDeriv_comp_le_of_isOpen hs hShr (hGs.of_le h2) (hTs.of_le h2)
        hsT hys hn hGC hTd
    have hfac : (n.factorial : ℝ) ≤ 2 := by
      interval_cases n <;> norm_num [Nat.factorial]
    have hpow : d ^ n ≤ d ^ 2 := pow_le_pow_right₀ hd1 hn
    have hGb' : ‖iteratedFDeriv ℝ n (G ∘ T) y‖ ≤ 2 * C₁ * d ^ 2 * t := by
      have hCt0 : 0 ≤ C₁ * t := mul_nonneg hC₁ ht0.le
      calc ‖iteratedFDeriv ℝ n (G ∘ T) y‖ ≤ n.factorial * (C₁ * t) * d ^ n := hGb
        _ ≤ 2 * (C₁ * t) * d ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hfac hCt0) hpow (by positivity) (by positivity)
        _ = 2 * C₁ * d ^ 2 * t := by ring

    have hHb : ‖(4 * e t) • iteratedFDeriv ℝ n H y‖ ≤ 4 * B₁ * e t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have := (hBH n hn y hyL).trans hBH₁
      nlinarith
    have hsum := norm_add_le (iteratedFDeriv ℝ n (G ∘ T) y) ((4 * e t) • iteratedFDeriv ℝ n H y)
    have hx1 : 0 ≤ 2 * C₁ * d ^ 2 * e t := by positivity
    have hx2 : 0 ≤ 4 * B₁ * t := by positivity
    have hexp : M * (t + e t) = 2 * C₁ * d ^ 2 * t + 2 * C₁ * d ^ 2 * e t +
        4 * B₁ * t + 4 * B₁ * e t := by
      rw [hM_def]; ring
    linarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 ε₀ := Ioo_mem_nhdsGT hε₀
  have hβ : Tendsto (fun t => M * (t + e t)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((tendsto_id.mono_left nhdsWithin_le_nhds).add he).const_mul M
    simpa using h
  have hfU : ContDiffOn ℝ 2 f (thickening (δ / 2) L) := (hf.of_le h2).mono (hUK.trans hKcO)
  have three : ∀ t ∈ Ioo 0 ε₀, ∀ y ∈ L,
      ‖Fm t y - f y‖ ≤ M * (t + e t) ∧ ‖fderiv ℝ (Fm t) y - fderiv ℝ f y‖ ≤ M * (t + e t) ∧
      ‖fderiv ℝ (fderiv ℝ (Fm t)) y - fderiv ℝ (fderiv ℝ f) y‖ ≤ M * (t + e t) := by
    intro t ht y hy
    obtain ⟨e0, e1, e2⟩ := ArgumentConvergenceLemmas.norm_iteratedFDeriv_sub_eq isOpen_thickening (key t ht).1 hfU
      (hLU hy)
    refine ⟨?_, ?_, ?_⟩
    · rw [← e0]; exact (key t ht).2 y hy 0 (by norm_num)
    · rw [← e1]; exact (key t ht).2 y hy 1 (by norm_num)
    · rw [← e2]; exact (key t ht).2 y hy 2 le_rfl
  have hmodel : TendstoC2On Fm f L := by
    refine ⟨?_, ?_, ?_⟩
    · refine ArgumentConvergenceLemmas.tendstoUniformlyOn_of_norm_le hβ ?_
      filter_upwards [hev] with t ht y hy using (three t ht y hy).1
    · refine ArgumentConvergenceLemmas.tendstoUniformlyOn_of_norm_le (α := (Fin D → ℂ) →L[ℝ] ℝ) hβ ?_
      filter_upwards [hev] with t ht y hy using (three t ht y hy).2.1
    · refine ArgumentConvergenceLemmas.tendstoUniformlyOn_of_norm_le
        (α := (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) hβ ?_
      filter_upwards [hev] with t ht y hy using (three t ht y hy).2.2

  have hagree : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ thickening (δ / 2) L,
      molli ρ t (w t) (T y) - g y + 4 * e t * H y = Fm t y := by
    filter_upwards [hev, hw Q hQP hQc] with t ht hwt y hy
    have hsub : closedBall (T y) t ⊆ P' := (hmol t ht.1 ht.2 (T y) ⟨y, hUK hy, rfl⟩).1
    have hc : molli ρ t (w t) (T y) = molli ρ t u (T y) :=
      ReciprocityTheory.AnForm.A.molli_congr ρ ht.1 (U := Q) (hsub.trans hP'Q) hwt
    rw [hFm]
    simp only [hc]
  refine ⟨thickening (δ / 2) L, isOpen_thickening, hLU, hfU, ?_, ?_, M, ?_⟩
  · filter_upwards [hev, hagree] with t ht ha
    exact (key t ht).1.congr fun y hy => ha y hy
  · exact TendstoC2On.congr_open isOpen_thickening hLU hagree hmodel
  · filter_upwards [hev, hagree] with t ht ha y hy
    have hE : (fun y' => molli ρ t (w t) (T y') - g y' + 4 * e t * H y') =ᶠ[𝓝 y] Fm t :=
      Filter.eventually_of_mem (isOpen_thickening.mem_nhds (hLU hy)) ha
    rw [hE.fderiv_eq]
    exact (three t ht y hy).2.1

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

open Classical in

theorem regularised_eq_regMax_near (R : RegChartData A) {η : Fin R.N → X → ℝ} {Cη : ℝ}
    (hcut : R.IsCutoffFamily η Cη) (x₀ : X) :
    ∃ N : Set X, IsOpen N ∧ x₀ ∈ N ∧ (∀ j, x₀ ∈ R.mid j → N ⊆ R.mid j) ∧
      ∀ (ρ : Mollifier D) (K t ε : ℝ), 0 ≤ ε →
        (∀ j k, ∀ x ∈ R.mid j ∩ R.mid k, |R.phReg ρ K t j x - R.phReg ρ K t k x| ≤ ε) →
        ∀ y ∈ N, R.regularised ρ K t ε η y =
          regMax ε (fun j : {j // x₀ ∈ R.mid j} => R.phReg ρ K t j y + 4 * ε * η j y) + ε / 2 := by
  choose L hLc hLsub hL using hcut.eq_neg_one
  obtain ⟨N, hN⟩ : ∃ N : Set X, N =
      ⋂ j, (if x₀ ∈ R.mid j then R.mid j else (L j ∪ closure (R.inner j))ᶜ) := ⟨_, rfl⟩
  have hNo : IsOpen N := by
    rw [hN]
    refine isOpen_iInter_of_finite fun j => ?_
    split_ifs
    · exact R.isOpen_mid j
    · exact ((hLc j).union isClosed_closure).isOpen_compl
  have hx₀ : x₀ ∈ N := by
    rw [hN]
    refine mem_iInter.2 fun j => ?_
    split_ifs with h
    · exact h
    · rintro (h1 | h1)
      · exact h (hLsub j h1)
      · exact h (R.closure_inner j h1)
  have hyN : ∀ y ∈ N, ∀ j, (x₀ ∈ R.mid j → y ∈ R.mid j) ∧
      (x₀ ∉ R.mid j → y ∉ L j ∧ y ∉ closure (R.inner j)) := by
    intro y hy j
    rw [hN] at hy
    have := mem_iInter.1 hy j
    constructor
    · intro h
      rwa [if_pos h] at this
    · intro h
      rw [if_neg h] at this
      simpa only [mem_compl_iff, mem_union, not_or] using this
  refine ⟨N, hNo, hx₀, fun j hj y hy => (hyN y hy j).1 hj, ?_⟩
  intro ρ K t ε hε hcmp y hyy
  have hy := hyN y hyy
  simp only [RegChartData.regularised, PotentialCharts.glue]
  refine congrArg (· + ε / 2) ?_
  refine GroundTheory.Heights₂.Heights.Regular.regMax_of_injective
    (fun j : {j // x₀ ∈ R.mid j} => (⟨j.1, (hy j.1).1 j.2⟩ : {j // y ∈ R.mid j}))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) hε _ ?_
  intro i hi
  obtain ⟨k, hk⟩ := R.cover y
  have hk0 : x₀ ∈ R.mid k := by
    by_contra h
    exact ((hy k).2 h).2 (subset_closure hk)
  refine ⟨⟨k, hk0⟩, ?_⟩
  have hi0 : x₀ ∉ R.mid i := fun h => hi ⟨i.1, h⟩ rfl
  have hiL : η i y = -1 := hL i y ⟨i.2, ((hy i).2 hi0).1⟩
  have hk1 : η k y = 0 := hcut.eq_zero k y hk
  have hc := (abs_le.1 (hcmp i k y ⟨i.2, R.inner_subset_mid k hk⟩)).2
  simp only [hiL, hk1]
  linarith

theorem eventually_trunc_eq (R : RegChartData A) {Kt : ℝ → ℝ} (hK : Tendsto Kt (𝓝[>] 0) atTop)
    (i : Fin R.N) {Q : Set (Fin D → ℂ)} (hQ : Q ⊆ (R.chart i).target \ coordDiv (R.S i))
    (hQc : IsCompact Q) : ∀ᶠ t in 𝓝[>] (0 : ℝ), EqOn (R.trunc (Kt t) i) (R.u i) Q := by
  obtain ⟨B, hB⟩ := (hQc.image_of_continuousOn ((R.continuousOn_u i).mono hQ)).bddBelow
  filter_upwards [hK.eventually_ge_atTop (-B)] with t ht y hy
  have h1 : B ≤ R.u i y := hB ⟨y, hy, rfl⟩
  have hyn : y ∉ coordDiv (R.S i) := (hQ hy).2
  simp only [RegChartData.trunc, limsupExt, if_neg hyn]
  exact max_eq_left (by linarith)

theorem arg_C2_on_compact (R : RegChartData A) (ρ : Mollifier D) {η : Fin R.N → X → ℝ} {Cη : ℝ}
    (hcut : R.IsCutoffFamily η Cη) {Kt e : ℝ → ℝ} (hK : Tendsto Kt (𝓝[>] 0) atTop)
    (he : Tendsto e (𝓝[>] 0) (𝓝 0)) (het : ∀ t, 0 < t → t ≤ e t) (i : Fin R.N) (a : Fin A.n)
    {L : Set (Fin D → ℂ)} (hL : IsCompact L)
    (hLs : L ⊆ (A.chart a).target ∩ (A.chart a).symm ⁻¹' (R.Yo ∩ R.mid i)) :
    ∃ U : Set (Fin D → ℂ), IsOpen U ∧ L ⊆ U ∧
      ContDiffOn ℝ 2 (fun y => R.ph ((A.chart a).symm y)) U ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), ContDiffOn ℝ 2 (fun y => R.phReg ρ (Kt t) t i ((A.chart a).symm y) +
        4 * e t * η i ((A.chart a).symm y)) U) ∧
      TendstoC2On (fun t y => R.phReg ρ (Kt t) t i ((A.chart a).symm y) +
        4 * e t * η i ((A.chart a).symm y)) (fun y => R.ph ((A.chart a).symm y)) L ∧
      ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ L,
        ‖fderiv ℝ (fun y' => R.phReg ρ (Kt t) t i ((A.chart a).symm y') +
            4 * e t * η i ((A.chart a).symm y')) y -
          fderiv ℝ (fun y' => R.ph ((A.chart a).symm y')) y‖ ≤ M * (t + e t) := by
  have hO : IsOpen ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (R.Yo ∩ R.mid i)) :=
    (A.chart a).isOpen_inter_preimage_symm (R.isOpen_Yo.inter (R.isOpen_mid i))
  have hP : IsOpen ((R.chart i).target \ coordDiv (R.S i)) :=
    (R.chart i).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have hsrc : ∀ y ∈ (A.chart a).target ∩ (A.chart a).symm ⁻¹' (R.Yo ∩ R.mid i),
      (A.chart a).symm y ∈ (R.chart i).source := fun y hy => R.mid_subset_source i hy.2.2
  have hTO : ContDiffOn ℝ ∞ (fun y => R.chart i ((A.chart a).symm y))
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (R.Yo ∩ R.mid i)) := fun y hy => by
    have h := (((R.compat i) a).1 y ⟨hy.1, hsrc y hy⟩).restrictScalars (𝕜 := ℝ)
    exact h.contDiffAt.contDiffWithinAt
  have hTP : MapsTo (fun y => R.chart i ((A.chart a).symm y))
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (R.Yo ∩ R.mid i))
      ((R.chart i).target \ coordDiv (R.S i)) := fun y hy =>
    ⟨(R.chart i).map_source (hsrc y hy), (R.mem_Yo i _ (hsrc y hy)).1 hy.2.1⟩
  have hu : ContDiffOn ℝ ∞ (R.u i) ((R.chart i).target \ coordDiv (R.S i)) := by
    intro z hz
    refine ContDiffAt.contDiffWithinAt ?_
    have hzs : (R.chart i).symm z ∈ (R.chart i).source := (R.chart i).map_target hz.1
    have h1 := GroundTheory.Heights₂.Heights.Regular.contDiffAt_comp_symm_of_smoothOn (R.compat i)
      R.isOpen_Yo R.ph_smooth (R.symm_mem_Yo i hz.1 hz.2) hzs
    rw [(R.chart i).right_inv hz.1] at h1
    exact ((R.q_smooth i).contDiffAt ((R.chart i).open_target.mem_nhds hz.1)).add h1
  have hf : ContDiffOn ℝ ∞ (fun y => R.ph ((A.chart a).symm y))
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (R.Yo ∩ R.mid i)) :=
    (R.ph_smooth a).mono fun y hy => ⟨hy.1, hy.2.1⟩
  have hg : ContDiffOn ℝ ∞ (fun y => R.q i (R.chart i ((A.chart a).symm y)))
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (R.Yo ∩ R.mid i)) :=
    (R.q_smooth i).comp hTO fun y hy => (hTP hy).1
  have hH : ContDiffOn ℝ ∞ (fun y => η i ((A.chart a).symm y))
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (R.Yo ∩ R.mid i)) :=
    (hcut.smooth i a).mono fun y hy => ⟨hy.1, hy.2.2⟩
  have hfeq : ∀ y ∈ (A.chart a).target ∩ (A.chart a).symm ⁻¹' (R.Yo ∩ R.mid i),
      R.ph ((A.chart a).symm y) = R.u i (R.chart i ((A.chart a).symm y)) -
        R.q i (R.chart i ((A.chart a).symm y)) := by
    intro y hy
    simp only [RegChartData.u, PotentialCharts.chartFun]
    rw [(R.chart i).left_inv (hsrc y hy)]
    ring
  exact arg_C2_through_chart ρ hO hP hL hLs hTO hTP hu hf hg hH hfeq
    (w := fun t => R.trunc (Kt t) i) (fun Q hQ hQc => eventually_trunc_eq R hK i hQ hQc) he het

theorem regularised_C2 (R : RegChartData A) (ρ : Mollifier D) {η : Fin R.N → X → ℝ} {Cη : ℝ}
    (hcut : R.IsCutoffFamily η Cη) {Kt e : ℝ → ℝ} (hK : Tendsto Kt (𝓝[>] 0) atTop)
    (he : Tendsto e (𝓝[>] 0) (𝓝 0)) (het : ∀ t, 0 < t → t ≤ e t)
    (hcmp : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j k, ∀ x ∈ R.mid j ∩ R.mid k,
      |R.phReg ρ (Kt t) t j x - R.phReg ρ (Kt t) t k x| ≤ e t)
    (a : Fin A.n) {C : Set (Fin D → ℂ)} (hC : IsCompact C)
    (hCs : C ⊆ (A.chart a).target ∩ (A.chart a).symm ⁻¹' R.Yo) :
    TendstoC2On (fun t y => R.regularised ρ (Kt t) t (e t) η ((A.chart a).symm y))
      (fun y => R.ph ((A.chart a).symm y)) C := by
  classical
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ 0 < e t := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact ⟨ht, ht.trans_le (het t ht)⟩
  have hloc : ∀ y₀ ∈ C, ∃ r > 0, TendstoC2On
      (fun t y => R.regularised ρ (Kt t) t (e t) η ((A.chart a).symm y))
      (fun y => R.ph ((A.chart a).symm y)) (closedBall y₀ r) := by
    intro y₀ hy₀
    obtain ⟨N, hNo, hx₀, hNmid, hglue⟩ := regularised_eq_regMax_near R hcut ((A.chart a).symm y₀)
    have hO : IsOpen ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (R.Yo ∩ N)) :=
      (A.chart a).isOpen_inter_preimage_symm (R.isOpen_Yo.inter hNo)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO y₀ ⟨(hCs hy₀).1, (hCs hy₀).2, hx₀⟩
    have hLO : closedBall y₀ (r / 2) ⊆ (A.chart a).target ∩ (A.chart a).symm ⁻¹' (R.Yo ∩ N) :=
      (closedBall_subset_ball (by linarith)).trans hball
    refine ⟨r / 2, by positivity, ?_⟩
    have hdata := fun i : {j // (A.chart a).symm y₀ ∈ R.mid j} =>
      arg_C2_on_compact R ρ hcut hK he het i.1 a (isCompact_closedBall y₀ (r / 2))
        (fun y hy => ⟨(hLO hy).1, (hLO hy).2.1, hNmid i.1 i.2 (hLO hy).2.2⟩)
    choose Uj hUo hLU hfC hargC hT M hM using hdata
    obtain ⟨U, hU⟩ : ∃ U : Set (Fin D → ℂ),
        U = ((A.chart a).target ∩ (A.chart a).symm ⁻¹' N) ∩ ⋂ i, Uj i := ⟨_, rfl⟩
    have hUo' : IsOpen U := hU ▸
      ((A.chart a).isOpen_inter_preimage_symm hNo).inter (isOpen_iInter_of_finite hUo)
    have hLU' : closedBall y₀ (r / 2) ⊆ U := fun y hy => by
      rw [hU]
      exact ⟨⟨(hLO hy).1, (hLO hy).2.2⟩, mem_iInter.2 fun i => hLU i hy⟩
    have hUj : ∀ i, U ⊆ Uj i := fun i y hy => by
      rw [hU] at hy
      exact mem_iInter.1 hy.2 i
    have hUN : ∀ y ∈ U, (A.chart a).symm y ∈ N := fun y hy => by
      rw [hU] at hy
      exact hy.1.2
    obtain ⟨Mt, hMt⟩ : ∃ Mt : ℝ, Mt = ∑ i, |M i| := ⟨_, rfl⟩
    have hc : Nonempty {j // (A.chart a).symm y₀ ∈ R.mid j} := inferInstance
    have H := RegularizedMaxConvergenceC2.proof {j // (A.chart a).symm y₀ ∈ R.mid j} U (closedBall y₀ (r / 2))
      (fun y => R.ph ((A.chart a).symm y))
      (fun t i y => R.phReg ρ (Kt t) t i.1 ((A.chart a).symm y) +
        4 * e t * η i.1 ((A.chart a).symm y))
      e (fun t => Mt * (t + e t)) hUo' hLU' ((hfC hc.some).mono (hUj _)) ?ev he hT ?grad ?ratio
    · refine TendstoC2On.congr_open hUo' hLU' ?_ H
      filter_upwards [hpos, hcmp] with t ht hct y hy
      exact hglue ρ (Kt t) t (e t) ht.2.le hct _ (hUN y hy)
    case ev =>
      filter_upwards [hpos, eventually_all.2 fun i => hargC i] with t ht hcd
      exact ⟨ht.2, fun i => (hcd i).mono (hUj i)⟩
    case grad =>
      filter_upwards [hpos, eventually_all.2 fun i => hM i] with t ht hMj i y hy
      have hnn : 0 ≤ t + e t := by linarith [ht.1, ht.2]
      calc _ ≤ M i * (t + e t) := hMj i y hy
        _ ≤ |M i| * (t + e t) := mul_le_mul_of_nonneg_right (le_abs_self _) hnn
        _ ≤ Mt * (t + e t) := mul_le_mul_of_nonneg_right (by
            rw [hMt]
            exact Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg _)
              (Finset.mem_univ i)) hnn
    case ratio =>
      have hK0 : Tendsto (fun t => 4 * Mt ^ 2 * e t) (𝓝[>] 0) (𝓝 0) := by
        simpa using he.const_mul (4 * Mt ^ 2)
      refine squeeze_zero' ?_ ?_ hK0
      · filter_upwards [hpos] with t ht
        exact div_nonneg (sq_nonneg _) ht.2.le
      · filter_upwards [hpos] with t ht
        obtain ⟨ht0, hε⟩ := ht
        rw [div_le_iff₀ hε]
        have h1 : t ≤ e t := het t ht0
        have h2 : 0 ≤ t + e t := by linarith
        have h3 : t + e t ≤ 2 * e t := by linarith
        calc (Mt * (t + e t)) ^ 2 = Mt ^ 2 * (t + e t) ^ 2 := by ring
          _ ≤ Mt ^ 2 * (2 * e t) ^ 2 := by gcongr
          _ = 4 * Mt ^ 2 * e t * e t := by ring
  choose! r hr hTr using hloc
  obtain ⟨T, hTC, hcov⟩ := hC.elim_nhds_subcover (fun y => closedBall y (r y))
    fun y hy => closedBall_mem_nhds y (hr y hy)
  exact ⟨(tendstoUniformlyOn_finset_biUnion T _ fun y hy => (hTr y (hTC y hy)).1).mono hcov,
    (tendstoUniformlyOn_finset_biUnion T _ fun y hy => (hTr y (hTC y hy)).2.1).mono hcov,
    (tendstoUniformlyOn_finset_biUnion T _ fun y hy => (hTr y (hTC y hy)).2.2).mono hcov⟩

theorem regWeight_tendsto_C2_of_tied :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B), S.IsTied → ∀ j, ∀ K' ⊆ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => S.regWeight t ∘ (M.atlas.chart j).symm) (S.R.ph ∘ (M.atlas.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (S.regWeight t ∘ (M.atlas.chart j).symm)) (fderiv ℝ (S.R.ph ∘ (M.atlas.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (S.regWeight t ∘ (M.atlas.chart j).symm))) (fderiv ℝ (fderiv ℝ (S.R.ph ∘ (M.atlas.chart j).symm))) (𝓝[>] 0) K' := by
  intro K _ ι _ P n M Xo B S hS j K' hK's hK'c
  have h := regularised_C2 S.R S.ρ S.cutoff hS.K_tendsto hS.e1_tendsto_zero S.e1_ge hS.compare j hK'c hK's
  exact ⟨h.1, h.2.1, h.2.2⟩

end

end GlobalTheory.CompanionTheory.Ar.Giv
