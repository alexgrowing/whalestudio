import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.LocalForm

theorem holoOn_coord {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (i : Fin e) :
    A.HoloOn ψ.source (fun y => ψ y i) := by
  intro j z hz
  exact (analyticAt_pi_iff.1 ((hψ j).1 z hz)) i

theorem exists_local_form : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSNC A L s m W → ∀ x, ∃ (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ ∧ x ∈ φ.source ∧ Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target ∧ φ x = 0 ∧ φ.source ⊆ L.U x ∧ (∀ i ∈ S, 1 ≤ μ i) ∧ A.HoloOn φ.source v ∧ (∀ y ∈ φ.source, v y ≠ 0) ∧ ∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i := by
  intro e X _ A L s nb m W hsnc x
  obtain ⟨ψ, hψ, hxψ, hψU, σ, hinj, -, u, hu, hu0, hs⟩ := hsnc x
  obtain ⟨c, hc⟩ : ∃ c, c = ψ x := ⟨_, rfl⟩
  have hev : ∀ᶠ z in 𝓝 c, z ∈ ψ.target ∧ ∀ i, c i ≠ 0 → z i ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 c, z ∈ ψ.target := ψ.open_target.mem_nhds (hc ▸ ψ.map_source hxψ)
    refine h1.and ?_
    rw [eventually_all]
    intro i
    by_cases h : c i = 0
    · simp [h]
    · filter_upwards [((continuous_apply i).continuousAt (x := c)).eventually_ne h] with z hz _
      exact hz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hV : IsOpen (ψ.source ∩ ψ ⁻¹' Metric.ball c r) :=
    ψ.continuousOn.isOpen_inter_preimage ψ.open_source Metric.isOpen_ball
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have ha : (3 / r : ℂ) ≠ 0 := by simpa using hrC
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (ψ.restrOpen _ hV).transHomeomorph (pa_aff (3 / r : ℂ) ha c) := ⟨_, rfl⟩
  have hφc : IsCompatChart A φ := hφ ▸ pa_compat_aff A _ (pa_compat_restr A _ hψ _ hV) _ ha _
  have hsrc : ∀ y ∈ φ.source, y ∈ ψ.source ∧ ψ y ∈ Metric.ball c r := by
    intro y hy
    subst hφ
    exact ⟨hy.1, hy.2.2⟩
  have hφapp : ∀ y, φ y = (3 / r : ℂ) • (ψ y - c) := by
    intro y
    subst hφ
    rfl
  have hxφ : x ∈ φ.source := by
    subst hφ
    refine ⟨hxψ, hxψ, ?_⟩
    show ψ x ∈ Metric.ball c r
    rw [← hc]
    exact Metric.mem_ball_self hr
  have htarget : Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target := by
    intro z hz
    subst hφ
    set w : Fin e → ℂ := (3 / r : ℂ)⁻¹ • z + c with hw
    have hwb : w ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, hw, add_sub_cancel_right, norm_smul]
      have hz' : ‖z‖ ≤ 2 := by simpa using hz
      have : ‖(3 / r : ℂ)⁻¹‖ = r / 3 := by
        rw [norm_inv, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
        norm_num
      rw [this]
      nlinarith
    have hwT : w ∈ ψ.target := (hball _ hwb).1
    have hmem : w ∈ (ψ.restrOpen _ hV).target :=
      ⟨hwT, ψ.map_target hwT, by simpa [ψ.right_inv hwT] using hwb⟩
    exact hmem

  let g : Fin nb → X → ℂ := fun k y => (σ k).elim 1 (fun i => ψ y i ^ m k)
  have hg : ∀ k y, (match σ k with
      | some i => ψ y i ^ m k
      | none => 1) = g k y := by
    intro k y
    simp only [g]
    cases σ k <;> rfl
  have hgholo : ∀ k, A.HoloOn ψ.source (g k) := by
    intro k j z hz
    simp only [g]
    cases σ k with
    | none => exact analyticAt_const
    | some i => exact (holoOn_coord A ψ hψ i j z hz).pow (m k)
  let K : Finset (Fin nb) := Finset.univ.filter (fun k => ∃ i, σ k = some i ∧ c i = 0 ∧ 1 ≤ m k)
  let S : Finset (Fin e) := Finset.univ.filter (fun i => c i = 0 ∧ ∃ k, σ k = some i ∧ 1 ≤ m k)
  let μ : Fin e → ℕ := fun i => ∑ k, if σ k = some i then m k else 0
  have hμ : ∀ k i, σ k = some i → μ i = m k := by
    intro k i hk
    refine (Finset.sum_eq_single k (fun b _ hb => if_neg fun h => hb (hinj _ _ i h hk))
      (by simp)).trans (if_pos hk)
  have hKS : ∀ y, ∏ k ∈ K, g k y = ∏ i ∈ S, ψ y i ^ μ i := by
    intro y
    refine Finset.prod_bij (fun k hk => Classical.choose (Finset.mem_filter.1 hk).2) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2, k, h1, h3⟩
    · intro k hk k' hk' hkk
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      obtain ⟨h1', -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk').2
      exact hinj k k' _ h1 (hkk ▸ h1')
    · intro i hi
      obtain ⟨-, h0, k, hk, hm⟩ := Finset.mem_filter.1 hi
      have hkK : k ∈ K := Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hk, h0, hm⟩
      refine ⟨k, hkK, ?_⟩
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hkK).2
      exact Option.some.inj (h1.symm.trans hk)
    · intro k hk
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      have key : ∀ i, σ k = some i → g k y = ψ y i ^ μ i := by
        intro i hi
        simp only [g]
        rw [hi, hμ k i hi]
        rfl
      exact key _ h1
  let T : Finset (Fin nb) := Finset.univ.filter
    (fun k => ¬ ∃ i, σ k = some i ∧ c i = 0 ∧ 1 ≤ m k)
  let C : ℂ := ((r : ℂ) / 3) ^ (∑ i ∈ S, μ i)
  have hC : C ≠ 0 := pow_ne_zero _ (div_ne_zero hrC (by norm_num))
  refine ⟨φ, S, μ, fun y => u y * C * ∏ k ∈ T, g k y, hφc, hxφ, htarget, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφapp, ← hc, sub_self, smul_zero]
  · exact fun y hy => hψU (hsrc y hy).1
  · intro i hi
    obtain ⟨-, -, k, hk, hm⟩ := Finset.mem_filter.1 hi
    rw [hμ k i hk]
    exact hm
  · intro j z hz
    have hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source := ⟨hz.1, (hsrc _ hz.2).1⟩
    exact ((hu j z hz').mul analyticAt_const).mul
      (Finset.analyticAt_fun_prod _ fun k _ => hgholo k j z hz')
  · intro y hy
    obtain ⟨hy1, hy2⟩ := hsrc y hy
    refine mul_ne_zero (mul_ne_zero (hu0 y hy1) hC) (Finset.prod_ne_zero_iff.2 ?_)
    intro k hk
    have hk' := (Finset.mem_filter.1 hk).2
    simp only [g]
    cases hσ : σ k with
    | none => exact one_ne_zero
    | some i =>
      by_cases hm : m k = 0
      · simp [hm]
      · have hci : c i ≠ 0 := fun h0 => hk' ⟨i, hσ, h0, Nat.one_le_iff_ne_zero.2 hm⟩
        exact pow_ne_zero _ ((hball _ hy2).2 i hci)
  · intro y hy
    obtain ⟨hy1, -⟩ := hsrc y hy
    have hcoord : ∀ i ∈ S, ψ y i = ((r : ℂ) / 3) * φ y i := by
      intro i hi
      obtain ⟨-, h0, -⟩ := Finset.mem_filter.1 hi
      rw [hφapp]
      simp only [Pi.smul_apply, Pi.sub_apply, h0, sub_zero, smul_eq_mul]
      field_simp
    have hsplit : ∏ k, g k y = (∏ k ∈ K, g k y) * ∏ k ∈ T, g k y :=
      (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have hmono : ∏ i ∈ S, ψ y i ^ μ i = C * ∏ i ∈ S, φ y i ^ μ i := by
      rw [Finset.prod_congr rfl (fun i hi => by rw [hcoord i hi, mul_pow]),
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have h2 : s x y = u y * ∏ k, g k y := by
      rw [hs y hy1]
      congr 1
      exact Finset.prod_congr rfl (fun k _ => hg k y)
    show s x y = u y * C * (∏ k ∈ T, g k y) * ∏ i ∈ S, φ y i ^ μ i
    rw [h2, hsplit, hKS, hmono]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.LocalForm
