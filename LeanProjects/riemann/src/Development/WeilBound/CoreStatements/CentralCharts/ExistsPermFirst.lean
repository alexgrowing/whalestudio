import Development.WeilBound.CoreStatements.CentralCharts.PshAt0
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSncAdaptedChartAtPointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedChartSectionFormStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositive
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl

noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.PB

variable {n : ℕ} {X : Type} [TopologicalSpace X]

theorem holoAt_compat {A : FinHolAtlas n X} {ψ : OpenPartialHomeomorph X (Fin n → ℂ)} (hψ : IsCompatChart A ψ)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {t : Fin n → ℂ} (ht : t ∈ ψ.target) (hU : ψ.symm t ∈ U) :
    AnalyticAt ℂ (fun t' => g (ψ.symm t')) t := by
  obtain ⟨j, hj⟩ := A.cover (ψ.symm t)
  have h1 : AnalyticAt ℂ (A.chart j ∘ ψ.symm) t := (hψ j).2 t ⟨ht, hj⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) t) := by
    refine hg j _ ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (A.chart j).left_inv hj]
    exact hU
  refine (h2.comp h1).congr ?_
  filter_upwards [(ψ.continuousAt_symm ht).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)] with t' ht'
  have h3 : ψ.symm t' ∈ (A.chart j).source := ht'
  simp only [Function.comp, (A.chart j).left_inv h3]

def NChart (A : FinHolAtlas n X) (U : Set X) (L : LocPot X) (s : X → X → ℂ) (x₀ : X)
    (ψ : OpenPartialHomeomorph X (Fin n → ℂ)) (a : ℕ) (M : ℝ) : Prop :=
  IsCompatChart A ψ ∧ x₀ ∈ ψ.source ∧ ψ x₀ = 0 ∧ a ≤ n ∧ ∀ t ∈ ball (0 : Fin n → ℂ) 1, t ∈ ψ.target ∧ ψ.symm t ∈ U ∧
    (ψ.symm t ∈ bdry s ↔ ∃ i : Fin n, (i : ℕ) < a ∧ t i = 0) ∧
    (ψ.symm t ∉ bdry s → logR a t ≤ rW L s (ψ.symm t) + M)

theorem exists_perm_first (S : Finset (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, i ∈ S ↔ ((σ i : Fin n) : ℕ) < S.card := by
  classical
  have hle : S.card ≤ n := by simpa using S.card_le_univ
  have hcard : Fintype.card {i : Fin n // i ∈ S} = Fintype.card {i : Fin n // (i : ℕ) < S.card} := by
    rw [Fintype.card_coe, ← Fintype.card_congr (Fin.castLEquiv hle), Fintype.card_fin]
  have hcard' : Fintype.card {i : Fin n // ¬ i ∈ S} = Fintype.card {i : Fin n // ¬ (i : ℕ) < S.card} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard]
  let e := Fintype.equivOfCardEq hcard
  let f := Fintype.equivOfCardEq hcard'
  refine ⟨Equiv.subtypeCongr e f, fun i => ?_⟩
  by_cases hi : i ∈ S
  · have h1 : Equiv.subtypeCongr e f i = e ⟨i, hi⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hi]
    rw [h1]
    exact ⟨fun _ => (e ⟨i, hi⟩).2, fun _ => hi⟩
  · have h1 : Equiv.subtypeCongr e f i = f ⟨i, hi⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_neg hi]
    rw [h1]
    exact ⟨fun h => absurd h hi, fun h => absurd h (f ⟨i, hi⟩).2⟩

def scalePerm (δ : ℝ) (hδ : 0 < δ) (σ : Equiv.Perm (Fin n)) : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun t i => (δ : ℂ) * t (σ i)
      invFun := fun y i => (δ : ℂ)⁻¹ * y (σ.symm i)
      map_add' := fun t t' => by funext i; simp [mul_add]
      map_smul' := fun c t => by funext i; simp; ring
      left_inv := fun t => by
        have h : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
        funext i; simp [h]
      right_inv := fun t => by
        have h : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
        funext i; simp [h] }

theorem scalePerm_apply (δ : ℝ) (hδ : 0 < δ) (σ : Equiv.Perm (Fin n)) (t : Fin n → ℂ) (i : Fin n) :
    scalePerm δ hδ σ t i = (δ : ℂ) * t (σ i) := rfl

theorem exists_nchart (A : FinHolAtlas n X) (L : LocPot X) (s : X → X → ℂ) {nb : ℕ} {m : Fin nb → ℕ}
    {W : Fin nb → Set X} (hL : IsPotential A L) (hs : IsSection A L s) (snc : IsSNC A L s m W) (x₀ : X) (U : Set X)
    (hU : IsOpen U) (hx : x₀ ∈ U) : ∃ ψ a M, NChart A U L s x₀ ψ a M := by
  classical
  obtain ⟨φ, S, μ, v, hφ, hx0, hball2, hφ0, hsrc, hμ, hv, hv0, hsv⟩ :=
    GlobalTheory.T.exists_snc_adapted_chart_at_point n X A L s nb m W snc x₀
  obtain ⟨hbd, M, hM⟩ := GlobalTheory.T.snc_adapted_chart_section_form n X A L s hL hs x₀ φ S μ v hφ hball2 hsrc hμ hv hv0 hsv
  have h0t : (0 : Fin n → ℂ) ∈ φ.target := hball2 (by simp)
  have hs0 : φ.symm 0 = x₀ := by rw [← hφ0]; exact φ.left_inv hx0
  have hnhds : φ.target ∩ φ.symm ⁻¹' U ∈ 𝓝 (0 : Fin n → ℂ) := by
    refine Filter.inter_mem (φ.open_target.mem_nhds h0t) ?_
    exact (φ.continuousAt_symm h0t).preimage_mem_nhds (by rw [hs0]; exact hU.mem_nhds hx)
  obtain ⟨δ', hδ', hδball⟩ := Metric.mem_nhds_iff.1 hnhds
  have hδ : 0 < min δ' 1 := lt_min hδ' one_pos
  have hδ1 : min δ' 1 ≤ 1 := min_le_right _ _
  have hδδ' : min δ' 1 ≤ δ' := min_le_left _ _
  obtain ⟨σ, hσ⟩ := exists_perm_first S
  let Lδ := scalePerm (min δ' 1) hδ σ
  let ψ := φ.transHomeomorph Lδ.toHomeomorph.symm
  have hψs : ∀ t, ψ.symm t = φ.symm (Lδ t) := fun t => rfl
  have hψ : ∀ x, ψ x = Lδ.symm (φ x) := fun x => rfl
  have hψtgt : ∀ t, t ∈ ψ.target ↔ Lδ t ∈ φ.target := fun t => Iff.rfl
  have hnorm : ∀ t : Fin n → ℂ, ‖t‖ < 1 → ‖Lδ t‖ < min δ' 1 := by
    intro t ht
    refine (pi_norm_lt_iff hδ).2 fun i => ?_
    rw [scalePerm_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le]
    have : ‖t (σ i)‖ < 1 := (norm_le_pi_norm t (σ i)).trans_lt ht
    nlinarith [norm_nonneg (t (σ i))]
  refine ⟨ψ, S.card, M, ?_, ?_, ?_, by simpa using S.card_le_univ, ?_⟩
  · intro j
    constructor
    · intro y hy
      have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' φ.source := hy
      exact ((Lδ.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)).analyticAt _).comp ((hφ j).1 y hy')
    · intro y hy
      have hy' : Lδ y ∈ φ.target ∩ φ.symm ⁻¹' (A.chart j).source := hy
      exact ((hφ j).2 _ hy').comp ((Lδ : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)).analyticAt y)
  · exact hx0
  · rw [hψ, hφ0, map_zero]
  · intro t ht
    have ht1 : ‖t‖ < 1 := by simpa using ht
    have hz : ‖Lδ t‖ < min δ' 1 := hnorm t ht1
    have hzb : Lδ t ∈ ball (0 : Fin n → ℂ) δ' := by simpa using hz.trans_le hδδ'
    have hzmem := hδball hzb
    have hz2 : Lδ t ∈ closedBall (0 : Fin n → ℂ) 2 := by
      rw [mem_closedBall_zero_iff]; linarith
    have hzero : ∀ i, Lδ t i = 0 ↔ t (σ i) = 0 := by
      intro i
      rw [scalePerm_apply]
      simp [hδ.ne']
    have hbdry : ψ.symm t ∈ bdry s ↔ ∃ i : Fin n, (i : ℕ) < S.card ∧ t i = 0 := by
      rw [hψs, hbd _ hzmem.1]
      constructor
      · rintro ⟨i, hi, h0⟩
        exact ⟨σ i, (hσ i).1 hi, (hzero i).1 h0⟩
      · rintro ⟨j, hj, h0⟩
        exact ⟨σ.symm j, (hσ _).2 (by simpa using hj), (hzero _).2 (by simpa using h0)⟩
    refine ⟨(hψtgt t).2 hzmem.1, by rw [hψs]; exact hzmem.2, hbdry, ?_⟩
    intro hnb
    have hall : ∀ i ∈ S, t (σ i) ≠ 0 := fun i hi h0 => hnb (hbdry.2 ⟨σ i, (hσ i).1 hi, h0⟩)
    have hrw : |rW L s (ψ.symm t) - rLoc S μ (Lδ t)| ≤ M := hM _ hz2 hnb
    have hloc : logR S.card t ≤ rLoc S μ (Lδ t) := by
      unfold logR rLoc
      have hsum : (∑ i : Fin n, if (i : ℕ) < S.card then Real.log (1 / ‖t i‖ ^ 2) else 0) =
          ∑ i ∈ S, Real.log (1 / ‖t (σ i)‖ ^ 2) := by
        calc (∑ i : Fin n, if (i : ℕ) < S.card then Real.log (1 / ‖t i‖ ^ 2) else 0)
            = ∑ i : Fin n, (if ((σ i : Fin n) : ℕ) < S.card then Real.log (1 / ‖t (σ i)‖ ^ 2) else 0) :=
              (Equiv.sum_comp σ (fun i : Fin n =>
                if (i : ℕ) < S.card then Real.log (1 / ‖t i‖ ^ 2) else 0)).symm
          _ = ∑ i : Fin n, (if i ∈ S then Real.log (1 / ‖t (σ i)‖ ^ 2) else 0) :=
              Finset.sum_congr rfl fun i _ => by
                by_cases hi : i ∈ S
                · rw [if_pos ((hσ i).1 hi), if_pos hi]
                · rw [if_neg (fun h => hi ((hσ i).2 h)), if_neg hi]
          _ = ∑ i ∈ S, Real.log (1 / ‖t (σ i)‖ ^ 2) := by
              rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [hsum]
      gcongr with i hi
      have hx : 0 < ‖t (σ i)‖ := norm_pos_iff.2 (hall i hi)
      have hx1 : ‖t (σ i)‖ < 1 := (norm_le_pi_norm t (σ i)).trans_lt ht1
      have hLi : ‖Lδ t i‖ = min δ' 1 * ‖t (σ i)‖ := by
        rw [scalePerm_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le]
      have hpos : 0 < min δ' 1 * ‖t (σ i)‖ := mul_pos hδ hx
      have hA : 0 ≤ Real.log (1 / ‖t (σ i)‖ ^ 2) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have hB : Real.log (1 / ‖t (σ i)‖ ^ 2) ≤ Real.log (4 / ‖Lδ t i‖ ^ 2) := by
        rw [hLi]
        apply Real.log_le_log (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : min δ' 1 ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg ‖t (σ i)‖]
      have hμ1 : (1 : ℝ) ≤ μ i := by exact_mod_cast hμ i hi
      nlinarith
    have := (abs_le.1 hrw).1
    linarith

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem not_mem_top (z : (Σ k, J k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing J)) := by
  intro h
  have := h.2 1 trivial
  simp at this

theorem analyticAt_lift {P Q : Ideal (MRing J)} (R : AnLogRes P Q n) {ψ : OpenPartialHomeomorph R.X (Fin n → ℂ)}
    (hψ : IsCompatChart R.A ψ) (x₀ : R.X) {t : Fin n → ℂ} (ht : t ∈ ψ.target) (hU : ψ.symm t ∈ R.U x₀) :
    AnalyticAt ℂ (fun t' => R.lift x₀ (ψ.symm t')) t :=
  analyticAt_pi_iff.2 fun q => holoAt_compat hψ (R.holo x₀ q) ht hU

def NChart.snc {P : Ideal (MRing J)} (R : AnLogRes P ⊤ n) {L : LocPot R.X} {s : R.X → R.X → ℂ} {x₀ : R.X}
    {ψ : OpenPartialHomeomorph R.X (Fin n → ℂ)} {a : ℕ} {M : ℝ} (h : NChart R.A (R.U x₀) L s x₀ ψ a M)
    (Bd : Set ((Σ k, J k) → ℂ)) (hBd : ∀ x ∈ R.U x₀, R.lift x₀ x ∈ Bd ↔ x ∈ bdry s) : SncChart P n Bd where
  γ t := R.lift x₀ (ψ.symm t)
  a := a
  a_le := h.2.2.2.1
  analytic t ht := analyticAt_lift R h.1 x₀ (h.2.2.2.2 t ht).1 (h.2.2.2.2 t ht).2.1
  mem t ht := R.mem _ _ (h.2.2.2.2 t ht).2.1
  immersion t ht v := by
    rintro ⟨c, hc⟩
    obtain ⟨htt, hxU, -⟩ := h.2.2.2.2 t ht
    have hγ := analyticAt_lift R h.1 x₀ htt hxU
    obtain ⟨j, hj⟩ := R.A.cover (ψ.symm t)
    choose p hp using (R.mem _ _ (R.mem_U (ψ.symm t))).1
    have himm := R.immersion _ (not_mem_top _) p hp j hj
    have hpγ : ∀ k, R.lift x₀ (ψ.symm t) ⟨k, p k⟩ ≠ 0 := by
      intro k
      obtain ⟨c', hc', h'⟩ := R.compat _ x₀ _ ⟨R.mem_U _, hxU⟩
      have := hp k
      rw [h'] at this
      exact right_ne_zero_of_mul this
    have hk := PosFs.fderiv_affCoord_torus p hγ.differentiableAt hpγ hc
    have hτ : AnalyticAt ℂ (R.A.chart j ∘ ψ.symm) t := (h.1 j).2 t ⟨htt, hj⟩
    have hF : DifferentiableAt ℂ (fun y => affCoord p (R.lift (ψ.symm t) ((R.A.chart j).symm y)))
        ((R.A.chart j ∘ ψ.symm) t) := by
      refine differentiableAt_pi.2 fun q => ?_
      have hmem : (R.A.chart j) (ψ.symm t) ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U (ψ.symm t) :=
        ⟨(R.A.chart j).map_source hj, by
          simp only [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact R.mem_U _⟩
      have hd := (R.holo _ q j _ hmem).div (R.holo _ ⟨q.1, p q.1⟩ j _ hmem) (by
        simp only [Function.comp, (R.A.chart j).left_inv hj]
        exact hp q.1)
      exact hd.differentiableAt
    have hev : (fun t' => affCoord p (R.lift x₀ (ψ.symm t'))) =ᶠ[𝓝 t]
        (fun y => affCoord p (R.lift (ψ.symm t) ((R.A.chart j).symm y))) ∘ (R.A.chart j ∘ ψ.symm) := by
      filter_upwards [(ψ.continuousAt_symm htt).preimage_mem_nhds
        ((((R.isOpen_U x₀).inter (R.isOpen_U (ψ.symm t))).inter (R.A.chart j).open_source).mem_nhds
          ⟨⟨hxU, R.mem_U _⟩, hj⟩)] with t' ht'
      obtain ⟨c', hc', h'⟩ := R.compat x₀ (ψ.symm t) _ ht'.1
      have h3 : ψ.symm t' ∈ (R.A.chart j).source := ht'.2
      funext q
      simp only [affCoord, Function.comp, (R.A.chart j).left_inv h3]
      rw [h']
      exact mul_div_mul_left _ _ (hc' q.1)
    rw [hev.fderiv_eq, fderiv_comp t hF hτ.differentiableAt] at hk
    have hmem : fderiv ℂ (R.A.chart j ∘ ψ.symm) t v ∈
        (fderiv ℂ (fun y => affCoord p (R.lift (ψ.symm t) ((R.A.chart j).symm y))) (R.A.chart j (ψ.symm t))).ker := hk
    rw [himm] at hmem
    have h0 : fderiv ℂ (R.A.chart j ∘ ψ.symm) t v = 0 := (Submodule.mem_bot _).1 hmem
    have hσ : AnalyticAt ℂ (ψ ∘ (R.A.chart j).symm) ((R.A.chart j ∘ ψ.symm) t) :=
      (h.1 j).1 _ ⟨(R.A.chart j).map_source hj, by
        simp only [Set.mem_preimage, Function.comp, (R.A.chart j).left_inv hj]; exact ψ.map_target htt⟩
    have hid : (ψ ∘ (R.A.chart j).symm) ∘ (R.A.chart j ∘ ψ.symm) =ᶠ[𝓝 t] id := by
      filter_upwards [(ψ.continuousAt_symm htt).preimage_mem_nhds ((R.A.chart j).open_source.mem_nhds hj),
        ψ.open_target.mem_nhds htt] with t' h1 h2
      have h3 : ψ.symm t' ∈ (R.A.chart j).source := h1
      simp only [Function.comp, (R.A.chart j).left_inv h3, ψ.right_inv h2, id]
    have hcc := fderiv_comp t hσ.differentiableAt hτ.differentiableAt
    rw [hid.fderiv_eq, fderiv_id] at hcc
    have := congrArg (fun f : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => f v) hcc
    simpa [h0] using this
  injective t ht t' ht' c hc he := by
    obtain ⟨h1, h2, -⟩ := h.2.2.2.2 t ht
    obtain ⟨h1', h2', -⟩ := h.2.2.2.2 t' ht'
    have o : SameOrbit (R.lift x₀ (ψ.symm t)) (R.lift x₀ (ψ.symm t')) := ⟨c, hc, he⟩
    have := R.inj (ψ.symm t) (ψ.symm t') (not_mem_top _)
      (Cj.sameOrbit_trans (R.compat _ x₀ _ ⟨R.mem_U _, h2⟩) (Cj.sameOrbit_trans o (R.compat x₀ _ _ ⟨h2', R.mem_U _⟩)))
    rw [← ψ.right_inv h1, this, ψ.right_inv h1']
  boundary t ht := (hBd _ (h.2.2.2.2 t ht).2.1).trans (h.2.2.2.2 t ht).2.2.1

end AnalyticReference.An
