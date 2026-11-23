import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsKerProjStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartWSaturatedAndContinuousSectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartWOfContinuousPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentSpanRelIndexCriterionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousChangeOfFrameStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetMulNormSqDetStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetImEqZeroStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFamilyInIdealOfIsOFamilyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NzEqNzOfAndPosStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetPosOfSemidefiniteTransversalStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentAppendIndependentSpanStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQHermitianAndRealPairingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQContinuousAtAndLocalSolutionStatement

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit

theorem contAt_act {E : Type} [Field E] [NumberField E] [IsCMField E] {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (L : ActPeriods E n a g Λ) (c' : 𝓞 E) (t : (Fin n → ℂ) → Fin g → ℂ) (ht : ContinuousAt t 0) :
    ContinuousAt (fun z => L.B z c' (t z)) 0 := by
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have e : (fun z => L.B z c' (t z)) = fun z => ∑ i, t z i • L.B z c' (Pi.single i 1) := by
    funext z
    conv_lhs => rw [pi_eq_sum_univ' (t z)]
    simp only [map_sum, map_smul]
  rw [e]
  refine tendsto_finset_sum _ fun i _ => ?_
  have h1 : ContinuousAt (fun z => L.B z c' (Pi.single i 1)) 0 :=
    (L.B_hol c' _).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  exact ((continuous_apply i).continuousAt.comp ht).smul h1

theorem li_of_det {g m : ℕ} (u f : Fin m → Fin g → ℂ) (T : Matrix (Fin m) (Fin m) ℂ) (hu : LinearIndependent ℂ u)
    (hf : ∀ i, f i = ∑ j, T j i • u j) (hd : T.det ≠ 0) : LinearIndependent ℂ f := by
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro l hl i
  have h1 : ∑ j, (T *ᵥ l) j • u j = 0 := by
    rw [← hl]
    simp only [hf, Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have h2 : T *ᵥ l = 0 := funext (hu _ h1)
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hd h2) i

theorem contAt_form {n g : ℕ} (u u' : (Fin n → ℂ) → Fin g → ℂ) (Q : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (hu : ContinuousAt u 0) (hu' : ContinuousAt u' 0) (hQ : ContinuousAt Q 0) :
    ContinuousAt (fun z => u z ⬝ᵥ Q z *ᵥ star (u' z)) 0 := by
  have hc : Continuous (fun t : (Fin g → ℂ) × Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
      t.1 ⬝ᵥ t.2.1 *ᵥ star t.2.2) :=
    continuous_fst.dotProduct ((continuous_fst.comp continuous_snd).matrix_mulVec
      (continuous_star.comp (continuous_snd.comp continuous_snd)))
  exact ContinuousAt.comp (f := fun z => (u z, Q z, u' z)) hc.continuousAt (hu.prodMk (hQ.prodMk hu'))

theorem limit_of_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (L : ActPeriods E n a g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ) (W I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (s : W → (Fin n → ℂ) → Fin g → ℂ) (Hb : Matrix (Fin g) (Fin g) ℂ) (Qm : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ : ℝ), IsCMFam σ → IsEigFrames (Metric.ball 0 1) L.B σ b → I ≤ W → (∀ x ∈ I, ∀ y ∈ I, L.toLogPeriods.E x y = 0) → Function.Injective per → (∀ (c : 𝓞 E) (x : W), per (c • x) = L.B 0 c (per x)) → (∀ x : W, ContinuousAt (s x) 0 ∧ s x 0 = per x ∧ ∀ w ∈ logCover L.a_le, s x (expCover a w) = L.P w x) → Hb.IsHermitian → (∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x})) → ContinuousAt Qm 0 → Qm 0 = Hb → 0 < ρ → (∀ w ∈ logCover L.a_le, ‖expCover a w‖ < ρ → ∀ y : Fin g → ℂ, ∃ p : Fin g → ℂ, p - y ∈ Submodule.span ℂ (L.P w '' (I : Set Λ)) ∧ (∀ x ∈ I, p ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w x) = 0) ∧ ∀ y' : Fin g → ℂ, y' ⬝ᵥ L.H (expCover a w) *ᵥ star p = y' ⬝ᵥ Qm (expCover a w) *ᵥ star y) → ∀ ν : ℝ, PhiNormSq (L.B 0) (fun x y => y ⬝ᵥ Hb *ᵥ star x) (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) 1 σ (fun τ i => b τ i 0) ν → 0 < ν ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < δ → |(L.riem w hw).logDet (fun τ i => b τ i (expCover a w)) - Real.log ((L.riem w hw).nz σ I) - Real.log ν| < ε := by
  intro E _ _ _ n a g Λ _ _ Ψ _ L σ m b W I per s Hb Qm ρ hσ hb hIW hiso hinj hact hs hHerm hpos hQc hQ0 hρ hrep ν hν
  classical
  obtain ⟨r, k, rfl, v, q, T, hfam, hq, hT, hdet, hνeq⟩ := hν
  simp only [Fin.cast_eq_self] at hT
  obtain ⟨y, hyI, hyv, hyli, hidx⟩ := GlobalTheory.T.exists_family_in_ideal_of_isOFamily E g Λ W I per (L.B 0) r v hIW hinj hact hfam
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  choose cf hcf using fun τ => GlobalTheory.T.exists_eigenComponent_polynomial E (σ τ)
  let f : Ψ → (Fin n → ℂ) → Fin r → Fin g → ℂ := fun τ z a => eigComp (L.B z) (σ τ) (s (y a) z)
  let qt : Ψ → (Fin n → ℂ) → Fin k → Fin g → ℂ := fun τ z c => ∑ j, T τ j (Fin.natAdd r c) • b τ j z
  let F : Ψ → (Fin n → ℂ) → Fin (r + k) → Fin g → ℂ := fun τ z => Fin.append (f τ z) (qt τ z)
  have hbc : ∀ τ j, ContinuousAt (b τ j) 0 := fun τ j =>
    (hb.1 τ j).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  have hfc : ∀ τ a, ContinuousAt (fun z => f τ z a) 0 := by
    intro τ a'
    have e : (fun z => f τ z a') = fun z => ∑ e ∈ (cf τ).support, cf τ e • L.B z e (s (y a') z) := by
      funext z
      exact ((hcf τ) (Fin g → ℂ) (L.B z)).1 _
    rw [e]
    refine tendsto_finset_sum _ fun e _ => ?_
    exact (contAt_act L e _ (hs (y a')).1).tendsto.const_smul _
  have hqc : ∀ τ c, ContinuousAt (fun z => qt τ z c) 0 := fun τ c =>
    tendsto_finset_sum _ fun j _ => (hbc τ j).tendsto.const_smul _
  have hFc : ∀ τ i, ContinuousAt (fun z => F τ z i) 0 := by
    intro τ i
    refine Fin.addCases (fun a' => ?_) (fun c => ?_) i
    · simpa only [F, Fin.append_left] using hfc τ a'
    · simpa only [F, Fin.append_right] using hqc τ c
  have hf0 : ∀ τ a', f τ 0 a' = eigComp (L.B 0) (σ τ) (v a') := by
    intro τ a'
    simp only [f, (hs (y a')).2.1, hyv]
  have hqt0 : ∀ τ c, qt τ 0 c = q τ c := by
    intro τ c
    have := hT τ (Fin.natAdd r c)
    rw [Fin.append_right] at this
    exact this.symm
  have hF0 : ∀ τ, F τ 0 = Fin.append (fun a' => eigComp (L.B 0) (σ τ) (v a')) (q τ) := by
    intro τ
    simp only [F]
    congr 1
    · exact funext (hf0 τ)
    · exact funext (hqt0 τ)
  have hsol := fun τ => GlobalTheory.T.exists_continuous_change_of_frame n g (r + k) (fun z i => b τ i z) (F τ) (T τ) (fun i => hbc τ i) (hFc τ)
    ((hb.2 0 h0ball τ).1) (fun i => by rw [hF0 τ]; exact hT τ i) (by
      filter_upwards [Metric.isOpen_ball.mem_nhds h0ball] with z hz i
      rw [(hb.2 z hz τ).2]
      refine Fin.addCases (fun a' => ?_) (fun c => ?_) i
      · simp only [F, Fin.append_left]
        exact ((hcf τ) (Fin g → ℂ) (L.B z)).2.1 _
      · simp only [F, Fin.append_right]
        rw [← (hb.2 z hz τ).2]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  choose Tt hTc hT0 hTe using hsol
  let Qd : Ψ → (Fin n → ℂ) → ℂ := fun τ z => (Matrix.of fun c c' => qt τ z c' ⬝ᵥ Qm z *ᵥ star (qt τ z c)).det
  have hQdc : ∀ τ, ContinuousAt (Qd τ) 0 := by
    intro τ
    have hM : ContinuousAt (fun z => (Matrix.of fun c c' => qt τ z c' ⬝ᵥ Qm z *ᵥ star (qt τ z c) :
        Matrix (Fin k) (Fin k) ℂ)) 0 := by
      refine continuousAt_pi.2 fun c => continuousAt_pi.2 fun c' => ?_
      exact contAt_form _ _ _ (continuousAt_pi.2 fun i => ((continuous_apply i).continuousAt.comp (hqc τ c')))
        (continuousAt_pi.2 fun i => ((continuous_apply i).continuousAt.comp (hqc τ c))) hQc
    have hdc : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.det) := continuous_id.matrix_det
    exact hdc.continuousAt.comp hM
  have hQd0 : ∀ τ, Qd τ 0 = (Matrix.of fun c c' => q τ c' ⬝ᵥ Hb *ᵥ star (q τ c)).det := by
    intro τ
    simp only [Qd, hqt0, hQ0]
  have hstable : ∀ (c : 𝓞 E), ∀ x ∈ AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x},
      L.B 0 c x ∈ AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x} := by
    intro c x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨c • x, I.smul_mem c hx, (hact c x).symm⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  have hQpos : ∀ τ, 0 < (Qd τ 0).re := by
    intro τ
    rw [hQd0 τ]
    refine GlobalTheory.T.gram_det_pos_of_semidefinite_transversal g Hb (Submodule.span ℂ {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) k (q τ) hHerm hpos fun l hl => ?_
    refine GlobalTheory.T.eigenComponent_append_independent_span E (Fin g → ℂ) (L.B 0) (σ τ) _ r k v (q τ) hfam hstable (hq τ) ?_ l ?_
    · have := li_of_det (fun i => b τ i 0) (F τ 0) (T τ) (hb.2 0 h0ball τ).1
        (fun i => by rw [hF0 τ]; exact hT τ i) (hdet τ)
      rwa [hF0 τ] at this
    · refine Submodule.span_mono ?_ hl
      exact AddSubgroup.subset_closure
  have hTne : ∀ τ, 0 < ‖(Tt τ 0).det‖ ^ 2 := fun τ => by
    rw [hT0 τ]
    have := norm_pos_iff.2 (hdet τ)
    positivity
  have hdetc : ∀ τ, ContinuousAt (fun z => ‖(Tt τ z).det‖ ^ 2) 0 := by
    intro τ
    have hdc : Continuous (fun N : Matrix (Fin (r + k)) (Fin (r + k)) ℂ => ‖N.det‖ ^ 2) :=
      (continuous_id.matrix_det.norm).pow 2
    exact hdc.continuousAt.comp (hTc τ)
  have hQre : ∀ τ, ContinuousAt (fun z => (Qd τ z).re) 0 := fun τ =>
    Complex.continuous_re.continuousAt.comp (hQdc τ)
  let Φ : (Fin n → ℂ) → ℝ := fun z => ∑ τ, (Real.log (Qd τ z).re - Real.log (‖(Tt τ z).det‖ ^ 2))
  have hΦc : ContinuousAt Φ 0 := by
    refine tendsto_finset_sum _ fun τ _ => ?_
    exact ((hQre τ).log (hQpos τ).ne').sub ((hdetc τ).log (hTne τ).ne')
  set idx : ℕ := (Submodule.span (𝓞 E) (Set.range fun a' => (y a' : Λ))).toAddSubgroup.relIndex I.toAddSubgroup with hidxdef
  have hidx0 : idx ≠ 0 := by
    rw [← hidx]
    exact hfam.2.2
  have hidxpos : (0 : ℝ) < idx := Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx0)
  have hνe : ν = (idx : ℝ) * ∏ τ, ((Qd τ 0).re / ‖(Tt τ 0).det‖ ^ 2) := by
    rw [hνeq, hidx]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hQd0 τ, hT0 τ, one_pow, one_mul]
  have hνpos : 0 < ν := by
    rw [hνe]
    exact mul_pos hidxpos (Finset.prod_pos fun τ _ => div_pos (hQpos τ) (hTne τ))
  have hlogν : Real.log ν = Real.log idx + Φ 0 := by
    rw [hνe, Real.log_mul hidxpos.ne' (Finset.prod_ne_zero_iff.2 fun τ _ => (div_pos (hQpos τ) (hTne τ)).ne'),
      Real.log_prod (fun τ _ => (div_pos (hQpos τ) (hTne τ)).ne')]
    congr 1
    exact Finset.sum_congr rfl fun τ _ => Real.log_div (hQpos τ).ne' (hTne τ).ne'
  refine ⟨hνpos, fun ε hε => ?_⟩
  have hev : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ τ, ∀ i, F τ z i = ∑ j, Tt τ z j i • b τ j z) ∧
      (∀ τ, 0 < (Qd τ z).re) ∧ (∀ τ, 0 < ‖(Tt τ z).det‖ ^ 2) ∧ |Φ z - Φ 0| < ε := by
    refine (eventually_all.2 hTe).and ((eventually_all.2 fun τ =>
      (hQre τ).eventually (lt_mem_nhds (hQpos τ))).and ((eventually_all.2 fun τ =>
      (hdetc τ).eventually (lt_mem_nhds (hTne τ))).and ?_))
    have := (hΦc.eventually (Metric.ball_mem_nhds (Φ 0) hε))
    filter_upwards [this] with z hz
    simpa [Real.dist_eq] using hz
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨min δ₀ ρ, lt_min hδ₀ hρ, fun w hw hwδ => ?_⟩
  set z := expCover a w with hz
  have hzball : z ∈ Metric.ball (0 : Fin n → ℂ) δ₀ := by
    rw [mem_ball_zero_iff]
    exact hwδ.trans_le (min_le_left _ _)
  obtain ⟨h1, h2, h3, h4⟩ := hball z hzball
  have hwρ : ‖z‖ < ρ := hwδ.trans_le (min_le_right _ _)
  set R := L.riem w hw with hR
  have hfz : ∀ τ, (fun a' => eigComp R.B (σ τ) (R.P (y a' : Λ))) = f τ z := by
    intro τ
    funext a'
    simp only [f]
    rw [(hs (y a')).2.2 w hw]
    rfl
  have hGQ : ∀ τ, (R.gram (F τ z)).det = (R.gram (f τ z)).det * Qd τ z := by
    intro τ
    have hp := fun c => hrep w hw hwρ (qt τ z c)
    choose p hp1 hp2 hp3 using hp
    have hS := GlobalTheory.T.eigenComponent_span_relIndex_criterion E g Λ R I (σ τ) r k (fun a' => (y a' : Λ)) (qt τ z) p hyI (by rw [← hidxdef]; exact hidx0)
      (fun c => ?_) hp1 hp2
    · rw [hfz τ] at hS
      refine hS.trans ?_
      congr 2
      ext c c'
      exact hp3 c (qt τ z c')
    · have hzb : z ∈ Metric.ball (0 : Fin n → ℂ) 1 := expCover_mem_ball L.a_le hw
      have h5 : qt τ z c ∈ Submodule.span ℂ (Set.range fun i => b τ i z) :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      rw [(hb.2 z hzb τ).2] at h5
      exact h5
  have hDG : ∀ τ, ‖(Tt τ z).det‖ ^ 2 * (R.gram fun i => b τ i z).det.re = (R.gram (f τ z)).det.re * (Qd τ z).re := by
    intro τ
    have e1 := GlobalTheory.T.gram_det_mul_normSq_det E g Λ R (r + k) (fun i => b τ i z) (F τ z) (Tt τ z) (h1 τ)
    rw [hGQ τ] at e1
    have e2 := congrArg Complex.re e1
    rw [Complex.mul_re, GlobalTheory.T.gram_det_im_eq_zero E g Λ R r (f τ z), zero_mul, sub_zero, Complex.re_ofReal_mul] at e2
    exact e2.symm
  obtain ⟨hnz, hnzpos⟩ := GlobalTheory.T.nz_eq_nzOf_and_pos E g Λ Ψ R σ I r (fun a' => (y a' : Λ)) hσ (fun x hx y hy => hiso x hx y hy) hyI hyli
    (by rw [← hidxdef]; exact hidx0)
  have hnz2 : R.nz σ I = (∏ τ, (R.gram (f τ z)).det.re) / (idx : ℝ) := by
    rw [hnz, RiemLat.nzOf]
    simp only [hfz]
    rfl
  have hPne : (∏ τ, (R.gram (f τ z)).det.re) ≠ 0 := by
    intro h0
    rw [hnz2, h0, zero_div] at hnzpos
    exact lt_irrefl _ hnzpos
  have hGne : ∀ τ, (R.gram (f τ z)).det.re ≠ 0 := fun τ => (Finset.prod_ne_zero_iff.1 hPne) τ (Finset.mem_univ τ)
  have hlogD : ∀ τ, Real.log (R.gram fun i => b τ i z).det.re =
      Real.log (R.gram (f τ z)).det.re + (Real.log (Qd τ z).re - Real.log (‖(Tt τ z).det‖ ^ 2)) := by
    intro τ
    have e : (R.gram fun i => b τ i z).det.re = (R.gram (f τ z)).det.re * (Qd τ z).re / ‖(Tt τ z).det‖ ^ 2 := by
      rw [← hDG τ, mul_div_cancel_left₀ _ (h3 τ).ne']
    rw [e, Real.log_div (mul_ne_zero (hGne τ) (h2 τ).ne') (h3 τ).ne', Real.log_mul (hGne τ) (h2 τ).ne']
    ring
  have hmain : R.logDet (fun τ i => b τ i z) - Real.log (R.nz σ I) - Real.log ν = Φ z - Φ 0 := by
    rw [hnz2, hlogν, Real.log_div hPne hidxpos.ne', Real.log_prod (fun τ _ => hGne τ), RiemLat.logDet]
    simp only [hlogD, Finset.sum_add_distrib]
    ring
  rw [hmain]
  exact h4

theorem limit_at_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (L : ActPeriods E n a g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsCMFam σ → IsEigFrames (Metric.ball 0 1) L.B σ b → ∃ (W : Submodule (𝓞 E) Λ) (I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (s : W → (Fin n → ℂ) → Fin g → ℂ) (Hb : Matrix (Fin g) (Fin g) ℂ), (∀ x, x ∈ I ↔ x ∈ W ∧ ∀ y ∈ W, L.toLogPeriods.E x y = 0) ∧ IsSaturated I ∧ Function.Injective per ∧ (∀ x : W, ContinuousAt (s x) 0 ∧ s x 0 = per x ∧ ∀ w ∈ logCover L.a_le, s x (expCover a w) = L.P w x) ∧ (∀ (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ), (∀ k, ws k ∈ logCover L.a_le) → Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) → Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀) ∧ Submodule.span ℂ (Set.range per) = ⊤ ∧ Hb.IsHermitian ∧ (∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = L.toLogPeriods.E x x') ∧ (∀ x : W, (x : Λ) ∈ I → Hb *ᵥ star (per x) = 0) ∧ ∀ ν : ℝ, PhiNormSq (L.B 0) (fun x y => y ⬝ᵥ Hb *ᵥ star x) (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) 1 σ (fun τ i => b τ i 0) ν → 0 < ν ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < δ → |(L.riem w hw).logDet (fun τ i => b τ i (expCover a w)) - Real.log ((L.riem w hw).nz σ I) - Real.log ν| < ε := by
  intro E _ _ _ n a g Λ _ _ Ψ _ L σ m b hσ hb
  classical
  obtain ⟨bas, A, T0, B, c, ρ, h⟩ := exists_isChart L.toLogPeriods
  obtain ⟨Pr, hPr⟩ := GlobalTheory.T.exists_isKerProj' g (∑ j, B j)
  obtain ⟨hsat, hs, hinj, hspan⟩ := GlobalTheory.T.chartW_saturated_and_continuous_section n a g Λ L.toLogPeriods bas A T0 B c ρ h
  obtain ⟨hext, hlim⟩ := GlobalTheory.T.mem_chartW_of_continuous_period n a g Λ L.toLogPeriods bas A T0 B c ρ h
  obtain ⟨hHerm, hIm, hKill, hPos⟩ := GlobalTheory.T.chartQ_hermitian_and_real_pairing n a g Λ L.toLogPeriods bas A T0 B c ρ Pr h hPr
  obtain ⟨hQc, ρ', hρ', hrep⟩ := GlobalTheory.T.chartQ_continuousAt_and_local_solution n a g Λ L.toLogPeriods bas A T0 B c ρ Pr h hPr
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos

  have hBc : ∀ (c' : 𝓞 E) (t : (Fin n → ℂ) → Fin g → ℂ), ContinuousAt t 0 →
      ContinuousAt (fun z => L.B z c' (t z)) 0 := fun c' t ht => contAt_act L c' t ht
  have hstab : ∀ (c' : 𝓞 E) (x : Λ), x ∈ chartW bas B → c' • x ∈ chartW bas B := by
    intro c' x hx
    refine hext (c' • x) (fun z => L.B z c' (chartS bas A T0 x z)) (hBc c' _ (hs x hx).1) fun w hw => ?_
    rw [L.act w hw, (hs x hx).2 w hw]
  have hconj : ∀ c' : 𝓞 E, ∃ c'' : 𝓞 E, (c'' : E) = IsCMField.complexConj E (c' : E) := by
    intro c'
    refine ⟨⟨IsCMField.complexConj E (c' : E), ?_⟩, rfl⟩
    exact (NumberField.RingOfIntegers.isIntegral_coe c').map (IsCMField.complexConj E)
  let W : Submodule (𝓞 E) Λ :=
    { carrier := chartW bas B
      add_mem' := fun hx hy => (chartW bas B).add_mem hx hy
      zero_mem' := (chartW bas B).zero_mem
      smul_mem' := fun c' x hx => hstab c' x hx }
  have hW : ∀ x, x ∈ W ↔ x ∈ chartW bas B := fun x => Iff.rfl
  let I : Submodule (𝓞 E) Λ :=
    { carrier := {x | x ∈ chartW bas B ∧ ∀ y ∈ chartW bas B, L.toLogPeriods.E x y = 0}
      add_mem' := fun {x y} hx hy => ⟨(chartW bas B).add_mem hx.1 hy.1, fun u hu => by
        rw [map_add, LinearMap.add_apply, hx.2 u hu, hy.2 u hu, add_zero]⟩
      zero_mem' := ⟨(chartW bas B).zero_mem, fun u _ => by simp⟩
      smul_mem' := fun c' x hx => ⟨hstab c' x hx.1, fun u hu => by
        obtain ⟨c'', hc⟩ := hconj c'
        rw [L.adj c' c'' hc]
        exact hx.2 _ (hstab c'' u hu)⟩ }
  have hI : ∀ x, x ∈ I ↔ x ∈ W ∧ ∀ y ∈ W, L.toLogPeriods.E x y = 0 := fun x => Iff.rfl
  let toZ : W →+ chartW bas B := AddMonoidHom.mk' (fun x => ⟨x.1, x.2⟩) (fun _ _ => rfl)
  have hrad : ∀ x : chartW bas B, (∀ x' : chartW bas B, L.toLogPeriods.E x x' = 0) ↔ (x : Λ) ∈ I :=
    fun x => ⟨fun hx => ⟨x.2, fun y hy => hx ⟨y, hy⟩⟩, fun hx x' => hx.2 _ x'.2⟩
  let per : W →+ (Fin g → ℂ) := (chartPer bas A T0 B).comp toZ
  have hper : ∀ x : W, per x = chartS bas A T0 (x : Λ) 0 := fun _ => rfl
  let s : W → (Fin n → ℂ) → Fin g → ℂ := fun x => chartS bas A T0 (x : Λ)
  have hs' : ∀ x : W, ContinuousAt (s x) 0 ∧ s x 0 = per x ∧ ∀ w ∈ logCover L.a_le, s x (expCover a w) = L.P w x :=
    fun x => ⟨(hs x.1 x.2).1, rfl, (hs x.1 x.2).2⟩
  have hinj' : Function.Injective per := fun x y hxy => Subtype.ext (congrArg Subtype.val (hinj hxy))
  have hseq : ∃ ws : ℕ → Fin n → ℂ, (∀ m, ws m ∈ logCover L.a_le) ∧
      Tendsto (fun m => expCover a (ws m)) atTop (𝓝 0) := by
    refine ⟨fun m k => if k.val < a then -(((m : ℝ) + 1 : ℝ) : ℂ) else 0, fun m => ⟨fun i => ?_, fun k hk => ?_⟩, ?_⟩
    · have hi : (Fin.castLE L.a_le i).val < a := i.2
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [hi, if_true, Complex.neg_re, Complex.ofReal_re]
      linarith
    · have hk' : ¬ k.val < a := not_lt.2 hk
      simp [hk']
    · rw [tendsto_pi_nhds]
      intro k
      by_cases hk : k.val < a
      · simp only [expCover, hk, if_true, Pi.zero_apply]
        have h1 : Tendsto (fun m : ℕ => Real.exp (-((m : ℝ) + 1))) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
            (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
        simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_exp, Complex.ofReal_neg] using h2
      · simp [expCover, hk]
  have hact : ∀ (c' : 𝓞 E) (x : W), per (c' • x) = L.B 0 c' (per x) := by
    intro c' x
    obtain ⟨ws, hws, hlim0⟩ := hseq
    have h1 : Tendsto (fun m => chartS bas A T0 ((c' • x : W) : Λ) (expCover a (ws m))) atTop
        (𝓝 (per (c' • x))) := (hs' (c' • x)).1.tendsto.comp hlim0 |>.congr fun _ => rfl
    have h2 : Tendsto (fun m => L.B (expCover a (ws m)) c' (chartS bas A T0 (x : Λ) (expCover a (ws m)))) atTop
        (𝓝 (L.B 0 c' (per x))) := (hBc c' _ (hs' x).1).tendsto.comp hlim0 |>.congr fun _ => rfl
    refine tendsto_nhds_unique h1 (h2.congr fun m => ?_)
    rw [(hs x.1 x.2).2 _ (hws m), ← L.act _ (hws m)]
    exact ((hs _ (hstab c' x.1 x.2)).2 _ (hws m)).symm
  have hset : {p | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.toLogPeriods.E x x' = 0) ∧ p = chartPer bas A T0 B x} =
      {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x} := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, x.2⟩, (hrad x).1 hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, x.2⟩, (hrad ⟨x.1, x.2⟩).2 hx, rfl⟩
  refine ⟨W, I, per, s, chartQ Pr A T0 0, hI, ?_, hinj', hs', ?_, ?_, hHerm, ?_, ?_, ?_⟩
  · intro x k hk hx
    have h2 : x ∈ chartW bas B := hsat x k hk hx.1
    refine ⟨h2, fun y hy => ?_⟩
    have h3 := hx.2 y hy
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h3
    exact (mul_eq_zero.1 h3).resolve_left hk
  · intro ws x p h1 h2 h3
    obtain ⟨x₀, hx₀⟩ := hlim ws x p h1 h2 h3
    exact ⟨⟨x₀.1, x₀.2⟩, hx₀⟩
  · rw [← hspan]
    congr 1
  · intro x x'
    exact hIm (toZ x) (toZ x')
  · intro x hx
    exact hKill (toZ x) ((hrad (toZ x)).2 hx)
  · refine limit_of_data E n a g Λ Ψ L σ m b W I per s (chartQ Pr A T0 0) (chartQ Pr A T0) ρ' hσ hb (fun x hx => hx.1)
      (fun x hx y hy => hx.2 y hy.1) hinj' hact hs' hHerm ?_ hQc rfl hρ' ?_
    · intro v
      rw [← hset]
      exact hPos v
    · intro w hw hwρ y
      obtain ⟨p, h1, h2, h3⟩ := hrep w hw hwρ y
      refine ⟨p, ?_, fun x hx => ?_, h3⟩
      · refine Submodule.span_mono ?_ h1
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, (hrad x).1 hx, rfl⟩
      · exact h2 ⟨x, hx.1⟩ ((hrad ⟨x, hx.1⟩).2 hx)

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
