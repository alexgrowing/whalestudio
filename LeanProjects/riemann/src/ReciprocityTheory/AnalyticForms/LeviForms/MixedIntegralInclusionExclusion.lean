import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

theorem locDens_expand {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (P : Fin e → LocPot X) (hΘ : IsPotential A Θ) (hP : ∀ i, IsPotential A (P i))
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    locDens A (fun i => P i + Θ.rsmul (-1)) j y =
      ∑ S : Finset (Fin e), (-1 : ℝ) ^ (e - S.card) *
        locDens A (fun i => if i ∈ S then P i else Θ) j y := by
  classical
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := e)
  set a : Fin e → Matrix (Fin e) (Fin e) ℂ :=
    fun k => hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y with ha
  set b : Matrix (Fin e) (Fin e) ℂ :=
    hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y with hb
  have h1 : (fun k => hessC (fun y' => (P k + Θ.rsmul (-1)).φ ((A.chart j).symm y)
      ((A.chart j).symm y')) y) = fun k => a k + (fun _ => (-1 : ℂ) • b) k := by
    funext k
    have : (fun y' => (P k + Θ.rsmul (-1)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
        fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
          (-1) * Θ.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
    rw [this, hessC_add' _ _ _ (potential_contDiffAt A (P k) (hP k) j hy)
      ((potential_contDiffAt A Θ hΘ j hy).const_smul (-1 : ℝ) |>.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => by simp [smul_eq_mul])), hessC_const_mul']
    simp [ha, hb]
  have h2 : ∀ S : Finset (Fin e), (fun k => hessC (fun y' => (if k ∈ S then P k else Θ).φ
      ((A.chart j).symm y) ((A.chart j).symm y')) y) = S.piecewise a (fun _ => b) := by
    intro S; funext k
    by_cases hk : k ∈ S <;> simp [hk, Finset.piecewise, ha, hb]
  have h2' : ∀ S : Finset (Fin e), mdisc (fun k => hessC (fun y' => (if k ∈ S then P k else Θ).φ
      ((A.chart j).symm y) ((A.chart j).symm y')) y) = M (S.piecewise a (fun _ => b)) := fun S => by
    rw [hM, ← h2 S]
  unfold locDens maDens
  simp only [h2']
  rw [h1, ← hM, show (fun k => a k + (fun _ => (-1 : ℂ) • b) k) = a + fun _ => (-1 : ℂ) • b from rfl,
    M.map_add_univ, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [mul_left_comm]
  congr 1
  have h3 : S.piecewise a (fun _ => (-1 : ℂ) • b) =
      Sᶜ.piecewise (fun k => (-1 : ℂ) • S.piecewise a (fun _ => b) k) (S.piecewise a (fun _ => b)) := by
    funext k
    by_cases hk : k ∈ S <;> simp [hk, Finset.piecewise]
  rw [h3, M.map_piecewise_smul, Finset.prod_const, Finset.card_compl, Fintype.card_fin, smul_eq_mul]
  have : ((-1 : ℂ) ^ (e - S.card)) = (((-1 : ℝ) ^ (e - S.card) : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul]

theorem mixed_integral_inclusion_exclusion : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (P : Fin e → LocPot X), IsPotential A Θ → (∀ i, IsPotential A (P i)) →
    ∀ g : X → ℝ, Continuous g →
      mInt A (fun i => P i + Θ.rsmul (-1)) g =
        ∑ S : Finset (Fin e), (-1 : ℝ) ^ (e - S.card) *
          mInt A (fun i => if i ∈ S then P i else Θ) g := by
  intro e X _ _ _ A Θ P hΘ hP g hg
  classical
  have hpot : ∀ S : Finset (Fin e), ∀ i, IsPotential A (if i ∈ S then P i else Θ) := by
    intro S i; split_ifs; exacts [hP i, hΘ]
  unfold mInt
  split_ifs with h
  · unfold integralWith
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun S _ =>
      ((integrableOn_weight A h.some _ g (mIntegrableCont A _ (hpot S) g hg) j).const_mul _)]
    refine setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    rw [locDens_expand A Θ P hΘ hP j hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  · simp

theorem tendstoUniformlyOn_comp_continuous {α ι Z W : Type*} [PseudoMetricSpace Z] [ProperSpace Z]
    [PseudoMetricSpace W] {l : Filter ι} {K : Set α} (G : Z → W) (hG : Continuous G)
    (F : ι → α → Z) (f : α → Z) (hb : Bornology.IsBounded (f '' K))
    (h : TendstoUniformlyOn F f l K) :
    TendstoUniformlyOn (fun t y => G (F t y)) (fun y => G (f y)) l K := by
  rcases isEmpty_or_nonempty Z with hZ | ⟨⟨z0⟩⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε _
    exact Filter.Eventually.of_forall fun t y _ => (IsEmpty.false (f y)).elim
  obtain ⟨R, hR⟩ := hb.subset_closedBall z0
  have huc := (isCompact_closedBall z0 (R + 1)).uniformContinuousOn_of_continuous hG.continuousOn
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  filter_upwards [h (min δ 1) (lt_min hδ one_pos)] with t ht y hy
  have h1 := ht y hy
  have hfy : f y ∈ Metric.closedBall z0 R := hR ⟨y, hy, rfl⟩
  have hfy' : f y ∈ Metric.closedBall z0 (R + 1) :=
    Metric.closedBall_subset_closedBall (by linarith) hfy
  have hFy : F t y ∈ Metric.closedBall z0 (R + 1) := by
    rw [Metric.mem_closedBall] at hfy ⊢
    have h3 := dist_triangle (F t y) (f y) z0
    have h2 : dist (F t y) (f y) < 1 := by
      rw [dist_comm]; exact lt_of_lt_of_le h1 (min_le_right _ _)
    linarith
  exact hδG _ hfy' _ hFy (lt_of_lt_of_le h1 (min_le_left _ _))

def hessL {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) : Fin D → Fin D → ℂ :=
  fun i j =>
    ((H (Pi.single i 1) (Pi.single j 1) +
        H (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1) : ℝ) +
      Complex.I * ((H (Pi.single i 1) (Complex.I • Pi.single j 1) -
        H (Complex.I • Pi.single i 1) (Pi.single j 1) : ℝ))) / 4

theorem continuous_hessL {D : ℕ} : Continuous (hessL (D := D)) := by
  have hev : ∀ a b : Fin D → ℂ,
      Continuous fun H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ => H a b := fun a b =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ => ((H (Pi.single i 1) (Pi.single j 1) +
        H (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1) : ℝ) +
      Complex.I * ((H (Pi.single i 1) (Complex.I • Pi.single j 1) -
        H (Complex.I • Pi.single i 1) (Pi.single j 1) : ℝ)) : ℂ) / 4
  refine Continuous.div_const ?_ _
  exact (Complex.continuous_ofReal.comp ((hev _ _).add (hev _ _))).add
    (continuous_const.mul (Complex.continuous_ofReal.comp ((hev _ _).sub (hev _ _))))

private theorem hessC_eq_lemma_3 {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    hessC φ z = hessL (fderiv ℝ (fderiv ℝ φ) z) := rfl

private theorem hessL_add_lemma_2 {D : ℕ} (H1 H2 : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    hessL (H1 + H2) = hessL H1 + hessL H2 := by
  funext i k
  simp only [hessL, ContinuousLinearMap.add_apply, Pi.add_apply]
  push_cast
  ring

private theorem hessL_re_lemma {D : ℕ} (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ)
    (hh : ∀ᶠ z in 𝓝 y, AnalyticAt ℂ h z) :
    hessL (fderiv ℝ (fderiv ℝ fun z => (h z).re) y) = 0 := by
  obtain ⟨L, hL⟩ : ∃ L : ((Fin D → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin D → ℂ) →L[ℝ] ℝ),
      ∀ T, L T = Complex.reCLM.comp (T.restrictScalars ℝ) :=
    ⟨(ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ), fun T => rfl⟩
  have h1 : fderiv ℝ (fun z => (h z).re) =ᶠ[𝓝 y] fun z => L (fderiv ℂ h z) := by
    filter_upwards [hh] with z hz
    rw [hL]
    have h3 := (Complex.reCLM.hasFDerivAt.comp z
      (hz.differentiableAt.hasFDerivAt.restrictScalars ℝ)).fderiv
    simpa [Function.comp_def] using h3
  have h2 : HasFDerivAt (fun z => L (fderiv ℂ h z))
      (L.comp ((fderiv ℂ (fderiv ℂ h) y).restrictScalars ℝ)) y :=
    L.hasFDerivAt.comp y (hh.self_of_nhds.fderiv.differentiableAt.hasFDerivAt.restrictScalars ℝ)
  rw [h1.fderiv_eq, h2.fderiv]
  funext i k
  simp [hessL, hL, Complex.mul_re]

theorem hessC_base {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X)
    (hP : IsPotential A P) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (x : X)
    (hx : (A.chart j).symm y ∈ P.U x) :
    hessC (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      hessC (P.φ x ∘ (A.chart j).symm) y := by
  obtain ⟨W, hWo, hxW, G, hG, hdiff⟩ :=
    hP.2 ((A.chart j).symm y) x ((A.chart j).symm y) ⟨P.mem_U _, hx⟩
  have hN : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ P.U ((A.chart j).symm y) ∩ P.U x)
      ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm ((hWo.inter (P.isOpen_U _)).inter (P.isOpen_U _))).mem_nhds
      ⟨hy, ⟨hxW, P.mem_U _⟩, hx⟩
  have hS1o : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  have hS2 : (A.chart j).target ∩ (A.chart j).symm ⁻¹' W ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm hWo).mem_nhds ⟨hy, hxW⟩
  have hcd : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) z := by
    filter_upwards [hS1o.mem_nhds ⟨hy, hx⟩] with z hz
    exact (hP.1 x j).contDiffAt (hS1o.mem_nhds hz)
  have han : ∀ᶠ z in 𝓝 y, AnalyticAt ℂ (fun z => G ((A.chart j).symm z)) z := by
    filter_upwards [hS2] with z hz
    exact hG j z hz
  have hd1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (P.φ x ∘ (A.chart j).symm) z :=
    hcd.mono fun z hz => hz.differentiableAt (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two))
  have hd2 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (fun z => (G ((A.chart j).symm z)).re) z :=
    han.mono fun z hz => by
      have h0 : ContDiffAt ℝ 1 (fun z => G ((A.chart j).symm z)) z :=
        (hz.contDiffAt).restrict_scalars ℝ
      exact (Complex.reCLM.contDiff.contDiffAt.comp z h0).differentiableAt (by simp)
  have hcd2 : ContDiffAt ℝ 2 (fun z => (G ((A.chart j).symm z)).re) y := by
    have h0 : ContDiffAt ℝ 2 (fun z => G ((A.chart j).symm z)) y :=
      (han.self_of_nhds.contDiffAt).restrict_scalars ℝ
    exact Complex.reCLM.contDiff.contDiffAt.comp y h0
  have heq : (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      fun z => (P.φ x ∘ (A.chart j).symm) z + (G ((A.chart j).symm z)).re := by
    filter_upwards [hN] with z hz
    have h4 := hdiff ((A.chart j).symm z) hz.2
    simp only [Function.comp_apply]
    linarith
  have h1 : fderiv ℝ (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      fun z => fderiv ℝ (P.φ x ∘ (A.chart j).symm) z +
        fderiv ℝ (fun z => (G ((A.chart j).symm z)).re) z := by
    filter_upwards [heq.eventuallyEq_nhds, hd1, hd2] with z hz hz1 hz2
    rw [hz.fderiv_eq]
    exact fderiv_add hz1 hz2
  have hF : fderiv ℝ (fderiv ℝ fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      fderiv ℝ (fderiv ℝ (P.φ x ∘ (A.chart j).symm)) y +
        fderiv ℝ (fderiv ℝ fun z => (G ((A.chart j).symm z)).re) y := by
    rw [h1.fderiv_eq]
    exact fderiv_add
      (((contDiffAt_infty.1 hcd.self_of_nhds 2).fderiv_right (m := 1) (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two))).differentiableAt (by simp))
      ((hcd2.fderiv_right (m := 1) (le_of_eq one_add_one_eq_two)).differentiableAt (by simp))
  rw [hessC_eq_lemma_3, hessC_eq_lemma_3, hF, hessL_add_lemma_2, hessL_re_lemma _ y han, add_zero]

theorem hessC_base_continuousOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (hP : IsPotential A P) (j : Fin A.n) :
    ContinuousOn (fun y => hessC (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)
      (A.chart j).target := by
  intro y0 hy0
  apply ContinuousAt.continuousWithinAt
  have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U ((A.chart j).symm y0)) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U _)
  have hS : (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U ((A.chart j).symm y0) ∈ 𝓝 y0 :=
    hSo.mem_nhds ⟨hy0, P.mem_U _⟩
  have hcd : ContDiffAt ℝ ∞ (P.φ ((A.chart j).symm y0) ∘ (A.chart j).symm) y0 :=
    (hP.1 _ j).contDiffAt hS
  have hc : ContinuousAt
      (fun y => fderiv ℝ (fderiv ℝ (P.φ ((A.chart j).symm y0) ∘ (A.chart j).symm)) y) y0 :=
    (((contDiffAt_infty.1 hcd 2).fderiv_right (m := 1) (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two))).fderiv_right (m := 0) (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two))).continuousAt
  refine (continuous_hessL.continuousAt.comp hc).congr ?_
  filter_upwards [hS] with y hy
  simp only [Function.comp_apply]
  rw [hessC_base A P hP j hy.1 _ hy.2, hessC_eq_lemma_3]

private theorem evCD_lemma_5 {D : ℕ} {g : (Fin D → ℂ) → ℝ} {O : Set (Fin D → ℂ)}
    (hg : ContDiffOn ℝ ∞ g O) (hO : IsOpen O) {y : Fin D → ℂ} (hy : y ∈ O) :
    ∀ᶠ z in 𝓝 y, ContDiffAt ℝ (2 : ℕ) g z := by
  filter_upwards [hO.mem_nhds hy] with z hz
  exact contDiffAt_infty.1 (hg.contDiffAt (hO.mem_nhds hz)) 2

private theorem hessC_add_lemma_4 {D : ℕ} (f g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ (2 : ℕ) f z) (hg : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ (2 : ℕ) g z) :
    hessC (fun z => f z + g z) y = hessC f y + hessC g y := by
  have h1 : fderiv ℝ (fun z => f z + g z) =ᶠ[𝓝 y] fun z => fderiv ℝ f z + fderiv ℝ g z := by
    filter_upwards [hf, hg] with z hz1 hz2
    exact fderiv_add (hz1.differentiableAt (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two))) (hz2.differentiableAt (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two)))
  have hsum : fderiv ℝ (fun z => fderiv ℝ f z + fderiv ℝ g z) y =
      fderiv ℝ (fderiv ℝ f) y + fderiv ℝ (fderiv ℝ g) y :=
    (((hf.self_of_nhds.fderiv_right (m := 1) (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two))).differentiableAt (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two))).hasFDerivAt.add
      ((hg.self_of_nhds.fderiv_right (m := 1) (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two))).differentiableAt (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two))).hasFDerivAt).fderiv
  rw [hessC_eq_lemma_3, hessC_eq_lemma_3, hessC_eq_lemma_3, h1.fderiv_eq, hsum, hessL_add_lemma_2]
  all_goals rfl

theorem conv_dens_of_closed {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (s : X → X → ℂ) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ)
    (phT : Fin e → ℝ → X → ℝ) (hB : IsClosed (bdry s)) (hΘ : IsPotential A Θ)
    (hth : ∀ i, IsPotential A (th i)) (hph : ∀ i, A.SmoothOn (bdry s)ᶜ (ph i))
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ i, A.Smooth (phT i t))
    (hC2 : ∀ i, IsRegFamilyC2 A s (ph i) (phT i)) (j : Fin A.n) (K : Set (Fin e → ℂ))
    (hK : K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ) (hKc : IsCompact K) :
    TendstoUniformlyOn (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
      (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j) (nhdsWithin 0 (Set.Ioi 0)) K := by
  have hKT : K ⊆ (A.chart j).target := fun y hy => (hK hy).1
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ) :=
    (A.chart j).isOpen_inter_preimage_symm hB.isOpen_compl
  have hOt : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ) :=
    (A.chart j).isOpen_inter_preimage_symm isOpen_univ
  have hpot : ∀ Q : LocPot X, IsPotential A Q → ∀ y ∈ (A.chart j).target,
      ∀ᶠ z in 𝓝 y, ContDiffAt ℝ (2 : ℕ) (fun y' => Q.φ ((A.chart j).symm y) ((A.chart j).symm y')) z :=
    fun Q hQ y hy => evCD_lemma_5 (hQ.1 ((A.chart j).symm y) j)
      ((A.chart j).isOpen_inter_preimage_symm (Q.isOpen_U _)) ⟨hy, Q.mem_U _⟩
  obtain ⟨Gm, hGm⟩ : ∃ Gm : (Fin e → Fin e → Fin e → ℂ) → ℝ,
      ∀ Ms, Gm Ms = (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc Ms).re := ⟨_, fun _ => rfl⟩
  have hGc : Continuous Gm := by
    rw [show Gm = fun Ms => (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc Ms).re from funext hGm]
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    unfold mdisc
    refine continuous_const.mul (continuous_finset_sum _ fun T' _ => continuous_const.mul ?_)
    first
      | exact Continuous.matrix_det (continuous_finset_sum _ fun k _ => continuous_apply k)
      | fun_prop
  have hE : ∀ u : Fin e → X → ℝ,
      (∀ k, ∀ y ∈ K, ∀ᶠ z in 𝓝 y, ContDiffAt ℝ (2 : ℕ) (u k ∘ (A.chart j).symm) z) →
      ∀ y ∈ K, locDens A (fun i => th i + LocPot.ofFun (u i) + Θ) j y =
        Gm (fun k => hessL (fderiv ℝ (fderiv ℝ fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) + hessL (fderiv ℝ (fderiv ℝ (u k ∘ (A.chart j).symm)) y) + hessL (fderiv ℝ (fderiv ℝ fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)) := by
    intro u hu y hy
    have hM : (fun k => hessC (fun y' => (th k + LocPot.ofFun (u k) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) =
        fun k => hessL (fderiv ℝ (fderiv ℝ fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) + hessL (fderiv ℝ (fderiv ℝ (u k ∘ (A.chart j).symm)) y) + hessL (fderiv ℝ (fderiv ℝ fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y) := by
      funext k
      have hfun : (fun y' => (th k + LocPot.ofFun (u k) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
          fun y' => ((th k).φ ((A.chart j).symm y) ((A.chart j).symm y') + (u k ∘ (A.chart j).symm) y') + Θ.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
      have h12 : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ (2 : ℕ)
          (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y') + (u k ∘ (A.chart j).symm) y') z :=
        ((hpot (th k) (hth k) y (hKT hy)).and (hu k y hy)).mono fun z hz => hz.1.add hz.2
      rw [hfun, hessC_add_lemma_4 (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y') + (u k ∘ (A.chart j).symm) y')
          (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y h12 (hpot Θ hΘ y (hKT hy)),
        hessC_add_lemma_4 (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y')) (u k ∘ (A.chart j).symm) y
          (hpot (th k) (hth k) y (hKT hy)) (hu k y hy)]
      rw [hessC_eq_lemma_3, hessC_eq_lemma_3, hessC_eq_lemma_3]
      all_goals rfl
    rw [hGm]
    show (e.factorial : ℝ) * (2 / Real.pi) ^ e *
        (mdisc fun k => hessC (fun y' => (th k + LocPot.ofFun (u k) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y).re =
      (e.factorial : ℝ) * (2 / Real.pi) ^ e *
        (mdisc fun k => hessL (fderiv ℝ (fderiv ℝ fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) + hessL (fderiv ℝ (fderiv ℝ (u k ∘ (A.chart j).symm)) y) + hessL (fderiv ℝ (fderiv ℝ fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)).re
    rw [hM]
  have hc2 : ∀ k, ContinuousOn (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm))) K := fun k y hy =>
    (((contDiffAt_infty.1 ((hph k j).contDiffAt (hO.mem_nhds (hK hy))) 2).fderiv_right (m := 1)
      (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two))).fderiv_right (m := 0) (by first | exact le_top | (simp; done) | (norm_num; done) | exact le_of_eq (by norm_num) | exact le_of_eq one_add_one_eq_two | (simp; exact le_of_eq one_add_one_eq_two))).continuousAt.continuousWithinAt
  have hbk : ∀ k, Bornology.IsBounded ((fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm))) '' K) := fun k =>
    (hKc.image_of_continuousOn (hc2 k)).isBounded
  have hcf : ContinuousOn (fun y k => hessL (fderiv ℝ (fderiv ℝ fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) + hessL (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)) y) + hessL (fderiv ℝ (fderiv ℝ fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)) K :=
    continuousOn_pi.2 fun k =>
      ((((hessC_base_continuousOn A (th k) (hth k) j).mono hKT)).add
        (continuous_hessL.comp_continuousOn (hc2 k))).add
        ((hessC_base_continuousOn A Θ hΘ j).mono hKT)
  have hG : TendstoUniformlyOn (fun t y k => hessL (fderiv ℝ (fderiv ℝ fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) + hessL (fderiv ℝ (fderiv ℝ (phT k t ∘ (A.chart j).symm)) y) + hessL (fderiv ℝ (fderiv ℝ fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y))
      (fun y k => hessL (fderiv ℝ (fderiv ℝ fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) + hessL (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)) y) + hessL (fderiv ℝ (fderiv ℝ fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)) (nhdsWithin 0 (Set.Ioi 0)) K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hk : ∀ k, ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ y ∈ K,
        dist (hessL (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)) y)) (hessL (fderiv ℝ (fderiv ℝ (phT k t ∘ (A.chart j).symm)) y)) < ε := fun k =>
      Metric.tendstoUniformlyOn_iff.1 (tendstoUniformlyOn_comp_continuous hessL continuous_hessL _ _
        (hbk k) ((hC2 k j K hK hKc).2.2)) ε hε
    filter_upwards [Filter.eventually_all.2 hk] with t ht y hy
    rw [dist_pi_lt_iff hε]
    intro k
    try dsimp only
    rw [dist_add_right, dist_add_left]
    exact ht k y hy
  have hlim := tendstoUniformlyOn_comp_continuous Gm hGc _ _
    (hKc.image_of_continuousOn hcf).isBounded hG
  refine (hlim.congr ?_).congr_right ?_
  · filter_upwards [hT] with t ht y hy
    exact (hE (fun k => phT k t)
      (fun k y' hy' => evCD_lemma_5 (ht k j) hOt ⟨(hK hy').1, Set.mem_univ _⟩) y hy).symm
  · intro y hy
    exact (hE ph (fun k y' hy' => evCD_lemma_5 (hph k j) hO (hK hy')) y hy).symm

end

end ReciprocityTheory.AnForm.P
