import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsPosDensIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableA
import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian

namespace PtsPosDens

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logNorm_ofWeight_one {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    logNorm (HermLine.ofWeight g hg.2) 1 = g := by
  funext z
  simp [logNorm, HermLine.ofWeight, Real.exp_neg, Real.log_exp]

theorem isSmoothHerm_ofWeight {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    IsSmoothHerm (HermLine.ofWeight g hg.2) :=
  show ContDiffOn ℝ _ (fun z => Real.exp (-g z)) _ from Real.contDiff_exp.comp_contDiffOn hg.1.neg

theorem isSectionOn_ofWeight_one {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    IsSectionOn P (HermLine.ofWeight g hg.2) 1 := by
  refine ⟨0, fun k => by simp [HermLine.ofWeight], fun m hm k => ?_,
    fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem exists_bound {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    ∃ M : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → |g z| ≤ M := by
  set T : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ‖fun i : ι k => z ⟨k, i⟩‖ = 1} with hTdef
  have hTc : IsClosed T := by
    rw [hTdef, Set.ofPred_forall]
    exact isClosed_iInter fun k =>
      isClosed_eq (continuous_norm.comp (continuous_pi fun i => continuous_apply _)) continuous_const
  have hTb : T ⊆ Metric.closedBall 0 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    have h1 := norm_le_pi_norm (fun i : ι p.1 => z ⟨p.1, i⟩) p.2
    rw [hz p.1] at h1
    exact h1
  have hTK : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTc (Metric.isBounded_closedBall.subset hTb)
  have hTU : T ⊆ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra h
    push Not at h
    have h0 : (fun i : ι k => z ⟨k, i⟩) = 0 := funext h
    have := hz k
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨M, hM⟩ := hTK.exists_bound_of_continuousOn (hg.1.continuousOn.mono hTU)
  refine ⟨M, fun z hz => ?_⟩
  have hb : ∀ k, (fun i : ι k => z ⟨k, i⟩) ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun h0 i)
  set c : K → ℂ := fun k => ((‖fun i : ι k => z ⟨k, i⟩‖ : ℝ) : ℂ)⁻¹ with hcdef
  have hc : ∀ k, c k ≠ 0 := fun k =>
    inv_ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hb k)))
  have hmem : (fun p : Σ k, ι k => c p.1 * z p) ∈ T := by
    intro k
    have : (fun i : ι k => c k * z ⟨k, i⟩) = c k • fun i : ι k => z ⟨k, i⟩ := rfl
    rw [this, norm_smul, hcdef]
    simp only [norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hb k))
  rw [← hg.2 c z hc]
  exact hM _ hmem

theorem isSemiPosHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAp : Inter.IsSemiPosHerm A) (hBp : Inter.IsSemiPosHerm B) : Inter.IsSemiPosHerm (A.tensor B) := by
  intro z hz v
  have hU : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := isOpen_blockNonzero
  have hline : Continuous fun t : ℂ => z + t • v := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), z + t • v ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    refine hline.continuousAt.preimage_mem_nhds ?_
    simpa using hU.mem_nhds hz
  have hsm : ∀ C : HermLine ι, IsSmoothHerm C →
      ContDiffAt ℝ 2 (fun t : ℂ => Real.log (C.h (z + t • v))) 0 := by
    intro C hC
    have h1 : ContDiffAt ℝ 2 C.h (z + (0 : ℂ) • v) := by
      rw [zero_smul, add_zero]
      exact (hC.contDiffAt (hU.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)
    have h2 : ContDiffAt ℝ 2 (fun t : ℂ => z + t • v) 0 := by fun_prop
    have h3 := h1.comp (0 : ℂ) h2
    refine h3.log ?_
    simp only [Function.comp, zero_smul, add_zero]
    exact (C.pos z hz).ne'
  have heq : (fun t : ℂ => Real.log ((A.tensor B).h (z + t • v))) =ᶠ[𝓝 0]
      (fun t : ℂ => Real.log (A.h (z + t • v))) + fun t : ℂ => Real.log (B.h (z + t • v)) := by
    filter_upwards [hev] with t ht
    simp only [Pi.add_apply, HermLine.tensor]
    exact Real.log_mul (A.pos _ ht).ne' (B.pos _ ht).ne'
  rw [(laplacian_congr_nhds heq).eq_of_nhds, (hsm A hA).laplacian_add (hsm B hB)]
  exact add_nonneg (hAp z hz v) (hBp z hz v)

theorem aestronglyMeasurable {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι}
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g) :
    AEStronglyMeasurable (ptsPosDens P Ψ (pot L) g) := by
  classical
  have hfin := fibreFinite K ι P e Ψ hP hΨ
  obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin
  have hind := sheetIndep K ι P e Ψ L _ 1 hP hΨ hL (isSmoothHerm_ofWeight hg) (isSectionOn_ofWeight_one hP hg)
  rw [logNorm_ofWeight_one hg] at hind
  have hsheet : ∀ m, ∀ y ∈ B m, IsSheet P Ψ y (segre (γ m y)) (γ m) := fun m y hy =>
    ⟨rfl, Filter.eventually_of_mem ((hBo m).mem_nhds hy) fun y' hy' => hlift m y' hy'⟩
  have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
    (hlift m y hy).1.continuousAt.continuousWithinAt
  have hO : ∀ m, Set.MapsTo (γ m) (B m) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun m y hy =>
    (hlift m y hy).2.1.1
  have hseg : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd _ fun k _ => continuous_apply _
  set σ : ℕ → (Fin e → ℂ) → ((k : K) → ι k) → ℂ := fun m =>
    (B m).piecewise (fun y => segre (γ m y)) 0 with hσdef
  have hσB : ∀ m, ∀ y ∈ B m, σ m y = segre (γ m y) := fun m y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hσm : ∀ m, Measurable (σ m) := fun m =>
    (hseg.comp_continuousOn (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet
  set a : ℕ → (Fin e → ℂ) → ℝ := fun m => (B m).piecewise (fun y => g (γ m y)) 0 with hadef
  have ham : ∀ m, Measurable (a m) := fun m =>
    (hg.1.continuousOn.comp (hγc m) (hO m)).measurable_piecewise continuousOn_const (hBo m).measurableSet
  set dens : ℕ → (Fin e → ℂ) → ℝ := fun m y =>
    max (a m y * maDensity (fun j y' => pot L j (γ m y')) y) 0 with hddef
  have hdm : ∀ m, Measurable (dens m) := fun m =>
    ((ham m).mul (PtsSumMeasurable.measurable_maDensity _)).max measurable_const
  have hdens : ∀ m, ∀ y ∈ B m,
      dens m y = max (g (γ m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0 := by
    intro m y hy
    simp only [hddef, hadef, Set.piecewise_eq_of_mem _ _ _ hy]
  set S : ℕ → Set (Fin e → ℂ) := fun m =>
    {y | y ∈ B m ∧ ∀ m' < m, ¬ (y ∈ B m' ∧ σ m' y = σ m y)} with hSdef
  have hSm : ∀ m, MeasurableSet (S m) := by
    intro m
    have : S m = B m ∩ ⋂ m' ∈ Finset.range m, (B m' ∩ {y | σ m' y = σ m y})ᶜ := by
      ext y
      simp [hSdef]
    rw [this]
    exact (hBo m).measurableSet.inter (Finset.measurableSet_biInter _ fun m' _ =>
      ((hBo m').measurableSet.inter (measurableSet_eq_fun (hσm m') (hσm m))).compl)
  set f : ℕ → (Fin e → ℂ) → ℝ := fun m => (S m).indicator (dens m) with hfdef
  have hfm : ∀ m, Measurable (f m) := fun m => (hdm m).indicator (hSm m)
  have hpp : ptsPosDens P Ψ (pot L) g =
      fun y => ∑ᶠ w ∈ fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 := rfl
  rw [hpp]
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ m ∈ Finset.range N, f m y)
    (fun N => (Finset.measurable_sum _ fun m _ => hfm m).aestronglyMeasurable) ?_
  filter_upwards [hind] with y hy
  have hterm : ∀ m, y ∈ S m → f m y = max (sheetDensity P Ψ (pot L) g y (σ m y)) 0 := by
    intro m hm
    have hsh := hsheet m y hm.1
    rw [← hσB m y hm.1] at hsh
    have hex : ∃ γ', IsSheet P Ψ y (σ m y) γ' := ⟨_, hsh⟩
    rw [hfdef]
    simp only
    rw [Set.indicator_of_mem hm, hdens m y hm.1]
    unfold sheetDensity
    rw [dif_pos hex]
    rw [hy _ _ _ hex.choose_spec hsh]
  have hmemF : ∀ m, y ∈ S m → σ m y ∈ (hfin y).toFinset := by
    intro m hm
    rw [Set.Finite.mem_toFinset, hσB m y hm.1]
    exact ⟨γ m y, (hlift m y hm.1).2.1, rfl, (hlift m y hm.1).2.2⟩
  have hfy : ∀ m, (∑ w ∈ (hfin y).toFinset, if σ m y = w then f m y else 0) = f m y := by
    intro m
    rw [Finset.sum_ite_eq]
    by_cases hm : y ∈ S m
    · rw [if_pos (hmemF m hm)]
    · split_ifs
      · rfl
      · rw [hfdef]
        simp only
        rw [Set.indicator_of_notMem hm]
  have hev : ∀ w ∈ (hfin y).toFinset, ∀ᶠ N in atTop,
      max (sheetDensity P Ψ (pot L) g y w) 0 =
        ∑ m ∈ Finset.range N, if σ m y = w then f m y else 0 := by
    intro w _
    by_cases hex : ∃ γ', IsSheet P Ψ y w γ'
    · obtain ⟨γ', hγ'⟩ := hex
      have hP' : ∃ m, y ∈ B m ∧ σ m y = w := by
        obtain ⟨m, hm, hmw⟩ := hcov y w γ' hγ'
        exact ⟨m, hm, (hσB m y hm).trans hmw⟩
      obtain ⟨hm1B, hm1w⟩ := Nat.find_spec hP'
      have hm1S : y ∈ S (Nat.find hP') :=
        ⟨hm1B, fun m' hm' h => Nat.find_min hP' hm' ⟨h.1, h.2.trans hm1w⟩⟩
      filter_upwards [eventually_gt_atTop (Nat.find hP')] with N hN
      rw [Finset.sum_eq_single_of_mem (Nat.find hP') (Finset.mem_range.2 hN), if_pos hm1w,
        hterm _ hm1S, hm1w]
      intro m _ hne
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · exfalso
          have hle : Nat.find hP' ≤ m := Nat.find_min' hP' ⟨hmS.1, hmw⟩
          exact hmS.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ⟨hm1B, hm1w.trans hmw.symm⟩
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
    · have h0 : sheetDensity P Ψ (pot L) g y w = 0 := by
        unfold sheetDensity
        rw [dif_neg hex]
      refine Eventually.of_forall fun N => ?_
      rw [h0, max_self]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · have hsh := hsheet m y hmS.1
          rw [← hσB m y hmS.1, hmw] at hsh
          exact absurd ⟨_, hsh⟩ hex
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
  have hsum : ∑ᶠ w ∈ fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 =
      ∑ w ∈ (hfin y).toFinset, max (sheetDensity P Ψ (pot L) g y w) 0 :=
    finsum_mem_eq_finite_toFinset_sum _ (hfin y)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(eventually_all_finset _).2 hev] with N hN
  rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => hfy m

end PtsPosDens

end GroundTheory.Heights₂.Heights
