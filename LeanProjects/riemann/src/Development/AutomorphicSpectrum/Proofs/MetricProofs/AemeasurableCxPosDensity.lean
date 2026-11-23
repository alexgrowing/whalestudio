import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas

open MvPolynomial MeasureTheory Metric Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
  GlobalTheory.CompanionTheory.Ar.Pub.CxComp
open ReciprocityTheory.AnForm.R (conePts)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

def setSecSet (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (B : Set (Fin e → ℂ)) : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) :=
  {G | (∀ y ∉ B, G y = 0) ∧ DifferentiableOn ℂ G B ∧ ∀ y ∈ B, G y ∈ setFibre S Ψ y}

theorem setCoincide_null {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {c : Fin e → ℂ} {r : ℝ}
    {G G' : (Fin e → ℂ) → ((k : K) → ι k) → ℂ} (hG : G ∈ setSecSet S Ψ (ball c r))
    (hG' : G' ∈ setSecSet S Ψ (ball c r)) (hne : G ≠ G') :
    volume {y | y ∈ ball c r ∧ G y = G' y} = 0 := by
  obtain ⟨y0, hy0⟩ := Function.ne_iff.mp hne
  have hy0B : y0 ∈ ball c r := by
    by_contra h
    exact hy0 ((hG.1 y0 h).trans (hG'.1 y0 h).symm)
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hy0
  have hd : DifferentiableOn ℂ (fun y => G y v - G' y v) (ball c r) :=
    (differentiableOn_pi.mp hG.2.1 v).sub (differentiableOn_pi.mp hG'.2.1 v)
  have han := osgood e _ _ isOpen_ball hd
  refine measure_mono_null ?_ (ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_ball
    (convex_ball c r).isPreconnected han ⟨y0, hy0B, sub_ne_zero.mpr hv⟩)
  rintro y ⟨hyB, hy⟩
  exact ⟨hyB, by simp [hy]⟩

theorem setSecSet_finite {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (setFibre S Ψ y).Finite)
    (c : Fin e → ℂ) {r : ℝ} (hr : 0 < r) : (setSecSet S Ψ (ball c r)).Finite := by
  by_contra hinf
  let f := Set.Infinite.natEmbedding _ hinf
  set N : Set (Fin e → ℂ) := ⋃ i : ℕ, ⋃ j : ℕ, ⋃ (_ : i ≠ j),
    {y | y ∈ ball c r ∧ (f i : (Fin e → ℂ) → ((k : K) → ι k) → ℂ) y = (f j : (Fin e → ℂ) → ((k : K) → ι k) → ℂ) y}
  have hN : volume N = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
    refine setCoincide_null (f i).2 (f j).2 fun h => hij (f.injective (Subtype.ext h))
  have hpos : 0 < volume (ball c r) := measure_ball_pos volume c hr
  obtain ⟨y, hyB, hyN⟩ : ∃ y ∈ ball c r, y ∉ N := by
    by_contra h
    push Not at h
    exact hpos.ne' (measure_mono_null h hN)
  refine (hfin y).not_infinite (Set.infinite_of_injective_forall_mem (f := fun n =>
    (f n : (Fin e → ℂ) → ((k : K) → ι k) → ℂ) y) ?_ fun n => (f n).2.2.2 y hyB)
  intro i j hij
  by_contra h
  exact hyN (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨h, hyB, hij⟩⟩⟩)

def setBadSet (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set (Fin e → ℂ) :=
  {y | ∃ w γ γ', IsSetSheet S Ψ y w γ ∧ IsSetSheet S Ψ y w γ' ∧
    ¬ ((fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y'))}

theorem mem_setSecSet_of_sheet {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {B : Set (Fin e → ℂ)}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : ∀ y' ∈ B, DifferentiableAt ℂ γ y' ∧ γ y' ∈ S ∧ Ψ (segre (γ y')) = Fin.cons 1 y') :
    B.indicator (fun y' => segre (γ y')) ∈ setSecSet S Ψ B := by
  refine ⟨fun y hy => Set.indicator_of_notMem hy _, ?_, fun y hy => ?_⟩
  · refine DifferentiableOn.congr (f := fun y' => segre (γ y')) ?_ fun y hy => Set.indicator_of_mem hy _
    exact fun y hy => (segre_differentiableAt (h y hy).1).differentiableWithinAt
  · rw [Set.indicator_of_mem hy]
    exact ⟨γ y, (h y hy).2.1, rfl, (h y hy).2.2⟩

theorem setBadSet_null {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (setFibre S Ψ y).Finite) :
    volume (setBadSet S Ψ) = 0 := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin e → ℂ)
  have hρ : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  refine measure_mono_null (t := ⋃ d ∈ D, ⋃ n : ℕ,
      ⋃ G ∈ setSecSet S Ψ (ball d (1 / (n + 1))), ⋃ G' ∈ setSecSet S Ψ (ball d (1 / (n + 1))),
        ⋃ (_ : G ≠ G'), {y | y ∈ ball d (1 / (n + 1)) ∧ G y = G' y}) ?_ ?_
  · rintro y ⟨w, γ, γ', h1, h2, hne⟩
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.2.and h2.2)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨d, hdy, hdD⟩ := Metric.dense_iff.mp hDd y _ (hρ n)
    set B := ball d (1 / ((n : ℝ) + 1))
    have hyB : y ∈ B := by
      rw [mem_ball, dist_comm]
      exact hdy
    have hBsub : B ⊆ ball y ε := by
      intro y' hy'
      rw [mem_ball] at hy' hdy ⊢
      calc dist y' y ≤ dist y' d + dist d y := dist_triangle _ _ _
        _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_lt_add hy' hdy
        _ < ε := by linarith
    have hG := mem_setSecSet_of_sheet (S := S) (Ψ := Ψ) (B := B) (γ := γ) fun y' hy' =>
      (hball y' (hBsub hy')).1
    have hG' := mem_setSecSet_of_sheet (S := S) (Ψ := Ψ) (B := B) (γ := γ') fun y' hy' =>
      (hball y' (hBsub hy')).2
    refine Set.mem_iUnion₂.mpr ⟨d, hdD, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion₂.mpr ⟨_, hG,
      Set.mem_iUnion₂.mpr ⟨_, hG', Set.mem_iUnion.mpr ⟨fun heq => hne ?_, hyB, ?_⟩⟩⟩⟩⟩
    · filter_upwards [isOpen_ball.mem_nhds hyB] with y' hy'
      have := congrFun heq y'
      rwa [Set.indicator_of_mem hy', Set.indicator_of_mem hy'] at this
    · simp only [Set.indicator_of_mem hyB]
      rw [h1.1, h2.1]
  · refine (measure_biUnion_null_iff hDc).mpr fun d _ => measure_iUnion_null fun n => ?_
    have hfinS := setSecSet_finite hfin d (hρ n) (S := S) (Ψ := Ψ)
    refine (measure_biUnion_null_iff hfinS.countable).mpr fun G hG => ?_
    refine (measure_biUnion_null_iff hfinS.countable).mpr fun G' hG' => ?_
    exact measure_iUnion_null fun hne => setCoincide_null hG hG' hne

theorem setSheet_analyticAt {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSetSheet S Ψ y w γ) :
    AnalyticAt ℂ γ y := by
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.mp h.2
  refine analyticAt_pi_iff.mpr fun p => ?_
  exact osgood e _ _ isOpen_ball (fun y' hy' =>
    (differentiableAt_pi.mp (hb y' hy').1 p).differentiableWithinAt) y (mem_ball_self hε)

theorem maDensity_eq_of_segre {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : AnalyticAt ℂ γ y) (hγ' : AnalyticAt ℂ γ' y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0)
    (hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y')) :
    maDensity (fun j y' => pot L j (γ y')) y = maDensity (fun j y' => pot L j (γ' y')) y := by
  have hs : IsSectionOn (⊥ : Ideal (MRing ι))
      (HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)) 1 := by
    refine ⟨0, fun k => by simp [HermLine.ofWeight], fun m hm k => ?_, ?_⟩
    · rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp
    · simp
  have h := density_eq hL hs hγ hγ' hy hseg
  have h1 : ∀ z, logNorm (HermLine.ofWeight (fun _ : (Σ k, ι k) → ℂ => (1 : ℝ)) (fun _ _ _ => rfl)) 1 z = 1 := by
    intro z
    simp [logNorm, HermLine.ofWeight, Real.exp_neg, Real.log_exp]
  simpa only [h1, one_mul] using h

theorem setSheetIndep {S : Set ((Σ k, ι k) → ℂ)} (hS : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (setFibre S Ψ y).Finite)
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ᵐ y : Fin e → ℂ, ∀ (w : ((k : K) → ι k) → ℂ) (γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ),
      IsSetSheet S Ψ y w γ → IsSetSheet S Ψ y w γ' →
      maDensity (fun j y' => pot L j (γ y')) y = maDensity (fun j y' => pot L j (γ' y')) y := by
  refine ae_iff.mpr (measure_mono_null (fun y hy => ?_) (setBadSet_null hfin))
  simp only [Set.mem_ofPred_eq, not_forall] at hy
  obtain ⟨w, γ, γ', h1, h2, hne⟩ := hy
  refine ⟨w, γ, γ', h1, h2, fun hseg => hne ?_⟩
  exact maDensity_eq_of_segre hL (setSheet_analyticAt h1) (setSheet_analyticAt h2)
    (hS _ h1.2.self_of_nhds.2.1) hseg

theorem exists_setLift_family {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (setFibre S Ψ y).Finite) :
    ∃ (B : ℕ → Set (Fin e → ℂ)) (γ : ℕ → (Fin e → ℂ) → (Σ k, ι k) → ℂ),
      (∀ m, IsOpen (B m)) ∧
      (∀ m, ∀ y ∈ B m, DifferentiableAt ℂ (γ m) y ∧ γ m y ∈ S ∧
        Ψ (segre (γ m y)) = Fin.cons 1 y) ∧
      ∀ y w γ', IsSetSheet S Ψ y w γ' → ∃ m, y ∈ B m ∧ segre (γ m y) = w := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin e → ℂ)
  have hρ : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  let Bl : D × ℕ → Set (Fin e → ℂ) := fun p => ball (p.1 : Fin e → ℂ) (1 / (p.2 + 1))
  have : Countable D := hDc.to_subtype
  have : ∀ p : D × ℕ, Countable (setSecSet S Ψ (Bl p)) := fun p =>
    (setSecSet_finite hfin (p.1 : Fin e → ℂ) (hρ p.2)).countable.to_subtype
  let T := Σ p : D × ℕ, setSecSet S Ψ (Bl p)
  let Lift : T → ((Fin e → ℂ) → (Σ k, ι k) → ℂ) → Prop := fun t γ =>
    ∀ y ∈ Bl t.1, DifferentiableAt ℂ γ y ∧ γ y ∈ S ∧
      segre (γ y) = (t.2 : (Fin e → ℂ) → ((k : K) → ι k) → ℂ) y
  let Bo : Option T → Set (Fin e → ℂ) := fun o =>
    o.elim ∅ fun t => if ∃ γ, Lift t γ then Bl t.1 else ∅
  let γo : Option T → (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun o =>
    o.elim (fun _ _ => 0) fun t => if h : ∃ γ, Lift t γ then h.choose else fun _ _ => 0
  obtain ⟨f, hf⟩ := exists_surjective_nat (Option T)
  have hBsome : ∀ t : T, Bo (some t) = if ∃ γ, Lift t γ then Bl t.1 else ∅ := fun t => rfl
  have hγsome : ∀ t : T, (h : ∃ γ, Lift t γ) → γo (some t) = h.choose := fun t h => by
    show (if h : ∃ γ, Lift t γ then h.choose else fun _ _ => 0) = _
    rw [dif_pos h]
  have hBo : ∀ o, IsOpen (Bo o) := by
    rintro (_ | t)
    · exact isOpen_empty
    · rw [hBsome]
      split_ifs
      · exact isOpen_ball
      · exact isOpen_empty
  have hlift : ∀ o, ∀ y ∈ Bo o, DifferentiableAt ℂ (γo o) y ∧ γo o y ∈ S ∧
      Ψ (segre (γo o y)) = Fin.cons 1 y := by
    rintro (_ | t) y hy
    · exact absurd hy (Set.notMem_empty y)
    · rw [hBsome] at hy
      split_ifs at hy with h
      · rw [hγsome t h]
        obtain ⟨h1, h2, h3⟩ := h.choose_spec y hy
        refine ⟨h1, h2, ?_⟩
        obtain ⟨-, -, hfib⟩ := t.2.2
        obtain ⟨z, -, -, hΨ⟩ := hfib y hy
        rw [h3, hΨ]
      · exact absurd hy (Set.notMem_empty y)
  refine ⟨fun m => Bo (f m), fun m => γo (f m), fun m => hBo (f m), fun m => hlift (f m),
    fun y w γ' hγ' => ?_⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hγ'.2
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨d, hdy, hdD⟩ := Metric.dense_iff.mp hDd y _ (hρ n)
    let p : D × ℕ := (⟨d, hdD⟩, n)
    have hyB : y ∈ Bl p := by
      show y ∈ ball d (1 / ((n : ℝ) + 1))
      rw [mem_ball, dist_comm]
      exact hdy
    have hBsub : Bl p ⊆ ball y ε := by
      intro y' hy'
      have hy'' : dist y' d < 1 / ((n : ℝ) + 1) := hy'
      rw [mem_ball] at hdy ⊢
      calc dist y' y ≤ dist y' d + dist d y := dist_triangle _ _ _
        _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_lt_add hy'' hdy
        _ < ε := by linarith
    have hG := mem_setSecSet_of_sheet (S := S) (Ψ := Ψ) (B := Bl p) (γ := γ') fun y' hy' =>
      hball y' (hBsub hy')
    let t : T := ⟨p, _, hG⟩
    have hL : ∃ γ, Lift t γ := ⟨γ', fun y' hy' => ⟨(hball y' (hBsub hy')).1,
      (hball y' (hBsub hy')).2.1, by simp only [t]; rw [Set.indicator_of_mem hy']⟩⟩
    obtain ⟨m, hm⟩ := hf (some t)
    refine ⟨m, ?_, ?_⟩
    · show y ∈ Bo (f m)
      rw [hm, hBsome, if_pos hL]
      exact hyB
    · show segre (γo (f m) y) = w
      rw [hm, hγsome t hL, (hL.choose_spec y hyB).2.2]
      simp only [t]
      rw [Set.indicator_of_mem hyB, hγ'.1]

theorem cxPosDens_aemeasurable_of_finite {S : Set ((Σ k, ι k) → ℂ)}
    (hS : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (setFibre S Ψ y).Finite)
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {g : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : Measurable g)
    (hdeg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) :
    AEMeasurable (cxPosDens S Ψ (pot L) g) := by
  classical
  obtain ⟨B, γ, hBo, hlift, hcov⟩ := exists_setLift_family (S := S) (Ψ := Ψ) hfin

  have hind := setSheetIndep hS hfin hL
  have hsheet : ∀ m, ∀ y ∈ B m, IsSetSheet S Ψ y (segre (γ m y)) (γ m) := fun m y hy =>
    ⟨rfl, Filter.eventually_of_mem ((hBo m).mem_nhds hy) fun y' hy' => hlift m y' hy'⟩
  have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
    (hlift m y hy).1.continuousAt.continuousWithinAt
  have hO : ∀ m, Set.MapsTo (γ m) (B m) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun m y hy =>
    hS _ (hlift m y hy).2.1
  have hseg : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd _ fun k _ => continuous_apply _
  set σ : ℕ → (Fin e → ℂ) → ((k : K) → ι k) → ℂ := fun m =>
    (B m).piecewise (fun y => segre (γ m y)) 0 with hσdef
  have hσB : ∀ m, ∀ y ∈ B m, σ m y = segre (γ m y) := fun m y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hσm : ∀ m, Measurable (σ m) := fun m =>
    (hseg.comp_continuousOn (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet

  set γt : ℕ → (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun m => (B m).piecewise (γ m) 0 with hγtdef
  have hγtm : ∀ m, Measurable (γt m) := fun m =>
    (hγc m).measurable_piecewise continuousOn_const (hBo m).measurableSet
  set dens : ℕ → (Fin e → ℂ) → ℝ := fun m y =>
    max (g (γt m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0 with hddef
  have hdm : ∀ m, Measurable (dens m) := fun m =>
    ((hg.comp (hγtm m)).mul (GroundTheory.Heights₂.Heights.PtsSumMeasurable.measurable_maDensity _)).max
      measurable_const
  have hdens : ∀ m, ∀ y ∈ B m,
      dens m y = max (g (γ m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0 := by
    intro m y hy
    simp only [hddef, hγtdef, Set.piecewise_eq_of_mem _ _ _ hy]
  set T : ℕ → Set (Fin e → ℂ) := fun m =>
    {y | y ∈ B m ∧ ∀ m' < m, ¬ (y ∈ B m' ∧ σ m' y = σ m y)} with hTdef
  have hTm : ∀ m, MeasurableSet (T m) := by
    intro m
    have : T m = B m ∩ ⋂ m' ∈ Finset.range m, (B m' ∩ {y | σ m' y = σ m y})ᶜ := by
      ext y
      simp [hTdef]
    rw [this]
    exact (hBo m).measurableSet.inter (Finset.measurableSet_biInter _ fun m' _ =>
      ((hBo m').measurableSet.inter (measurableSet_eq_fun (hσm m') (hσm m))).compl)
  set f : ℕ → (Fin e → ℂ) → ℝ := fun m => (T m).indicator (dens m) with hfdef
  have hfm : ∀ m, Measurable (f m) := fun m => (hdm m).indicator (hTm m)
  have key : AEStronglyMeasurable (cxPosDens S Ψ (pot L) g) volume := by
    have hpp : cxPosDens S Ψ (pot L) g =
        fun y => ∑ᶠ w ∈ setFibre S Ψ y, max (setSheetDensity S Ψ (pot L) g y w) 0 := rfl
    rw [hpp]
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ m ∈ Finset.range N, f m y)
      (fun N => (Finset.measurable_sum _ fun m _ => hfm m).aestronglyMeasurable) ?_
    filter_upwards [hind] with y hy
    have hterm : ∀ m, y ∈ T m → f m y = max (setSheetDensity S Ψ (pot L) g y (σ m y)) 0 := by
      intro m hm
      have hsh := hsheet m y hm.1
      rw [← hσB m y hm.1] at hsh
      have hex : ∃ γ', IsSetSheet S Ψ y (σ m y) γ' := ⟨_, hsh⟩
      rw [hfdef]
      simp only
      rw [Set.indicator_of_mem hm, hdens m y hm.1]
      unfold setSheetDensity
      rw [dif_pos hex, hy _ _ _ hex.choose_spec hsh]

      choose i0 hi0 using hO m hm.1
      have hs : segre (γ m y) = segre (hex.choose y) := by
        rw [hex.choose_spec.1, hσB m y hm.1]
      obtain ⟨hc', hrel⟩ := eq_bsmul_of_segre_eq i0 hi0 hs
      have hgy : g (hex.choose y) = g (γ m y) := by
        rw [hrel]
        exact hdeg _ _ fun k => div_ne_zero (hc' k) (hi0 k)
      rw [hgy]
    have hmemF : ∀ m, y ∈ T m → σ m y ∈ (hfin y).toFinset := by
      intro m hm
      rw [Set.Finite.mem_toFinset, hσB m y hm.1]
      exact ⟨γ m y, (hlift m y hm.1).2.1, rfl, (hlift m y hm.1).2.2⟩
    have hfy : ∀ m, (∑ w ∈ (hfin y).toFinset, if σ m y = w then f m y else 0) = f m y := by
      intro m
      rw [Finset.sum_ite_eq]
      by_cases hm : y ∈ T m
      · rw [if_pos (hmemF m hm)]
      · split_ifs
        · rfl
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hm]
    have hev : ∀ w ∈ (hfin y).toFinset, ∀ᶠ N in atTop,
        max (setSheetDensity S Ψ (pot L) g y w) 0 =
          ∑ m ∈ Finset.range N, if σ m y = w then f m y else 0 := by
      intro w _
      by_cases hex : ∃ γ', IsSetSheet S Ψ y w γ'
      · obtain ⟨γ', hγ'⟩ := hex
        have hP' : ∃ m, y ∈ B m ∧ σ m y = w := by
          obtain ⟨m, hm, hmw⟩ := hcov y w γ' hγ'
          exact ⟨m, hm, (hσB m y hm).trans hmw⟩
        obtain ⟨hm1B, hm1w⟩ := Nat.find_spec hP'
        have hm1T : y ∈ T (Nat.find hP') :=
          ⟨hm1B, fun m' hm' h => Nat.find_min hP' hm' ⟨h.1, h.2.trans hm1w⟩⟩
        filter_upwards [eventually_gt_atTop (Nat.find hP')] with N hN
        rw [Finset.sum_eq_single_of_mem (Nat.find hP') (Finset.mem_range.2 hN), if_pos hm1w,
          hterm _ hm1T, hm1w]
        intro m _ hne
        split_ifs with hmw
        · by_cases hmT : y ∈ T m
          · exfalso
            have hle : Nat.find hP' ≤ m := Nat.find_min' hP' ⟨hmT.1, hmw⟩
            exact hmT.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ⟨hm1B, hm1w.trans hmw.symm⟩
          · rw [hfdef]
            simp only
            rw [Set.indicator_of_notMem hmT]
        · rfl
      · have h0 : setSheetDensity S Ψ (pot L) g y w = 0 := by
          unfold setSheetDensity
          rw [dif_neg hex]
        refine Eventually.of_forall fun N => ?_
        rw [h0, max_self]
        refine (Finset.sum_eq_zero fun m _ => ?_).symm
        split_ifs with hmw
        · by_cases hmT : y ∈ T m
          · have hsh := hsheet m y hmT.1
            rw [← hσB m y hmT.1, hmw] at hsh
            exact absurd ⟨_, hsh⟩ hex
          · rw [hfdef]
            simp only
            rw [Set.indicator_of_notMem hmT]
        · rfl
    have hsum : ∑ᶠ w ∈ setFibre S Ψ y, max (setSheetDensity S Ψ (pot L) g y w) 0 =
        ∑ w ∈ (hfin y).toFinset, max (setSheetDensity S Ψ (pot L) g y w) 0 :=
      finsum_mem_eq_finite_toFinset_sum _ (hfin y)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_all_finset _).2 hev] with N hN
    rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => hfy m
  exact key.aemeasurable

theorem cxPosDens_aemeasurable : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    AEMeasurable (cxPosDens (conePts Q) Ψ (pot L) g) := by
  intro K _ ι _ Q e Ψ L g hQ hΨ hL hg hdeg
  exact cxPosDens_aemeasurable_of_finite (fun z hz => hz.1) (GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite K ι Q e Ψ hQ hΨ) hL hg hdeg

end GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas
