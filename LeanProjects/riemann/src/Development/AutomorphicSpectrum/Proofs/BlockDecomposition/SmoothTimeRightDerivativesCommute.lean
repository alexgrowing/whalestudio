import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SmCalc

section Generic

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {u : ℝ → E → W} {O : Set E}

theorem hasFDerivAt_unc (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O) :
    HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (s, y)) (s, y) :=
  ((hu.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
    (by simp)).hasFDerivAt

theorem hasDerivAt_line (s : ℝ) (y : E) :
    HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : E)) s :=
  (hasDerivAt_id s).prodMk (hasDerivAt_const s y)

theorem deriv_eq (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O) :
    deriv (fun r => u r y) s = fderiv ℝ (Function.uncurry u) (s, y) ((1 : ℝ), (0 : E)) := by
  have h2 := HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, y)) s
    (hasFDerivAt_unc hO hu s hy) (hasDerivAt_line s y)
  exact h2.deriv

theorem fderiv_slice_eq (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O)
    (v : E) : fderiv ℝ (u s) y v = fderiv ℝ (Function.uncurry u) (s, y) ((0 : ℝ), v) := by
  have h1 : HasFDerivAt (fun z : E => (s, z)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
    hasFDerivAt_prodMk_right s y
  have h2 := HasFDerivAt.comp (g := Function.uncurry u) (f := fun z : E => (s, z)) y
    (hasFDerivAt_unc hO hu s hy) h1
  have h3 : HasFDerivAt (u s) ((fderiv ℝ (Function.uncurry u) (s, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)) y := h2
  simp [h3.fderiv]

theorem fd_smooth (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) :
    ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ O) :=
  hu.fderiv_of_isOpen (isOpen_univ.prod hO) (by simp)

theorem smooth_deriv (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) :
    ContDiffOn ℝ ∞ (Function.uncurry fun s y => deriv (fun r => u r y) s) (Set.univ ×ˢ O) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (Function.uncurry u) p ((1 : ℝ), (0 : E))) (Set.univ ×ˢ O) :=
    (fd_smooth hO hu).clm_apply contDiffOn_const
  refine ContDiffOn.congr h ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact deriv_eq hO hu s hy

theorem smooth_field (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O))
    {V : E → E} (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (Function.uncurry fun s y => fderiv ℝ (u s) y (V y)) (Set.univ ×ˢ O) := by
  have h0 : ContDiff ℝ ∞ (fun p : ℝ × E => ((0 : ℝ), V p.2)) :=
    contDiff_const.prodMk (hV.comp contDiff_snd)
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (Function.uncurry u) p ((0 : ℝ), V p.2)) (Set.univ ×ˢ O) :=
    (fd_smooth hO hu).clm_apply h0.contDiffOn
  refine ContDiffOn.congr h ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact fderiv_slice_eq hO hu s hy _

theorem smooth_slice (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) :
    ContDiffOn ℝ ∞ (u s) O := by
  have h1 : ContDiff ℝ ∞ (fun z : E => (s, z)) := contDiff_const.prodMk contDiff_id
  exact ContDiffOn.comp (g := Function.uncurry u) (f := fun z : E => (s, z)) hu
    h1.contDiffOn (fun z hz => ⟨Set.mem_univ _, hz⟩)

theorem smooth_line (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O))
    {y : E} (hy : y ∈ O) : ContDiff ℝ ∞ fun s => u s y := by
  have h1 : ContDiff ℝ ∞ (fun r : ℝ => (r, y)) := contDiff_id.prodMk contDiff_const
  have h2 := ContDiffOn.comp (s := Set.univ) (g := Function.uncurry u)
    (f := fun r : ℝ => (r, y)) hu h1.contDiffOn (fun _ _ => ⟨Set.mem_univ _, hy⟩)
  exact contDiffOn_univ.1 h2

theorem deriv_fderiv_comm (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (v : E) (s : ℝ) {y : E}
    (hy : y ∈ O) :
    deriv (fun r => fderiv ℝ (u r) y v) s =
      fderiv ℝ (fun z => deriv (fun r => u r z) s) y v := by
  have hm : (s, y) ∈ (Set.univ : Set ℝ) ×ˢ O := ⟨Set.mem_univ _, hy⟩
  have hn := (isOpen_univ.prod hO).mem_nhds hm
  have hF : ContDiffAt ℝ ∞ (Function.uncurry u) (s, y) := hu.contDiffAt hn
  have hG : HasFDerivAt (fderiv ℝ (Function.uncurry u))
      (fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y)) (s, y) :=
    (((fd_smooth hO hu).contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hsym : IsSymmSndFDerivAt ℝ (Function.uncurry u) (s, y) :=
    hF.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hL : HasDerivAt (fun r => fderiv ℝ (u r) y v)
      (fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y) ((1 : ℝ), (0 : E)) ((0 : ℝ), v)) s := by
    have h2 := HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, y)) s hG (hasDerivAt_line s y)
    have h3 := ((ContinuousLinearMap.apply ℝ W ((0 : ℝ), v)).hasFDerivAt).comp_hasDerivAt s h2
    have he : (fun r => fderiv ℝ (u r) y v) = (⇑(ContinuousLinearMap.apply ℝ W ((0 : ℝ), v)) ∘
        (fderiv ℝ (Function.uncurry u)) ∘ fun r : ℝ => (r, y)) := by
      funext r
      simpa using fderiv_slice_eq hO hu r hy v
    rw [he]
    simpa using h3
  have hR : HasFDerivAt (fun z => deriv (fun r => u r z) s)
      ((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).comp
        ((fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y)).comp
          (ContinuousLinearMap.inr ℝ ℝ E))) y := by
    have h1 : HasFDerivAt (fun z : E => (s, z)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
      hasFDerivAt_prodMk_right s y
    have h2 := HasFDerivAt.comp (f := fun z : E => (s, z)) y hG h1
    have h3 := ((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).hasFDerivAt).comp y h2
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hy] with z hz
    simpa using deriv_eq hO hu s hz
  rw [hL.deriv, hR.fderiv]
  simpa using hsym.eq ((1 : ℝ), (0 : E)) ((0 : ℝ), v)

end Generic

theorem contDiff_mulRight {n : ℕ} (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff

end SmCalc

theorem sm_calculus : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (u : ℝ → Mat n → W), Sm u → Sm (dt u) ∧ (∀ X : Mat n, Sm (Rt X u)) ∧
      (∀ s, ContDiffOn ℝ ∞ (u s) (GLs n)) ∧ (∀ y ∈ GLs n, ContDiff ℝ ∞ fun s => u s y) ∧
      ∀ (X : Mat n) (s : ℝ), ∀ y ∈ GLs n, dt (Rt X u) s y = Rr X (dt u s) y :=
  fun _ hu => ⟨SmCalc.smooth_deriv isOpen_GLs hu,
    fun X => SmCalc.smooth_field isOpen_GLs hu (SmCalc.contDiff_mulRight X),
    SmCalc.smooth_slice hu, fun _ hy => SmCalc.smooth_line hu hy,
    fun _ s _ hy => SmCalc.deriv_fderiv_comm isOpen_GLs hu _ s hy⟩

end GlobalTheory.CompanionTheory.WaveSpd
