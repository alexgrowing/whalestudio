import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.WaveSpd.DensDeriv

section Generic

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def tD (u : ℝ → E → W) : ℝ → E → W := fun s y => deriv (fun r => u r y) s

def rD (L : E →L[ℝ] E) (u : ℝ → E → W) : ℝ → E → W := fun s y => fderiv ℝ (u s) y (L y)

variable {U : Set E} {u : ℝ → E → W}

theorem contDiffAt_F (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    ContDiffAt ℝ ∞ (Function.uncurry u) (s, y) :=
  hu.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ _, hy⟩)

theorem hasFDerivAt_F (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (s, y)) (s, y) :=
  ((contDiffAt_F hU hu s hy).differentiableAt (by simp)).hasFDerivAt

theorem hasDerivAt_line (y : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => ((r, y) : ℝ × E)) ((1 : ℝ), (0 : E)) s :=
  (hasDerivAt_id s).prodMk (hasDerivAt_const s y)

theorem hasDerivAt_time (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    HasDerivAt (fun r => u r y) (fderiv ℝ (Function.uncurry u) (s, y) (1, 0)) s :=
  by
  have h : HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (s, y))
      ((fun r : ℝ => ((r, y) : ℝ × E)) s) := hasFDerivAt_F hU hu s hy
  exact h.comp_hasDerivAt s (hasDerivAt_line y s)

theorem tD_eq (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    tD u s y = fderiv ℝ (Function.uncurry u) (s, y) (1, 0) :=
  (hasDerivAt_time hU hu s hy).deriv

theorem rD_eq (L : E →L[ℝ] E) (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    rD L u s y = fderiv ℝ (Function.uncurry u) (s, y) (0, L y) := by
  have h2 := (hasFDerivAt_F hU hu s hy).comp y (hasFDerivAt_prodMk_right s y)
  have h3 : fderiv ℝ (u s) y = _ := HasFDerivAt.fderiv (f := u s) h2
  simp only [rD]
  rw [h3]
  simp

theorem contDiffOn_fderivF (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ U) :=
  hu.fderiv_of_isOpen (isOpen_univ.prod hU) (by simp)

theorem contDiffOn_tD (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (Function.uncurry (tD u)) (Set.univ ×ˢ U) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E => fderiv ℝ (Function.uncurry u) p (1, 0))
      (Set.univ ×ˢ U) :=
    (contDiffOn_fderivF hU hu).clm_apply contDiffOn_const
  refine h.congr ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact tD_eq hU hu s hy

theorem tD_rD (L : E →L[ℝ] E) (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    HasDerivAt (fun r => rD L u r y) (fderiv ℝ (tD u s) y (L y)) s := by
  set F := Function.uncurry u with hF
  have hD : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (s, y)) (s, y) :=
    (((contDiffOn_fderivF hU hu).contDiffAt
      ((isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
      (by simp)).hasFDerivAt
  have hL : HasDerivAt (fun r => rD L u r y)
      (fderiv ℝ (fderiv ℝ F) (s, y) (1, 0) (0, L y)) s := by
    have h2 : HasDerivAt (fun r => fderiv ℝ F (r, y))
        (fderiv ℝ (fderiv ℝ F) (s, y) (1, 0)) s :=
      hD.comp_hasDerivAt s (hasDerivAt_line y s)
    have h3 := h2.clm_apply (hasDerivAt_const s ((0 : ℝ), L y))
    simp only [ContinuousLinearMap.map_zero, add_zero] at h3
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    exact rD_eq L hU hu r hy
  have hR : HasFDerivAt (tD u s)
      (((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).comp
        (fderiv ℝ (fderiv ℝ F) (s, y))).comp (ContinuousLinearMap.inr ℝ ℝ E)) y := by
    have h2 := (ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).hasFDerivAt.comp y
      (hD.comp y (hasFDerivAt_prodMk_right s y))
    refine HasFDerivAt.congr_of_eventuallyEq h2 ?_
    filter_upwards [hU.mem_nhds hy] with z hz
    exact tD_eq hU hu s hz
  have hsym : IsSymmSndFDerivAt ℝ F (s, y) :=
    (contDiffAt_F hU hu s hy).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [hR.fderiv]
  have e : fderiv ℝ (fderiv ℝ F) (s, y) (1, 0) (0, L y)
      = fderiv ℝ (fderiv ℝ F) (s, y) (0, L y) (1, 0) := hsym _ _
  simpa [e] using hL

end Generic

section Mat

variable {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g * X
      map_add' := fun a b => Matrix.add_mul a b X
      map_smul' := fun c a => by simp }

theorem sm_dt {u : ℝ → Mat n → W} (hu : Sm u) : Sm (dt u) :=
  contDiffOn_tD isOpen_GLs hu

theorem hasDerivAt_dt {u : ℝ → Mat n → W} (hu : Sm u) (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    HasDerivAt (fun r => u r y) (dt u s y) s := by
  have h := hasDerivAt_time isOpen_GLs hu s hy
  rwa [← tD_eq isOpen_GLs hu s hy] at h

theorem hasDerivAt_Rt {u : ℝ → Mat n → W} (hu : Sm u) (X : Mat n) (s : ℝ) {y : Mat n}
    (hy : y ∈ GLs n) : HasDerivAt (fun r => Rt X u r y) (Rr X (dt u s) y) s :=
  tD_rD (mulR X) isOpen_GLs hu s hy

end Mat

end GlobalTheory.CompanionTheory.WaveSpd.DensDeriv

open GlobalTheory.CompanionTheory.WaveSpd.DensDeriv in

theorem GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens {n : ℕ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (u : ℝ → Mat n → W) (hu : Sm u) (s : ℝ) (y : Mat n)
    (hy : y ∈ GLs n) :
    HasDerivAt (fun r => dens u r y)
      (2 * ⟪dt (dt u) s y, dt u s y⟫_ℝ
        + (1 / 2) * ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ
        + 2 * ⟪dt u s y, u s y⟫_ℝ) s := by
  have h1 := (hasDerivAt_dt (sm_dt hu) s hy).norm_sq
  have h3 := (hasDerivAt_dt hu s hy).norm_sq
  have h2 : HasDerivAt (fun r => ∑ p : Ix n, ‖Rt (hm p) u r y‖ ^ 2)
      (∑ p : Ix n, 2 * ⟪Rt (hm p) u s y, Rr (hm p) (dt u s) y⟫_ℝ) s := by
    have := HasDerivAt.fun_sum (u := Finset.univ)
      (fun (p : Ix n) _ => (hasDerivAt_Rt hu (hm p) s hy).norm_sq)
    exact this
  have h := (h1.add (h2.const_mul (1 / 4 : ℝ))).add h3
  refine (h.congr_deriv ?_)
  rw [real_inner_comm (dt (dt u) s y), real_inner_comm (dt u s y) (u s y), ← Finset.mul_sum]
  simp only [real_inner_comm (Rt _ u s y)]
  ring
