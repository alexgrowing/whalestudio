import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuDsDer

section general

variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]

def dL (a : E → E) (Φ : E × E' → V) (q : E × E') : V := fderiv ℝ Φ q (a q.1, 0)

def dR (b : E' → E') (Φ : E × E' → V) (q : E × E') : V := fderiv ℝ Φ q (0, b q.2)

theorem contDiff_dL {a : E → E} (ha : ContDiff ℝ ∞ a) {Φ : E × E' → V} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (dL a Φ) := by
  exact (contDiff_infty_iff_fderiv.1 hΦ).2.clm_apply ((ha.comp contDiff_fst).prodMk contDiff_const)

theorem contDiff_dR {b : E' → E'} (hb : ContDiff ℝ ∞ b) {Φ : E × E' → V} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (dR b Φ) := by
  exact (contDiff_infty_iff_fderiv.1 hΦ).2.clm_apply (contDiff_const.prodMk (hb.comp contDiff_snd))

theorem dR_dL {a : E → E} (ha : ContDiff ℝ ∞ a) {b : E' → E'} (hb : ContDiff ℝ ∞ b) {Φ : E × E' → V}
    (hΦ : ContDiff ℝ ∞ Φ) : dR b (dL a Φ) = dL a (dR b Φ) := by
  funext q
  have hΦ1 : ContDiff ℝ ∞ (fderiv ℝ Φ) := (contDiff_infty_iff_fderiv.1 hΦ).2
  have hc : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) q) q :=
    ((hΦ1.differentiable (by simp)) q).hasFDerivAt
  have hua : HasFDerivAt (fun q : E × E' => (a q.1, (0 : E')))
      (((fderiv ℝ a q.1).comp (ContinuousLinearMap.fst ℝ E E')).prod 0) q :=
    (((ha.differentiable (by simp)) q.1).hasFDerivAt.comp q hasFDerivAt_fst).prodMk (hasFDerivAt_const 0 q)
  have hub : HasFDerivAt (fun q : E × E' => ((0 : E), b q.2))
      ((0 : E × E' →L[ℝ] E).prod ((fderiv ℝ b q.2).comp (ContinuousLinearMap.snd ℝ E E'))) q :=
    (hasFDerivAt_const 0 q).prodMk (((hb.differentiable (by simp)) q.2).hasFDerivAt.comp q hasFDerivAt_snd)
  have hsymm := ((contDiff_infty.1 hΦ 2).contDiffAt (x := q)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  show fderiv ℝ (dL a Φ) q (0, b q.2) = fderiv ℝ (dR b Φ) q (a q.1, 0)
  rw [show dL a Φ = fun y => fderiv ℝ Φ y (a y.1, 0) from rfl,
    show dR b Φ = fun y => fderiv ℝ Φ y (0, b y.2) from rfl,
    (hc.clm_apply hua).fderiv, (hc.clm_apply hub).fderiv]
  simp
  exact hsymm _ _

end general

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def dW (W : List (Mat n)) (Φ : Mat n × Mat n → H) : Mat n × Mat n → H :=
  W.foldr (fun Y => dL fun g => g * Y) Φ

theorem contDiff_mulR (Y : Mat n) : ContDiff ℝ ∞ fun g : Mat n => g * Y := by
  exact contDiff_mul' contDiff_id contDiff_const

theorem contDiff_dW {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) : ∀ W, ContDiff ℝ ∞ (dW W Φ) := by
  intro W
  induction W with
  | nil => exact hΦ
  | cons Y W ih => exact contDiff_dL (contDiff_mulR Y) ih

theorem dR_dW {b : Mat n → Mat n} (hb : ContDiff ℝ ∞ b) {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) :
    ∀ W, dR b (dW W Φ) = dW W (dR b Φ) := by
  intro W
  induction W with
  | nil => rfl
  | cons Y W ih =>
    show dR b (dL (fun g => g * Y) (dW W Φ)) = dL (fun g => g * Y) (dW W (dR b Φ))
    rw [dR_dL (contDiff_mulR Y) hb (contDiff_dW hΦ W), ih]

theorem hasDerivAt_dL {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) (Y g y : Mat n) :
    HasDerivAt (fun t => Φ (g * ex Y t, y)) (dL (fun g => g * Y) Φ (g, y)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (g * ex Y t, y)) (g * Y, (0 : Mat n)) 0 :=
    (hasDerivAt_mul_ex g Y).prodMk (hasDerivAt_const 0 y)
  have h0 : (g, y) = (g * ex Y 0, y) := by rw [ex_zero, mul_one]
  exact ((hΦ.differentiable (by simp)) (g, y)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ h0

theorem hasDerivAt_dR {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) (X g y : Mat n) :
    HasDerivAt (fun t => Φ (g, y * ex X t)) (dR (fun y => y * X) Φ (g, y)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (g, y * ex X t)) ((0 : Mat n), y * X) 0 :=
    (hasDerivAt_const 0 g).prodMk (hasDerivAt_mul_ex y X)
  have h0 : (g, y) = (g, y * ex X 0) := by rw [ex_zero, mul_one]
  exact ((hΦ.differentiable (by simp)) (g, y)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ h0

variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

private theorem dW_eq_smul_dsW_of_eq_on_open (h : RepOn G σ) {u : H} (hu : IsSm G σ u) {Φ : Mat n × Mat n → H}
    (hΦ : ContDiff ℝ ∞ Φ) {y : Mat n} {O : Set (Mat n)} (hO : IsOpen O)
    (hΦu : ∀ g ∈ G, g ∈ O → Φ (g, y) = σ g u) :
    ∀ {W : List (Mat n)}, LieW G W → ∀ g ∈ G, g ∈ O → dW W Φ (g, y) = σ g (dsW σ W u) := by
  intro W
  induction W with
  | nil => intro _ g hg hgO; exact hΦu g hg hgO
  | cons Y W ih =>
    intro hW g hg hgO
    have hY : ∀ t, ex Y t ∈ G := hW Y (by simp)
    have hW' : LieW G W := fun X hX => hW X (by simp [hX])
    have hc : ContinuousAt (fun t : ℝ => g * ex Y t) 0 := (hasDerivAt_mul_ex g Y).continuousAt
    have hO' : O ∈ nhds (g * ex Y 0) := by rw [ex_zero, mul_one]; exact hO.mem_nhds hgO
    have hev : (fun t => σ (g * ex Y t) (dsW σ W u)) =ᶠ[nhds 0] fun t => dW W Φ (g * ex Y t, y) := by
      filter_upwards [hc.preimage_mem_nhds hO'] with t ht
      exact (ih hW' _ (h.mul_mem g hg _ (hY t)) ht).symm
    have hd := (hasDerivAt_dL (contDiff_dW hΦ W) Y g y).congr_of_eventuallyEq hev
    rw [dsW_cons, apply_ds h hY hg (CompanionTheory.D.Upq.Sm.IsSm.differentiableAt h (CompanionTheory.D.Upq.Sm.IsSm.dsW h hu hW') hY)]
    exact hd.deriv.symm

private theorem hasDerivAt_dsW_smul_mul_ex (h : RepOn G σ) {x : H} (hx : IsSm G σ x) {F : Mat n → H}
    (hF : ContDiff ℝ ∞ F) {O : Set (Mat n)} (hO : IsOpen O) (hFx : ∀ g ∈ G, g ∈ O → σ g x = F g)
    {W : List (Mat n)} (hW : LieW G W) {p : Mat n} (hp : p ∈ G) (hpO : p ∈ O) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) :
    HasDerivAt (fun τ : ℝ => dsW σ W (σ (p * ex X τ) x)) (dsW σ W (σ p (ds σ X x))) 0 := by
  have hΦ : ContDiff ℝ ∞ (fun q : Mat n × Mat n => F (q.1 * q.2)) := hF.comp contDiff_mul
  have h1 : (1 : Mat n) ∈ G := h.one_mem
  have hσ1 : ∀ v, σ 1 v = v := fun v => by rw [h.map_one]; rfl
  have hcont : ∀ y : Mat n, Continuous (fun g : Mat n => g * y) := fun y => (contDiff_mulR y).continuous
  have hpτ : ∀ᶠ τ in nhds (0 : ℝ), p * ex X τ ∈ O := by
    have hc : ContinuousAt (fun t : ℝ => p * ex X t) 0 := (hasDerivAt_mul_ex p X).continuousAt
    have hO' : O ∈ nhds (p * ex X 0) := by rw [ex_zero, mul_one]; exact hO.mem_nhds hpO
    exact hc.preimage_mem_nhds hO'
  have hev : (fun τ : ℝ => dW W (fun q : Mat n × Mat n => F (q.1 * q.2)) (1, p * ex X τ)) =ᶠ[nhds 0]
      fun τ : ℝ => dsW σ W (σ (p * ex X τ) x) := by
    filter_upwards [hpτ] with τ hτ
    have hpτG : p * ex X τ ∈ G := h.mul_mem p hp _ (hX τ)
    have key := dW_eq_smul_dsW_of_eq_on_open (y := p * ex X τ) (O := (fun g => g * (p * ex X τ)) ⁻¹' O) h
      (CompanionTheory.D.Upq.Sm.IsSm.apply h hx hpτG) hΦ (hO.preimage (hcont _))
      (fun g hg hgO => by
        show F (g * (p * ex X τ)) = σ g (σ (p * ex X τ) x)
        rw [← hFx _ (h.mul_mem g hg _ hpτG) hgO, h.apply_mul hg hpτG]) hW 1 h1
      (by show 1 * (p * ex X τ) ∈ O; rw [one_mul]; exact hτ)
    rw [key, hσ1]
  have hd := hasDerivAt_dR (contDiff_dW hΦ W) X 1 p
  rw [dR_dW (contDiff_mulR X) hΦ W] at hd
  have hX1 : LieW G [X] := by
    intro Y hY t
    simp only [List.mem_singleton] at hY
    subst hY
    exact hX t
  have hds : IsSm G σ (ds σ X x) := CompanionTheory.D.Upq.Sm.IsSm.dsW h hx hX1
  have hΦ2 : ∀ g ∈ G, g ∈ (fun g => g * p) ⁻¹' O →
      dR (fun y => y * X) (fun q : Mat n × Mat n => F (q.1 * q.2)) (g, p) = σ g (σ p (ds σ X x)) := by
    intro g hg hgO
    rw [← (hasDerivAt_dR hΦ X g p).deriv]
    have hgp : g * p ∈ G := h.mul_mem g hg p hp
    rw [← h.apply_mul hg hp, apply_ds h hX hgp (CompanionTheory.D.Upq.Sm.IsSm.differentiableAt h hx hX)]
    apply Filter.EventuallyEq.deriv_eq
    have hc : ContinuousAt (fun t : ℝ => g * p * ex X t) 0 := (hasDerivAt_mul_ex (g * p) X).continuousAt
    have hO' : O ∈ nhds (g * p * ex X 0) := by rw [ex_zero, mul_one]; exact hO.mem_nhds hgO
    filter_upwards [hc.preimage_mem_nhds hO'] with t ht
    show F (g * (p * ex X t)) = σ (g * p * ex X t) x
    rw [← mul_assoc, hFx _ (h.mul_mem _ hgp _ (hX t)) ht]
  have key2 := dW_eq_smul_dsW_of_eq_on_open h (CompanionTheory.D.Upq.Sm.IsSm.apply h hds hp) (contDiff_dR (contDiff_mulR X) hΦ)
    (hO.preimage (hcont p)) hΦ2 hW 1 h1 (by show 1 * p ∈ O; rw [one_mul]; exact hpO)
  rw [key2, hσ1] at hd
  exact hd.congr_of_eventuallyEq hev.symm

private theorem exists_contDiff_eq_on_nhds_of_contDiffOn {F : Mat n → H} {U : Set (Mat n)} {p : Mat n} (hU : IsOpen U) (hpU : p ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) :
    ∃ F' : Mat n → H, ContDiff ℝ ∞ F' ∧ ∃ O : Set (Mat n), IsOpen O ∧ p ∈ O ∧ O ⊆ U ∧ ∀ g ∈ O, F' g = F g := by
  obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.1 hU p hpU
  let φ : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨fun g => (φ g : ℝ) • F g, ?_, Metric.ball p (r / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), fun g hg => hrU (Metric.ball_subset_ball (by linarith) hg),
    fun g hg => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ Metric.ball p r
    · exact (φ.contDiff.contDiffAt).smul (hF.contDiffAt (hU.mem_nhds (hrU hz)))
    · have hzc : z ∈ (Metric.closedBall p (r / 2))ᶜ := by
        intro hz'
        exact hz (Metric.closedBall_subset_ball (by linarith) hz')
      have hev0 : ∀ᶠ g in nhds z, φ g = 0 := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hzc] with g hg
        apply φ.zero_of_le_dist
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hg
        exact hg.le
      have hev : (fun g => (φ g : ℝ) • F g) =ᶠ[nhds z] fun _ => (0 : H) := by
        filter_upwards [hev0] with g hg
        simp [hg]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · show (φ g : ℝ) • F g = F g
    rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hg), one_smul]

theorem dsDer : DsDer := by
  intro n Hm H _ _ _ σ hσ W hW p hp X hX x hx
  have h := hσ.rep
  have hLX : ∀ Y : Mat n, CompanionTheory.Bmu.Lie Hm Y → ∀ t, ex Y t ∈ Formalism.QuantumDeterminants.UH Hm :=
    fun Y hY t => ex_mem_of_lie hY t
  obtain ⟨U, F, hU, hpU, hFU, hFx⟩ := hx p hp
  obtain ⟨F', hF', O, hO, hpO, hOU, hF'O⟩ := exists_contDiff_eq_on_nhds_of_contDiffOn hU hpU hFU
  exact hasDerivAt_dsW_smul_mul_ex h hx hF' hO
    (fun g hg hgO => by rw [hF'O g hgO]; exact hFx g (hOU hgO) hg)
    (fun Y hY => hLX Y (hW Y hY)) hp hpO (hLX X hX)

end GlobalTheory.CompanionTheory.BmuDsDer

end
