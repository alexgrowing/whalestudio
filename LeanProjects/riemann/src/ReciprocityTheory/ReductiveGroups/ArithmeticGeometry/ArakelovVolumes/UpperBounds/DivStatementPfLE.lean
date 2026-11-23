import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLD

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix

noncomputable section

theorem coordL {n : ℕ} (W : V n → ℂ) (S : Fin n → V n → ℂ) (hW : AnalyticAt ℂ W 0) (hW0 : W 0 ≠ 0)
    (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => S k z / W z : V n)) 0).det ≠ 0) :
    ∃ L : V n ≃L[ℂ] V n, (∀ k z, (L z) k = fderiv ℂ (fun y => S k y / W y) 0 z) ∧
      (fun z => (WithLp.toLp 2 fun k => S k z / W z : V n) - L z) =o[𝓝 0] fun z => z := by
  classical
  let F : V n → V n := fun z => (WithLp.toLp 2 fun k => S k z / W z : V n)
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)
  have hcomp : ∀ k, DifferentiableAt ℂ (fun y => S k y / W y) 0 :=
    fun k => ((hS k).div hW hW0).differentiableAt
  have hG : DifferentiableAt ℂ (fun z k => S k z / W z) 0 := differentiableAt_pi.2 hcomp
  have hFd : DifferentiableAt ℂ F 0 := e.symm.differentiableAt.comp 0 hG
  have hdet' : LinearMap.det (fderiv ℂ F 0 : V n →ₗ[ℂ] V n) ≠ 0 := hdet
  let L : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ F 0 : V n →ₗ[ℂ] V n) hdet').toContinuousLinearEquiv
  have hL : ∀ z, L z = fderiv ℂ F 0 z := fun z => rfl
  refine ⟨L, fun k z => ?_, ?_⟩
  · rw [hL]
    have h1' := ((PiLp.proj 2 (fun _ : Fin n => ℂ) k).hasFDerivAt (x := F 0)).comp (0 : V n) hFd.hasFDerivAt
    have h1 : HasFDerivAt (fun y => S k y / W y)
        ((PiLp.proj 2 (fun _ : Fin n => ℂ) k).comp (fderiv ℂ F 0)) 0 := h1'
    rw [h1.fderiv]
    rfl
  · have h2 := hFd.hasFDerivAt.isLittleO
    have hF0 : F 0 = 0 := by
      apply PiLp.ext
      intro k
      simp [F, hS0]
    simp only [hF0, sub_zero] at h2
    exact h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem leadM_anal {r : ℕ} (X : Data E r) {Xa : ArchInM X} (Fl : FlatM X Xa) {δ : ℕ}
    (t : Fin δ → Frame X.Ψ r → ℂ) (ht : ∀ k, DifferentiableOn ℂ (t k) X.dom) (T d : ℕ)
    (cc : (Fin (nd X) → ℕ) → Fin δ → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    AnalyticAt ℂ (fun z => leadM X Fl.s Fl.w0 t T d cc (cpt X x z)) 0 := by
  unfold leadM monoM
  have hs : ∀ i, AnalyticAt ℂ (fun z => Fl.s i (cpt X x z)) 0 :=
    fun i => anal_loc X (Fl.s_van i).1.1.1.1 hx
  have hw := anal_loc X Fl.weightForm_vanishes.1.1.1.1 hx
  have hterm : ∀ (α : Fin (nd X) → ℕ) (k : Fin δ), AnalyticAt ℂ (fun z => cc α k *
      (∏ i, Fl.s i (cpt X x z) ^ α i) * Fl.w0 (cpt X x z) ^ (T - ∑ q, α q) * t k (cpt X x z)) 0 := by
    intro α k
    have hp : AnalyticAt ℂ (fun z => ∏ i, Fl.s i (cpt X x z) ^ α i) 0 :=
      Finset.analyticAt_fun_prod _ fun i _ => (hs i).pow _
    exact ((analyticAt_const.mul hp).mul (hw.pow _)).mul (anal_loc X (ht k) hx)
  have hk : ∀ α : Fin (nd X) → ℕ, AnalyticAt ℂ (fun z => ∑ k, cc α k *
      (∏ i, Fl.s i (cpt X x z) ^ α i) * Fl.w0 (cpt X x z) ^ (T - ∑ q, α q) * t k (cpt X x z)) 0 :=
    fun α => Finset.analyticAt_fun_sum _ fun k _ => hterm α k
  exact Finset.analyticAt_fun_sum _ fun α _ => hk α

theorem lead_ind {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) {δ : ℕ}
    (t : Fin δ → Frame X.Ψ r → ℂ) (ht : ∀ k, X.IsSec Xa.Fp (t k)) (hval : IsValBasisM X Fl.xs t)
    (f : Frame X.Ψ r → ℂ) (hf : X.IsSec (Xa.Fp + Xa.T • Xa.L) f) :
    ∀ d, d ≤ Xa.T → ∃ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f (cpt X (Fl.xs j) z) - leadM X Fl.s Fl.w0 t Xa.T d cc (cpt X (Fl.xs j) z)) =O[𝓝 0]
        fun z => ‖z‖ ^ d := by
  classical
  choose b hb using hval.1
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨0, fun j => ?_⟩
    have hc : (fun z => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun _ => (1 : ℝ) :=
      (anal_loc X hf.1 (Fl.xs_mem j)).continuousAt.tendsto.isBigO_one ℝ
    refine hc.congr (fun z => ?_) (fun z => by simp)
    simp [leadM, ReciprocityTheory.ChartRestriction.G.AR.multiLt]
  | succ d ih =>
    intro hd
    obtain ⟨cc, hcc⟩ := ih (by omega)
    have hloc : ∀ j, ∃ a : (Fin (nd X) → ℕ) → ℂ, ∀ c : (Fin (nd X) → ℕ) → Fin δ → ℂ,
        (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) d,
          ∑ k, c α k * t k (cpt X (Fl.xs j) 0) * Fl.w0 (cpt X (Fl.xs j) 0) ^ Xa.T = a α) →
        (fun z => (f (cpt X (Fl.xs j) z) - leadM X Fl.s Fl.w0 t Xa.T d cc (cpt X (Fl.xs j) z)) -
          ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) d, ∑ k, c α k *
            (∏ i, Fl.s i (cpt X (Fl.xs j) z) ^ α i) * Fl.w0 (cpt X (Fl.xs j) z) ^ (Xa.T - d) *
              t k (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (d + 1) := by
      intro j
      have hx := Fl.xs_mem j
      have hW := anal_loc X Fl.weightForm_vanishes.1.1.1.1 hx
      have hW0 : Fl.w0 (cpt X (Fl.xs j) 0) ≠ 0 := by rw [cpt_zero']; exact Fl.w0_ne j
      have hS := fun i => anal_loc X (Fl.s_van i).1.1.1.1 hx
      have hS0 : ∀ i, Fl.s i (cpt X (Fl.xs j) 0) = 0 := fun i => by
        rw [cpt_zero']; exact s_xs_zero X Fl j i
      obtain ⟨L, hL, -⟩ := coordL _ _ hW hW0 hS hS0 (Fl.coord j)
      exact DivLA.local_step (by omega) _ _ (fun k z => t k (cpt X (Fl.xs j) z)) L hW hW0 hS hS0
        (fun k => anal_loc X (ht k).1 hx) hL _
        ((anal_loc X hf.1 hx).sub (leadM_anal X Fl t (fun k => (ht k).1) _ _ _ hx)) (hcc j)
    choose a ha using hloc
    let cnew : (Fin (nd X) → ℕ) → Fin δ → ℂ :=
      fun α => b (fun j' => a j' α / Fl.w0 (Fl.xs j') ^ Xa.T)
    let cc' : (Fin (nd X) → ℕ) → Fin δ → ℂ :=
      fun α => if α ∈ Finset.Nat.antidiagonalTuple (nd X) d then cnew α else cc α
    refine ⟨cc', fun j => ?_⟩
    have hcond : ∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) d,
        ∑ k, cnew α k * t k (cpt X (Fl.xs j) 0) * Fl.w0 (cpt X (Fl.xs j) 0) ^ Xa.T = a j α := by
      intro α _
      rw [cpt_zero', ← Finset.sum_mul]
      show (∑ k, b (fun j' => a j' α / Fl.w0 (Fl.xs j') ^ Xa.T) k * t k (Fl.xs j)) *
        Fl.w0 (Fl.xs j) ^ Xa.T = a j α
      rw [hb]
      exact div_mul_cancel₀ _ (pow_ne_zero _ (Fl.w0_ne j))
    refine (ha j cnew hcond).congr_left fun z => ?_
    rw [leadM_succ X Fl.s Fl.w0 t Xa.T d cc cc' cnew (fun α hα => if_pos hα) (fun α hα => if_neg hα)]
    simp only [monoM]
    ring

theorem divLead_holds : DivLeadStatement (E := E) := by
  intro r X Xa Fl δ t ht hval f hf
  obtain ⟨cc, hcc⟩ := lead_ind X Xa Fl t ht hval f hf (Xa.T - nd X) (Nat.sub_le _ _)
  refine ⟨cc, fun j => ?_⟩
  have hx := Fl.xs_mem j
  have hW := anal_loc X Fl.weightForm_vanishes.1.1.1.1 hx
  have hW0 : Fl.w0 (cpt X (Fl.xs j) 0) ≠ 0 := by rw [cpt_zero']; exact Fl.w0_ne j
  have hS := fun i => anal_loc X (Fl.s_van i).1.1.1.1 hx
  have hS0 : ∀ i, Fl.s i (cpt X (Fl.xs j) 0) = 0 := fun i => by
    rw [cpt_zero']; exact s_xs_zero X Fl j i
  obtain ⟨L, -, hLo⟩ := coordL _ _ hW hW0 hS hS0 (Fl.coord j)
  obtain ⟨c1, hc1, hlow⟩ := DivLA.lower_of_deriv L hLo
  set w := ‖Fl.w0 (cpt X (Fl.xs j) 0)‖ with hwdef
  have hw : 0 < w := norm_pos_iff.2 hW0
  have hWev : ∀ᶠ z in 𝓝 (0 : V (nd X)), w / 2 < ‖Fl.w0 (cpt X (Fl.xs j) z)‖ :=
    hW.continuousAt.norm.eventually (lt_mem_nhds (by linarith))
  have hSlow : ∀ᶠ z in 𝓝 (0 : V (nd X)),
      ((w / 2) ^ 2 * c1 ^ 2) * ‖z‖ ^ 2 ≤ ∑ k, ‖Fl.s k (cpt X (Fl.xs j) z)‖ ^ 2 := by
    filter_upwards [hlow, hWev] with z h1 h2
    have hWz : Fl.w0 (cpt X (Fl.xs j) z) ≠ 0 := by
      intro h; rw [h, norm_zero] at h2; linarith
    have hnorm : ‖(WithLp.toLp 2 fun k => Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) :
        V (nd X))‖ ^ 2 * ‖Fl.w0 (cpt X (Fl.xs j) z)‖ ^ 2 = ∑ k, ‖Fl.s k (cpt X (Fl.xs j) z)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : ‖Fl.w0 (cpt X (Fl.xs j) z)‖ ≠ 0 := norm_ne_zero_iff.2 hWz
      simp only [norm_div, div_pow]
      field_simp
    rw [← hnorm]
    have h3 : c1 * ‖z‖ * (w / 2) ≤
        ‖(WithLp.toLp 2 fun k => Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))‖ *
          ‖Fl.w0 (cpt X (Fl.xs j) z)‖ :=
      mul_le_mul h1 h2.le (by positivity) (norm_nonneg _)
    have h4 := pow_le_pow_left₀ (by positivity) h3 2
    calc (w / 2) ^ 2 * c1 ^ 2 * ‖z‖ ^ 2 = (c1 * ‖z‖ * (w / 2)) ^ 2 := by ring
      _ ≤ _ := h4
      _ = _ := by ring
  have hn : 1 ≤ nd X := le_trans (by norm_num) Xa.n_ge
  exact DivLA.vanS_int hn (hcc j) (by positivity) hSlow

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
