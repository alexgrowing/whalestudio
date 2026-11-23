import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtDelApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngleFormFrameIndep
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AngleGlue
open GlobalTheory.Twist (resM app_resM)
variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {E L L' : X.Modules} {r : ℕ} (h : Met p σ E r)

theorem contDiffAt_form (H : h.IsCInf) {U : X.Opens} (s₁ s₂ : Γ(E, U)) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ U) {D : ℕ} (c : AlgChart p σ D) (hc : y ∈ c.e.source) :
    ContDiffAt ℝ ∞ (fun v => h.form s₁ s₂ (c.e.symm v)) (c.e y) :=
  (H.gram ![s₁, s₂] hy 0 1).contDiffAt_chart c hc

theorem contDiffAt_re_form (H : h.IsCInf) {U : X.Opens} (s₁ s₂ : Γ(E, U)) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ U) {D : ℕ} (c : AlgChart p σ D) (hc : y ∈ c.e.source) :
    ContDiffAt ℝ ∞ (fun v => (h.form s₁ s₂ (c.e.symm v)).re) (c.e y) :=
  Complex.reCLM.contDiff.contDiffAt.comp _ (contDiffAt_form h H s₁ s₂ hy c hc)

theorem re_form_pos {l : L ⟶ E} (hl : IsSubbundle l) (hL : IsVB L 1) {U : X.Opens} (t : Γ(L, U))
    (ht : IsFrame (fun _ : Fin 1 => t)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    0 < (h.form (l.app U t) (l.app U t) y).re :=
  (Complex.pos_iff.1 (((h.restrict hl hL).posDef ⟨U, fun _ => t, ht⟩ y hy).diag_pos (i := 0))).1

theorem form_eq_of_resM {U U₂ W : X.Opens} (hW : W ≤ U) (hW₂ : W ≤ U₂) (x₁ x₂ : Γ(E, U))
    (y₁ y₂ : Γ(E, U₂)) (f₁ f₂ : Γ(X, W)) (e₁ : resM E hW₂ y₁ = f₁ • resM E hW x₁)
    (e₂ : resM E hW₂ y₂ = f₂ • resM E hW x₂) (z : CxPts p σ) (hz : z ∈ ptsIn p σ W) :
    h.form y₁ y₂ z = ev p σ W f₁ z * starRingEnd ℂ (ev p σ W f₂ z) * h.form x₁ x₂ z := by
  have key (s t : Γ(E, W)) (f : Γ(X, W)) :
      h.form s (f • t) z = starRingEnd ℂ (ev p σ W f z) * h.form s t z := by
    rw [← h.conj_form, h.form_smul_left, map_mul, h.conj_form]
  rw [← h.form_resM y₁ y₂ hW₂ hz, e₁, e₂, h.form_smul_left, key, h.form_resM _ _ hW hz]
  ring

theorem exists_eq_smul {U U₂ : X.Opens} (t : Γ(L, U)) (ht : IsFrame (fun _ : Fin 1 => t))
    (s : Γ(L, U₂)) : ∃ f : Γ(X, U ⊓ U₂),
      resM L (inf_le_right : U ⊓ U₂ ≤ U₂) s = f • resM L (inf_le_left : U ⊓ U₂ ≤ U) t := by
  refine ⟨(ht.basis (inf_le_left : U ⊓ U₂ ≤ U)).repr (resM L inf_le_right s) 0, ?_⟩
  have := (ht.basis (inf_le_left : U ⊓ U₂ ≤ U)).sum_repr (resM L inf_le_right s)
  rw [Fin.sum_univ_one, IsFrame.basis_apply] at this
  exact this.symm

theorem exists_app_eq_smul (l : L ⟶ E) {U U₂ : X.Opens} (t : Γ(L, U))
    (ht : IsFrame (fun _ : Fin 1 => t)) (s : Γ(L, U₂)) : ∃ f : Γ(X, U ⊓ U₂),
      resM E (inf_le_right : U ⊓ U₂ ≤ U₂) (l.app U₂ s) =
        f • resM E (inf_le_left : U ⊓ U₂ ≤ U) (l.app U t) := by
  obtain ⟨f, hf⟩ := exists_eq_smul t ht s
  exact ⟨f, by rw [← app_resM, hf, Scheme.Modules.Hom.app_smul, app_resM]⟩

variable {l : L ⟶ E} {l' : L' ⟶ E}

theorem angleForm_frames (H : h.IsCInf) (hl : IsSubbundle l) (hl' : IsSubbundle l')
    (hL : IsVB L 1) (hL' : IsVB L' 1) (n : ℕ) {U U₂ : X.Opens} (t : Γ(L, U)) (t' : Γ(L', U))
    (s : Γ(L, U₂)) (s' : Γ(L', U₂)) (ht : IsFrame (fun _ : Fin 1 => t))
    (ht' : IsFrame (fun _ : Fin 1 => t')) (hs : IsFrame (fun _ : Fin 1 => s))
    (hs' : IsFrame (fun _ : Fin 1 => s')) (c : AlgChart p σ 1) {y : CxPts p σ}
    (hc : y ∈ c.e.source) (hy : y ∈ ptsIn p σ U) (hy₂ : y ∈ ptsIn p σ U₂) (ξ : EuclideanSpace ℂ (Fin 1)) :
    angleForm n (fun v => (h.form (l.app U₂ s) (l.app U₂ s) (c.e.symm v)).re)
      (fun v => (h.form (l'.app U₂ s') (l'.app U₂ s') (c.e.symm v)).re)
      (fun v => h.form (l'.app U₂ s') (l.app U₂ s) (c.e.symm v)) ξ (c.e y) =
    angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
      (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
      (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) ξ (c.e y) := by
  obtain ⟨f, hf⟩ := exists_app_eq_smul l t ht s
  obtain ⟨g, hg⟩ := exists_app_eq_smul l' t' ht' s'
  have hW : y ∈ ptsIn p σ (U ⊓ U₂) := mem_ptsIn_inf.2 ⟨hy, hy₂⟩
  have hN : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ (U ⊓ U₂) :=
    eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn (U ⊓ U₂))).mem_nhds
      (ChartGlue.mem_over c.e hc hW)) fun _ hv => hv.2
  have hre (a b : ℂ) : (a * starRingEnd ℂ a * b).re = ‖a‖ ^ 2 * b.re := by
    rw [Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
  have ef := form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ f f hf hf
  have eg := form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ g g hg hg
  have eq := form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ g f hg hf
  have e0 := c.e.left_inv hc
  have hpos₂ := re_form_pos h hl hL s hs hy₂
  have hpos₂' := re_form_pos h hl' hL' s' hs' hy₂
  refine GlobalTheory.CurveDens.angleForm_frame_indep _ n _ _ _ _ _ _ (fun v => ev p σ (U ⊓ U₂) f (c.e.symm v))
    (fun v => ev p σ (U ⊓ U₂) g (c.e.symm v)) ξ (c.e y)
    ((contDiffAt_re_form h H _ _ hy c hc).differentiableAt (by simp))
    ((contDiffAt_re_form h H _ _ hy c hc).differentiableAt (by simp))
    ((contDiffAt_form h H _ _ hy c hc).differentiableAt (by simp))
    (by simp only [e0]; exact re_form_pos h hl hL t ht hy)
    (by simp only [e0]; exact re_form_pos h hl' hL' t' ht' hy)
    (c.differentiableAt_ev f hc hW) (c.differentiableAt_ev g hc hW) ?_ ?_ ?_ ?_ ?_
  · simp only [e0]
    intro h0
    rw [ef _ hW, h0] at hpos₂
    simp at hpos₂
  · simp only [e0]
    intro h0
    rw [eg _ hW, h0] at hpos₂'
    simp at hpos₂'
  · filter_upwards [hN] with v hv
    rw [ef _ hv, hre]
  · filter_upwards [hN] with v hv
    rw [eg _ hv, hre]
  · filter_upwards [hN] with v hv
    rw [eq _ hv]

theorem apply_single_eq_det_smul (A : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) :
    A (EuclideanSpace.single 0 1) = A.det • EuclideanSpace.single 0 1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 1) ℂ).toBasis,
    Matrix.det_unique]
  ext i
  simp [LinearMap.toMatrix_apply, Subsingleton.elim i 0]

end GlobalTheory.AngleGlue

open GlobalTheory.Twist (resM)

theorem GlobalTheory.angleForm_global : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (V L L' : X.Modules) (r : ℕ) (h : Met p σ V r) (l : L ⟶ V) (l' : L' ⟶ V), h.IsCInf → IsSubbundle l → IsSubbundle l' → IsVB L 1 → IsVB L' 1 → ∀ n : ℕ, ∃ m : AlgChart p σ 1 → CxPts p σ → ℂ, (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) ∧ (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) ∧ ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), IsFrame (fun _ : Fin 1 => t) → IsFrame (fun _ : Fin 1 => t') → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → m c y = angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re) (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re) (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y) := by
  intro k _ X p σ V L L' r h l l' H hl hl' hL hL' n
  let W : CxPts p σ → X.Opens := fun y => (hL.pick y).U ⊓ (hL'.pick y).U
  let T : ∀ y, Γ(L, W y) := fun y => resM L inf_le_left ((hL.pick y).e 0)
  let T' : ∀ y, Γ(L', W y) := fun y => resM L' inf_le_right ((hL'.pick y).e 0)
  have hT : ∀ y, IsFrame (fun _ : Fin 1 => T y) := fun y => by
    have := (hL.pick y).isFrame.res (inf_le_left : W y ≤ _)
    convert this using 2 with i
    rw [Subsingleton.elim i 0]
  have hT' : ∀ y, IsFrame (fun _ : Fin 1 => T' y) := fun y => by
    have := (hL'.pick y).isFrame.res (inf_le_right : W y ≤ _)
    convert this using 2 with i
    rw [Subsingleton.elim i 0]
  have hW : ∀ y, y ∈ ptsIn p σ (W y) := fun y => mem_ptsIn_inf.2 ⟨hL.mem_pick y, hL'.mem_pick y⟩
  refine ⟨fun c y => angleForm n
    (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
    (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
    (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
    (EuclideanSpace.single 0 1) (c.e y), ?_, ?_, ?_⟩
  · intro c y hc
    have e0 := c.e.left_inv hc
    have hG := (GlobalTheory.CurveDens.angleForm_props _ n
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
      (EuclideanSpace.single 0 1) (c.e y)).2.1
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      ((GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
    refine hG.congr_of_eventuallyEq ?_
    filter_upwards [(ChartGlue.isOpen_over c.e (isOpen_ptsIn (W y))).mem_nhds
      (ChartGlue.mem_over c.e hc (hW y))] with v hv
    have := GlobalTheory.AngleGlue.angleForm_frames h H hl hl' hL hL' n (T y) (T' y) (T (c.e.symm v))
      (T' (c.e.symm v)) (hT y) (hT' y) (hT _) (hT' _) c (c.e.map_target hv.1) hv.2 (hW _)
      (EuclideanSpace.single 0 1)
    exact this.trans (by rw [c.e.right_inv hv.1])
  · intro c c' y hc hc'
    have e0 := c.e.left_inv hc
    have e0' := c'.e.left_inv hc'
    have hN := (ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (ChartGlue.mem_over c.e hc hc')
    have hφz : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e e0
    have hφ : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) := (c.holo_trans c').differentiableAt hN
    have step1 := GlobalTheory.CurveDens.angleForm_frame_indep _ n
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm ((c'.e ∘ c.e.symm) v))).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y))
        (c'.e.symm ((c'.e ∘ c.e.symm) v))).re)
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm ((c'.e ∘ c.e.symm) v)))
      (fun _ => 1) (fun _ => 1) (EuclideanSpace.single 0 1) (c.e y)
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      ((GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
      (differentiableAt_const _) (differentiableAt_const _) one_ne_zero one_ne_zero
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
    have step2 := (GlobalTheory.CurveDens.angleForm_props _ n
      (fun w => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm w)).re)
      (fun w => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c'.e.symm w)).re)
      (fun w => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm w))
      (EuclideanSpace.single 0 1) (c.e y)).2.2 (c'.e ∘ c.e.symm) hφ
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; simp only [e0']; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by rw [hφz]; simp only [e0']; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
    have step3 := (GlobalTheory.CurveDens.angleForm_props _ n
      (fun w => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm w)).re)
      (fun w => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c'.e.symm w)).re)
      (fun w => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm w))
      (EuclideanSpace.single 0 1) (c'.e y)).1 (ChartGlue.transDet c.e c'.e y)
    rw [hφz, GlobalTheory.AngleGlue.apply_single_eq_det_smul] at step2
    exact step1.symm.trans (step2.trans step3)
  · intro U t t' ht ht' c y hc hy
    exact GlobalTheory.AngleGlue.angleForm_frames h H hl hl' hL hL' n t t' (T y) (T' y) ht ht' (hT y)
      (hT' y) c hc hy (hW y) _
