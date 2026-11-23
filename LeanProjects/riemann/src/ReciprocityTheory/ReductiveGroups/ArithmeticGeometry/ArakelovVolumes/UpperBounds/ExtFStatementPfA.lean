import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure LUData (X : Data E r) (x0 : Frame X.Ψ r) where
  Δ : Frame X.Ψ r → ℂ
  zOf : Frame X.Ψ r → V (nd X)
  bOf : Frame X.Ψ r → Frame X.Ψ r
  hΔ : Differentiable ℂ Δ
  dense : ∀ x ∈ X.dom, ∀ ε > 0, ∃ y ∈ Metric.ball x ε, Δ y ≠ 0
  hz : DifferentiableOn ℂ zOf {x | x ∈ X.dom ∧ Δ x ≠ 0}
  hb : DifferentiableOn ℂ bOf {x | x ∈ X.dom ∧ Δ x ≠ 0}
  split : ∀ x ∈ X.dom, Δ x ≠ 0 → zOf x ∈ OmF X x0 ∧ bOf x ∈ Bor X.Ψ r ∧
    x = rmul (cpt X x0 (zOf x)) (bOf x)
  uniq : ∀ z ∈ OmF X x0, ∀ b ∈ Bor X.Ψ r, Δ (rmul (cpt X x0 z) b) ≠ 0 ∧
    zOf (rmul (cpt X x0 z) b) = z ∧ bOf (rmul (cpt X x0 z) b) = b

theorem luData_of (hLU : LUStatement (E := E)) (X : Data E r) (x0 : Frame X.Ψ r) (hx0 : IsOrth X x0) :
    Nonempty (LUData X x0) := by
  obtain ⟨Δ, zOf, bOf, h1, h2, h3, h4, h5, h6⟩ := hLU r X x0 hx0
  exact ⟨⟨Δ, zOf, bOf, h1, h2, h3, h4, h5, h6⟩⟩

variable (X : Data E r)

def oneF : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

private lemma mem_bor_iff' {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} :
    b ∈ Bor Ψ r ↔ ∀ τ : Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 :=
  Iff.rfl

private lemma mat_rmul' {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) :
    mat (rmul x b) τ = mat x τ * mat b τ :=
  rfl

theorem oneF_mem : oneF X ∈ Bor X.Ψ r := by
  rw [mem_bor_iff']
  intro τ
  refine ⟨?_, fun a c h => ?_⟩
  · show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne (ne_of_gt h)

theorem rmul_oneF (x : Frame X.Ψ r) : rmul x (oneF X) = x := by
  funext τ
  show mat x τ * (1 : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Matrix.mul_one]
  rfl

theorem rmul_assoc (x b b' : Frame X.Ψ r) : rmul (rmul x b) b' = rmul x (rmul b b') := by
  funext τ
  show mat x τ * mat b τ * mat b' τ = mat x τ * (mat b τ * mat b' τ)
  exact Matrix.mul_assoc _ _ _

theorem upper_iff (b : Frame X.Ψ r) (τ : X.Ψ) :
    (∀ a c : Fin r, c < a → b τ a c = 0) ↔ (mat b τ).BlockTriangular id := by
  exact ⟨fun h a c hca => h a c hca, fun h a c hca => h hca⟩

theorem mul_mem {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    rmul b b' ∈ Bor X.Ψ r := by
  rw [mem_bor_iff']
  intro τ
  refine ⟨?_, ?_⟩
  · rw [mat_rmul', Matrix.det_mul]
    exact mul_ne_zero (mem_bor_iff'.1 hb τ).1 (mem_bor_iff'.1 hb' τ).1
  · refine (upper_iff X _ τ).2 ?_
    rw [mat_rmul']
    exact ((upper_iff X b τ).1 (mem_bor_iff'.1 hb τ).2).mul ((upper_iff X b' τ).1 (mem_bor_iff'.1 hb' τ).2)

def invF (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem invF_mem {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : invF X b ∈ Bor X.Ψ r := by
  rw [mem_bor_iff']
  intro τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (mem_bor_iff'.1 hb τ).1
  have e : mat (invF X b) τ = (mat b τ)⁻¹ := rfl
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
  · refine (upper_iff X _ τ).2 ?_
    rw [e]
    haveI := Matrix.invertibleOfIsUnitDet _ hu
    exact Matrix.blockTriangular_inv_of_blockTriangular ((upper_iff X b τ).1 (mem_bor_iff'.1 hb τ).2)

theorem rmul_invF {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : rmul b (invF X b) = oneF X := by
  funext τ
  show mat b τ * (mat b τ)⁻¹ = (1 : Matrix (Fin r) (Fin r) ℂ)
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (mem_bor_iff'.1 hb τ).1)

theorem diag_mul {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    rmul b b' τ i i = b τ i i * b' τ i i := by
  show (mat b τ * mat b' τ) i i = b τ i i * b' τ i i
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rfl
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [show mat b τ i k = 0 from (mem_bor_iff'.1 hb τ).2 i k h, zero_mul]
    · rw [show mat b' τ k i = 0 from (mem_bor_iff'.1 hb' τ).2 k i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem bchar_mul (la : Wt X.Ψ r) {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    bchar la (rmul b b') = bchar la b * bchar la b' := by
  unfold bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [diag_mul X hb hb' τ i, mul_zpow]

theorem bchar_oneF (la : Wt X.Ψ r) : bchar la (oneF X) = 1 := by
  simp [bchar, oneF]

variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0)

def cell : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ D.Δ x ≠ 0}

theorem cell_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hΔ : D.Δ x ≠ 0) (hb : b ∈ Bor X.Ψ r) :
    D.Δ (rmul x b) ≠ 0 ∧ D.zOf (rmul x b) = D.zOf x ∧ D.bOf (rmul x b) = rmul (D.bOf x) b := by
  obtain ⟨hz, hbx, hxe⟩ := D.split x hx hΔ
  have e : rmul x b = rmul (cpt X x0 (D.zOf x)) (rmul (D.bOf x) b) := by
    rw [← rmul_assoc X, ← hxe]
  obtain ⟨h1, h2, h3⟩ := D.uniq (D.zOf x) hz (rmul (D.bOf x) b) (mul_mem X hbx hb)
  rw [e]
  exact ⟨h1, h2, h3⟩

theorem cell_of_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (hΔ : D.Δ (rmul x b) ≠ 0) : D.Δ x ≠ 0 := by
  have hxb : rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom (X := X) hx hb
  have h := (cell_rmul D hxb hΔ (invF_mem X hb)).1
  rwa [rmul_assoc X, rmul_invF X hb, rmul_oneF X] at h

theorem cpt_cell {z : V (nd X)} (hz : z ∈ OmF X x0) :
    D.Δ (cpt X x0 z) ≠ 0 ∧ D.zOf (cpt X x0 z) = z ∧ D.bOf (cpt X x0 z) = oneF X := by
  have h := D.uniq z hz (oneF X) (oneF_mem X)
  rwa [rmul_oneF X] at h

open Classical in

def P0 (la : Wt X.Ψ r) (F : V (nd X) → ℂ) (x : Frame X.Ψ r) : ℂ :=
  if x ∈ X.dom ∧ D.Δ x ≠ 0 then bchar la (D.bOf x) * F (D.zOf x) else 0

theorem poincareLift_on_chart (la : Wt X.Ψ r) (F : V (nd X) → ℂ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    P0 D la F (cpt X x0 z) = F z := by
  obtain ⟨h1, h2, h3⟩ := cpt_cell D hz
  have hd : cpt X x0 z ∈ X.dom := hz
  unfold P0
  rw [if_pos ⟨hd, h1⟩, h2, h3, bchar_oneF X, one_mul]

theorem poincareLift_borel_equivariant (la : Wt X.Ψ r) (F : V (nd X) → ℂ) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) : P0 D la F (rmul x b) = bchar la b * P0 D la F x := by
  have hxb : rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom (X := X) hx hb
  unfold P0
  by_cases hΔ : D.Δ x = 0
  · have hΔ' : D.Δ (rmul x b) = 0 := by
      by_contra h
      exact cell_of_rmul D hx hb h hΔ
    rw [if_neg (fun h => h.2 hΔ'), if_neg (fun h => h.2 hΔ), mul_zero]
  · obtain ⟨h1, h2, h3⟩ := cell_rmul D hx hΔ hb
    obtain ⟨-, hbx, -⟩ := D.split x hx hΔ
    rw [if_pos ⟨hxb, h1⟩, if_pos ⟨hx, hΔ⟩, h2, h3, bchar_mul X la hbx hb]
    ring

private lemma continuous_dmin' {Ψ : Finset (E →+* ℂ)} (G : Matrix (Fin r) (Fin r) E) (τ : Ψ) (i : Fin (r + 1)) :
    Continuous (fun x : Frame Ψ r => dmin G x τ i) := by
  unfold dmin lminor
  apply Continuous.matrix_det
  apply Continuous.matrix_submatrix
  refine continuous_pi (fun a => continuous_pi (fun c => ?_))
  simp only [gram, Matrix.of_apply, hermC, col, mat]
  fun_prop

private lemma isOpen_dom_upper_bounds : IsOpen X.dom := by
  show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
    ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite (fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite (fun i => ?_)))
  · exact isOpen_ne_fun (by unfold mat; fun_prop) continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (continuous_dmin' X.Gm τ i)))

theorem isOpen_cell : IsOpen (cell D) := by
  show IsOpen (X.dom ∩ {x | D.Δ x ≠ 0})
  exact (isOpen_dom_upper_bounds (X := X)).inter (isOpen_ne_fun D.hΔ.continuous continuous_const)

theorem diffOn_prod {ι : Type*} (u : Finset ι) {g : ι → Frame X.Ψ r → ℂ} {s : Set (Frame X.Ψ r)}
    (h : ∀ i ∈ u, DifferentiableOn ℂ (g i) s) : DifferentiableOn ℂ (fun x => ∏ i ∈ u, g i x) s := by
  classical
  revert h
  refine Finset.induction_on u (fun _ => ?_) (fun a u ha ih h => ?_)
  · simp only [Finset.prod_empty]
    exact differentiableOn_const 1
  · simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).mul (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem poincareLift_differentiableOn (la : Wt X.Ψ r) (F : V (nd X) → ℂ) (hF : DifferentiableOn ℂ F (OmF X x0)) :
    DifferentiableOn ℂ (P0 D la F) (cell D) := by
  have hsub : ∀ x ∈ cell D, D.zOf x ∈ OmF X x0 ∧ D.bOf x ∈ Bor X.Ψ r := by
    intro x hx
    have hx' : x ∈ X.dom ∧ D.Δ x ≠ 0 := hx
    have h := D.split x hx'.1 hx'.2
    exact ⟨h.1, h.2.1⟩
  have hbc : DifferentiableOn ℂ (fun x => bchar la (D.bOf x)) (cell D) := by
    unfold bchar
    refine diffOn_prod (g := fun τ x => ∏ i, D.bOf x τ i i ^ la τ i) Finset.univ (fun τ _ => ?_)
    refine diffOn_prod (g := fun i x => D.bOf x τ i i ^ la τ i) Finset.univ (fun i _ => ?_)
    refine DifferentiableOn.zpow ?_ (Or.inl (fun x hx => FrameDegreeData.bdiag_ne (X := X) (hsub x hx).2 τ i))
    have h1 := (differentiableOn_pi.1 D.hb) τ
    have h2 := (differentiableOn_pi.1 h1) i
    exact (differentiableOn_pi.1 h2) i
  have hFz : DifferentiableOn ℂ (fun x => F (D.zOf x)) (cell D) :=
    hF.comp D.hz (fun x hx => (hsub x hx).1)
  refine (hbc.mul hFz).congr (fun x hx => ?_)
  have hx' : x ∈ X.dom ∧ D.Δ x ≠ 0 := hx
  unfold P0
  rw [if_pos hx']
  rfl

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
