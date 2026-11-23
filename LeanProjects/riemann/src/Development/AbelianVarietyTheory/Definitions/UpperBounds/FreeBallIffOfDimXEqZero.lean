import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneLeMinorOfIsOrth

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Up

noncomputable def rhX {r : ℕ} (X : Data E r) (x0 x : Frame X.Ψ r) : ℝ :=
  -Real.log (∏ τ : X.Ψ, ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ /
    ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2)

def dimX {r : ℕ} (X : Data E r) : ℕ := X.Ψ.card * (X.p0 * (r - X.p0))

def FreeBall {r : ℕ} (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r) (ρ0 : ℝ) : Prop :=
  X.Γ ≤ G ∧ (∀ γ ∈ G, IsUStab X.Gm X.Λ γ) ∧
    ∀ γ ∈ G, γ ≠ 1 → ∀ x ∈ X.dom, rhX X x0 x < ρ0 → ρ0 ≤ rhX X x0 (lact γ x)

def IsPole {r : ℕ} (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r) (κ ε C δ : ℝ)
    (ψ : Frame X.Ψ r → ℝ) : Prop :=
  (∀ γ ∈ G, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (lact γ (rmul x b)) = ψ x) ∧ (∀ x ∈ X.dom, ψ x ≤ 0) ∧
  (∀ x1, IsOrth X x1 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x1 z)) (OmF X x1) ∧
    ∀ z ∈ OmF X x1, ∀ ξ : Fin (nd X) → ℂ, -(κ * leviRh X x1 z ξ) ≤ leviO X x1 ψ z ξ) ∧
  (∀ x ∈ X.dom, rhX X x0 x ≤ ε → ψ x ≤ dimX X * Real.log (rhX X x0 x + δ) + C) ∧
  ∀ x ∈ X.dom, ε / 2 ≤ rhX X x0 x → rhX X x0 x ≤ ε → -C ≤ ψ x

def PoleEx : Prop := ∀ (r : ℕ) (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r) (ρ0 θ : ℝ),
  IsOrth X x0 → 0 < ρ0 → 1 < θ → FreeBall X G x0 ρ0 →
  ∃ ε C : ℝ, 0 < ε ∧ ε < ρ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ ψ, IsPole X G x0 (dimX X * θ / ρ0) ε C δ ψ

def BlockConst {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∀ τ, ∀ i j : Fin r, ((i : ℕ) < X.p0 ↔ (j : ℕ) < X.p0) → la τ i = la τ j

def PoleSolve : Prop := ∀ (r : ℕ) (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r)
  (κ ε C bb m : ℝ), IsOrth X x0 → BlockConst X la → 0 < ε → 0 ≤ bb → bb + κ < m →
  (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ) →
  ∃ (χ : ℝ → ℝ) (M : ℝ≥0∞), Continuous χ ∧ (∀ u ≤ ε / 2, χ u = 1) ∧ (∀ u, ε ≤ u → χ u = 0) ∧ (∀ u, |χ u| ≤ 1) ∧ M < ⊤ ∧
    ∀ δ ψ, IsPole X G x0 κ ε C δ ψ → ∃ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) ∧
      ∫⁻ z, ENNReal.ofReal (‖(χ (rhF X x0 z) : ℂ) - F z‖ ^ 2 *
        Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z) ∂muF X x0 ≤ M

def PolePoint : Prop := ∀ (r : ℕ) (X : Data E r) (ρ c : ℝ), 1 ≤ dimX X → 0 < ρ → 0 < c →
  ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ x1, IsOrth X x1 → ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ u : V (nd X) → ℂ,
    DifferentiableOn ℂ u (Metric.ball 0 ρ ∩ OmF X x1) →
    ENNReal.ofReal (‖u 0‖ ^ 2) ≤ ENNReal.ofReal c *
      ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal (‖u z‖ ^ 2 * (rhF X x1 z + δ) ^ (-(dimX X : ℝ))) ∂muF X x1

def RhTr : Prop := ∀ (r : ℕ) (X : Data E r) (x1 x2 : Frame X.Ψ r), IsOrth X x1 → IsOrth X x2 →
  ContDiffOn ℝ ∞ (fun z => rhX X x2 (cpt X x1 z)) (OmF X x1) ∧ ∀ z ∈ OmF X x1, 0 ≤ rhX X x2 (cpt X x1 z) ∧
    ∀ ξ : Fin (nd X) → ℂ, leviO X x1 (rhX X x2) z ξ = leviRh X x1 z ξ ∧
      Complex.normSq (∑ j, wd (nd X) j (fun w => ((rhX X x2 (cpt X x1 w) : ℝ) : ℂ)) z * ξ j) ≤
        rhX X x2 (cpt X x1 z) * leviRh X x1 z ξ

def BallEx : Prop := ∀ (r : ℕ) (X : DataX E r) (G : Subgroup (GL (Fin r) E)) (g : ℕ), 0 < r → 3 * r < g →
  X.Γ ≤ G → (∀ γ ∈ G, IsUStab X.Gm X.Λ γ) →
  (∀ γ ∈ G, ∀ x ∈ X.L', Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x ∈ X.L') →
  (∀ γ ∈ G, ∃ z : 𝓞 E, (γ : Matrix (Fin r) (Fin r) E).trace - r = (g : E) * z) →
  ∃ x0, IsOrth X.toData x0 ∧ FreeBall X.toData G x0 (1 / (49 * (r : ℝ) ^ 2))

def OrbitInterp : Prop := ∀ (r : ℕ) (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r)
  (ρ0 bb m : ℝ), PropDisc X → IsOrth X x0 → 1 ≤ dimX X → 0 < ρ0 → FreeBall X G x0 ρ0 → BlockConst X la →
  4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → bb + dimX X / ρ0 < m →
  (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ) →
  (∀ P, X.IsBddSec la P → P ∈ X.SS la) →
  ∃ u0 ∈ X.SS la, u0 x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → u0 (lact γ x0) = 0

section Potential

variable {r : ℕ} {X : Data E r} {x0 x : Frame X.Ψ r}

theorem exp_neg_rhX (h0 : IsOrth X x0) (hx : x ∈ X.dom) :
    Real.exp (-rhX X x0 x) = ∏ τ : X.Ψ, ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ /
      ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 := by
  unfold rhX
  rw [neg_neg, Real.exp_log (Finset.prod_pos fun τ _ => (FramePotential.factor_mem X h0 hx τ).1)]

theorem lminor_inv_mul_ne_zero (h0 : IsOrth X x0) (hx : x ∈ X.dom) (τ : X.Ψ) :
    lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ ≠ 0 := by
  intro h
  have := (FramePotential.factor_mem X h0 hx τ).1
  rw [h] at this
  simp at this

theorem rhX_eq_sum_log (h0 : IsOrth X x0) (hx : x ∈ X.dom) :
    rhX X x0 x = ∑ τ : X.Ψ, -Real.log (‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ /
      ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2) := by
  unfold rhX
  rw [Real.log_prod (fun τ _ => (FramePotential.factor_mem X h0 hx τ).1.ne'), Finset.sum_neg_distrib]

theorem rhX_eq_sum (h0 : IsOrth X x0) (hx : x ∈ X.dom) :
    rhX X x0 x = -∑ τ : X.Ψ, Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ +
      ∑ τ : X.Ψ, Real.log (‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2) := by
  rw [rhX_eq_sum_log h0 hx, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_div (norm_ne_zero_iff.2 (IW.dmin_ne_zero X hx τ _))
    (pow_ne_zero _ (norm_ne_zero_iff.2 (lminor_inv_mul_ne_zero h0 hx τ)))]
  ring

theorem rhX_nonneg (h0 : IsOrth X x0) (hx : x ∈ X.dom) : 0 ≤ rhX X x0 x := by
  rw [rhX_eq_sum_log h0 hx]
  exact Finset.sum_nonneg fun τ _ => neg_nonneg.2 (Real.log_nonpos
    (FramePotential.factor_mem X h0 hx τ).1.le (FramePotential.factor_mem X h0 hx τ).2)

theorem neg_log_factor_le_rhX (h0 : IsOrth X x0) (hx : x ∈ X.dom) (τ : X.Ψ) :
    -Real.log (‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ /
      ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2) ≤ rhX X x0 x := by
  rw [rhX_eq_sum_log h0 hx]
  exact Finset.single_le_sum (f := fun τ : X.Ψ =>
    -Real.log (‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ /
      ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2))
    (fun τ _ => neg_nonneg.2 (Real.log_nonpos
      (FramePotential.factor_mem X h0 hx τ).1.le (FramePotential.factor_mem X h0 hx τ).2))
    (Finset.mem_univ τ)

theorem rhX_rmul (x0 x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rhX X x0 (rmul x b) = rhX X x0 x := by
  unfold rhX
  rw [Finset.prod_congr rfl fun τ _ => FramePotential.factor_rmul X x0 x hb τ _]

theorem rhX_cpt (h0 : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    rhX X x0 (cpt X x0 z) = rhF X x0 z := by
  unfold rhX
  rw [(FramePotential.frame_potential_basic r X x0 h0).2.2.2 z hz, Real.log_exp, neg_neg]

theorem rhX_self (h0 : IsOrth X x0) : rhX X x0 x0 = 0 := by
  unfold rhX
  rw [Finset.prod_eq_one, Real.log_one, neg_zero]
  intro τ _
  rw [FramePotential.norm_dmin_of_isOrth X h0,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)), LUPf.lminor_one]
  simp

theorem measurable_rhX (h0 : IsOrth X x0) : Measurable (rhX X x0) :=
  (Real.measurable_log.comp (FramePotential.frame_potential_basic r X x0 h0).1).neg

theorem continuousOn_rhX (h0 : IsOrth X x0) : ContinuousOn (rhX X x0) X.dom := by
  refine ContinuousOn.neg (ContinuousOn.log (continuousOn_finset_prod _ fun τ _ => ?_)
    fun x hx => (Finset.prod_pos fun τ _ => (FramePotential.factor_mem X h0 hx τ).1).ne')
  refine ContinuousOn.div (ExtFPf.cont_dmin X τ _).norm.continuousOn ?_
    fun x hx => pow_ne_zero _ (norm_ne_zero_iff.2 (lminor_inv_mul_ne_zero h0 hx τ))
  have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
  exact ((((continuous_const.matrix_mul hm).matrix_submatrix _ _).matrix_det).norm.pow 2).continuousOn

theorem isOrth_lact_of_isUStab {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) (h0 : IsOrth X x0) :
    IsOrth X (lact γ x0) := fun τ => by rw [MajInv.gram_lact X hγ, h0 τ]

theorem rhX_lact_lact {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) (x0 x : Frame X.Ψ r) :
    rhX X (lact γ x0) (lact γ x) = rhX X x0 x := by
  unfold rhX
  congr 2
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det := by
    rw [show ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det =
      τ.1 (γ : Matrix (Fin r) (Fin r) E).det by rw [RingHom.map_det]; rfl]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).map τ.1
  have e : ∀ y : Frame X.Ψ r, mat (lact γ y) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ :=
    fun _ => rfl
  unfold dmin
  rw [MajInv.gram_lact X hγ, e, e, Matrix.mul_inv_rev, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem rhX_lact {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) (x0 x : Frame X.Ψ r) :
    rhX X x0 (lact γ x) = rhX X (lact γ⁻¹ x0) x := by
  rw [← rhX_lact_lact hγ (lact γ⁻¹ x0) x, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]

theorem leviRh_nonneg (h0 : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ leviRh X x0 z ξ :=
  OntoB.levi_rh_nonneg RhGradFStatement_holds h0 hz ξ

end Potential

section Dimension

variable {r : ℕ} (X : Data E r)

theorem dimX_eq_zero_iff : dimX X = 0 ↔ X.p0 = 0 ∨ X.p0 = r := by
  have hΨ : X.Ψ.card ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine Finset.card_ne_zero.2 ?_
    by_cases h : τ ∈ X.Ψ
    · exact ⟨τ, h⟩
    · exact ⟨_, not_not.1 fun h' => h ((X.cmType τ).2 h')⟩
  have := X.p0_le
  unfold dimX
  simp only [Nat.mul_eq_zero, hΨ, false_or]
  omega

theorem one_le_dimX_iff : 1 ≤ dimX X ↔ 0 < X.p0 ∧ X.p0 < r := by
  have h := dimX_eq_zero_iff X
  have := X.p0_le
  omega

def mixedEntEquiv :
    {e : Ent X // (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ)} ≃ X.Ψ × (Fin X.p0 × Fin (r - X.p0)) where
  toFun e := (e.1.1, ⟨e.1.2.1.2, e.2.1⟩, ⟨e.1.2.1.1 - X.p0, by have := e.1.2.1.1.isLt; have := e.2.2; omega⟩)
  invFun t := ⟨(t.1, ⟨(⟨X.p0 + t.2.2, by have := t.2.2.isLt; omega⟩,
      ⟨t.2.1, lt_of_lt_of_le t.2.1.isLt X.p0_le⟩), by
        have := t.2.1.isLt
        simp only [Fin.lt_def]; omega⟩), t.2.1.isLt, Nat.le_add_right _ _⟩
  left_inv := by
    rintro ⟨⟨τ, ⟨a, b⟩, hab⟩, h1, h2⟩
    simp only at h1 h2
    simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and, Fin.eta, and_true]
    exact Fin.ext (by simp only; omega)
  right_inv := by
    rintro ⟨τ, a, b⟩
    simp

theorem card_mixedEnt :
    Fintype.card {e : Ent X // (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ)} = dimX X := by
  rw [Fintype.card_congr (mixedEntEquiv X)]
  simp [dimX]

end Dimension

section Ball

variable {r : ℕ} {X : Data E r} {G G' : Subgroup (GL (Fin r) E)} {x0 x : Frame X.Ψ r} {ρ0 ρ1 : ℝ}

theorem FreeBall.le (h : FreeBall X G x0 ρ0) : X.Γ ≤ G := h.1

theorem FreeBall.isUStab (h : FreeBall X G x0 ρ0) {γ : GL (Fin r) E} (hγ : γ ∈ G) :
    IsUStab X.Gm X.Λ γ := h.2.1 γ hγ

theorem FreeBall.eq_one (h : FreeBall X G x0 ρ0) {γ : GL (Fin r) E} (hγ : γ ∈ G) (hx : x ∈ X.dom)
    (h1 : rhX X x0 x < ρ0) (h2 : rhX X x0 (lact γ x) < ρ0) : γ = 1 := by
  by_contra hne
  exact absurd (h.2.2 γ hγ hne x hx h1) (not_le.2 h2)

theorem FreeBall.unique (h : FreeBall X G x0 ρ0) {γ γ' : GL (Fin r) E} (hγ : γ ∈ G) (hγ' : γ' ∈ G)
    (hx : x ∈ X.dom) (h1 : rhX X x0 (lact γ x) < ρ0) (h2 : rhX X x0 (lact γ' x) < ρ0) : γ = γ' := by
  have := h.eq_one (G.mul_mem hγ' (G.inv_mem hγ)) (MajInv.lact_mem_dom X (h.isUStab hγ) hx) h1
    (by rwa [FundSetPf.lact_mul, FundSetPf.lact_inv])
  exact (mul_inv_eq_one.1 this).symm

theorem FreeBall.mono (h : FreeBall X G x0 ρ0) (hρ : ρ1 ≤ ρ0) : FreeBall X G x0 ρ1 :=
  ⟨h.1, h.2.1, fun γ hγ hne x hx hlt => hρ.trans (h.2.2 γ hγ hne x hx (hlt.trans_le hρ))⟩

theorem FreeBall.of_le (h : FreeBall X G x0 ρ0) (h1 : X.Γ ≤ G') (h2 : G' ≤ G) : FreeBall X G' x0 ρ0 :=
  ⟨h1, fun γ hγ => h.2.1 γ (h2 hγ), fun γ hγ => h.2.2 γ (h2 hγ)⟩

theorem FreeBall.eq_of_lact_eq (h : FreeBall X G x0 ρ0) (h0 : IsOrth X x0) (hρ : 0 < ρ0)
    {γ γ' : GL (Fin r) E} (hγ : γ ∈ G) (hγ' : γ' ∈ G) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (e : lact γ x0 = lact γ' (rmul x0 b)) : γ = γ' := by
  have h1 : lact (γ'⁻¹ * γ) x0 = rmul x0 b := by rw [FundSetPf.lact_mul, e, FundSetPf.lact_inv]
  have := h.eq_one (G.mul_mem (G.inv_mem hγ') hγ) (IW.orth_mem_dom X x0 h0) (by rwa [rhX_self h0])
    (by rwa [h1, rhX_rmul x0 x0 hb, rhX_self h0])
  exact (inv_mul_eq_one.1 this).symm

theorem FreeBall.lact (h : FreeBall X G x0 ρ0) {g : GL (Fin r) E} (hg : g ∈ G) :
    FreeBall X G (lact g x0) ρ0 := by
  refine ⟨h.1, h.2.1, fun γ hγ hne x hx hlt => ?_⟩
  have hg' := h.isUStab (G.inv_mem hg)
  rw [← rhX_lact_lact hg', FundSetPf.lact_inv] at hlt ⊢
  have hc : g⁻¹ * γ * g ≠ 1 := fun hc => hne (by
    have : γ = g * (g⁻¹ * γ * g) * g⁻¹ := by group
    rw [this, hc]; group)
  have := h.2.2 _ (G.mul_mem (G.mul_mem (G.inv_mem hg) hγ) hg) hc _ (MajInv.lact_mem_dom X hg' hx) hlt
  rwa [← FundSetPf.lact_mul, mul_inv_cancel_right, FundSetPf.lact_mul] at this

end Ball

section Pole

variable {r : ℕ} {X : Data E r} {G G' : Subgroup (GL (Fin r) E)} {x0 x : Frame X.Ψ r}
  {κ κ' ε C C' δ : ℝ} {ψ : Frame X.Ψ r → ℝ}

theorem IsPole.lact (h : IsPole X G x0 κ ε C δ ψ) {γ : GL (Fin r) E} (hγ : γ ∈ G) (hx : x ∈ X.dom) :
    ψ (lact γ x) = ψ x := by
  have := h.1 γ hγ x hx _ (ExtFPf.oneF_mem X)
  rwa [ExtFPf.rmul_oneF] at this

theorem IsPole.rmul (h : IsPole X G x0 κ ε C δ ψ) (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : ψ (rmul x b) = ψ x := by
  have := h.1 1 G.one_mem x hx b hb
  rwa [FundSetPf.lact_one] at this

theorem IsPole.isInvFn (h : IsPole X G x0 κ ε C δ ψ) (hG : X.Γ ≤ G) : IsInvFn X ψ :=
  fun γ hγ => h.1 γ (hG hγ)

theorem IsPole.mono (h : IsPole X G x0 κ ε C δ ψ) (hG : G' ≤ G) (hκ : κ ≤ κ') (hC : C ≤ C') :
    IsPole X G' x0 κ' ε C' δ ψ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun γ hγ => h1 γ (hG hγ), h2, fun x1 hx1 => ⟨(h3 x1 hx1).1, fun z hz ξ => ?_⟩,
    fun x hx hle => (h4 x hx hle).trans (by linarith),
    fun x hx ha hb => le_trans (by linarith) (h5 x hx ha hb)⟩
  exact le_trans (neg_le_neg (mul_le_mul_of_nonneg_right hκ (leviRh_nonneg hx1 hz ξ)))
    ((h3 x1 hx1).2 z hz ξ)

theorem IsPole.le_log_orbit (h : IsPole X G x0 κ ε C δ ψ) (hG : ∀ γ ∈ G, IsUStab X.Gm X.Λ γ)
    {γ : GL (Fin r) E} (hγ : γ ∈ G) (hx : x ∈ X.dom) (hle : rhX X (ReciprocityTheory.ChartRestriction.G.FD.lact γ x0) x ≤ ε) :
    ψ x ≤ dimX X * Real.log (rhX X (ReciprocityTheory.ChartRestriction.G.FD.lact γ x0) x + δ) + C := by
  have hγ' := hG _ (G.inv_mem hγ)
  rw [← rhX_lact_lact hγ', FundSetPf.lact_inv] at hle ⊢
  rw [← h.lact (G.inv_mem hγ) hx]
  exact h.2.2.2.1 _ (MajInv.lact_mem_dom X hγ' hx) hle

theorem IsPole.centre (h : IsPole X G x0 κ ε C δ ψ) (h0 : IsOrth X x0) (hε : 0 ≤ ε) :
    ψ x0 ≤ dimX X * Real.log δ + C := by
  have := h.2.2.2.1 x0 (IW.orth_mem_dom X x0 h0) (by rwa [rhX_self h0])
  rwa [rhX_self h0, zero_add] at this

theorem isPole_zero (h0 : IsOrth X x0) (hκ : 0 ≤ κ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hC' : -(dimX X * Real.log δ) ≤ C) : IsPole X G x0 κ ε C δ fun _ => 0 := by
  refine ⟨fun _ _ _ _ _ _ => rfl, fun _ _ => le_rfl, fun x1 hx1 => ⟨contDiffOn_const, fun z hz ξ => ?_⟩,
    fun x hx _ => ?_, fun _ _ _ _ => by linarith⟩
  · have e : leviO X x1 (fun _ => 0) z ξ = 0 := by
      have e1 : ∀ k, wdb (nd X) k (fun _ => (0 : ℂ)) = fun _ => 0 := fun k => by
        funext y; simp [wdb]
      simp [leviO, leviM, leviV, e1, wd]
    rw [e]
    exact neg_nonpos.2 (mul_nonneg hκ (leviRh_nonneg hx1 hz ξ))
  · have h1 : Real.log δ ≤ Real.log (rhX X x0 x + δ) :=
      Real.log_le_log hδ (by linarith [rhX_nonneg h0 hx])
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) (dimX X))
    linarith

end Pole

section Block

variable {r : ℕ} {X : Data E r} {la la' : Wt X.Ψ r}

theorem blockConst_ite (a a' : X.Ψ → ℤ) :
    BlockConst X fun τ i => if (i : ℕ) < X.p0 then a τ else a' τ :=
  fun _ _ _ h => if_congr h rfl rfl

theorem blockConst_iff : BlockConst X la ↔
    ∃ a a' : X.Ψ → ℤ, la = fun τ (i : Fin r) => if (i : ℕ) < X.p0 then a τ else a' τ := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  · refine ⟨fun τ => if hi : ∃ i : Fin r, (i : ℕ) < X.p0 then la τ hi.choose else 0,
      fun τ => if hi : ∃ i : Fin r, ¬ (i : ℕ) < X.p0 then la τ hi.choose else 0, ?_⟩
    funext τ i
    beta_reduce
    by_cases hi : (i : ℕ) < X.p0
    · have hex : ∃ i : Fin r, (i : ℕ) < X.p0 := ⟨i, hi⟩
      rw [if_pos hi, dif_pos hex]
      exact h τ _ _ (iff_of_true hi hex.choose_spec)
    · have hex : ∃ i : Fin r, ¬ (i : ℕ) < X.p0 := ⟨i, hi⟩
      rw [if_neg hi, dif_pos hex]
      exact h τ _ _ (iff_of_false hi hex.choose_spec)
  · rintro ⟨a, a', rfl⟩
    exact blockConst_ite a a'

theorem BlockConst.add (h : BlockConst X la) (h' : BlockConst X la') : BlockConst X (la + la') :=
  fun τ i j hij => by simp only [Pi.add_apply, h τ i j hij, h' τ i j hij]

theorem BlockConst.zsmul (h : BlockConst X la) (k : ℤ) : BlockConst X (k • la) :=
  fun τ i j hij => by simp only [Pi.smul_apply, h τ i j hij]

theorem BlockConst.nsmul (h : BlockConst X la) (k : ℕ) : BlockConst X (k • la) :=
  fun τ i j hij => by simp only [Pi.smul_apply, h τ i j hij]

end Block

section Checks

example (X : Data E 2) (hp : X.p0 = 1) : dimX X = X.Ψ.card := by simp [dimX, hp]

example (X : Data E 5) (hp : X.p0 = 2) : dimX X = 6 * X.Ψ.card := by simp [dimX, hp, mul_comm]

example (x0 : Frame (inhab (E := E)).Ψ 1) (ρ0 : ℝ) : FreeBall (inhab (E := E)) ⊥ x0 ρ0 :=
  ⟨le_rfl, fun γ hγ => (inhab (E := E)).Γ_stab γ hγ, fun _ hγ hne => absurd (Subgroup.mem_bot.1 hγ) hne⟩

example {r : ℕ} (hr : 0 < r) (X : Data E r) (G : Subgroup (GL (Fin r) E)) (hG : -1 ∈ G) {x0 : Frame X.Ψ r}
    (h0 : IsOrth X x0) {ρ0 : ℝ} (hρ : 0 < ρ0) : ¬ FreeBall X G x0 ρ0 := by
  intro h
  have hb : (fun _ => (-1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := fun τ =>
    ⟨by
      show (-1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
      rw [Matrix.det_neg]; simp,
    fun a c hac => by
      show -(1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
      rw [Matrix.one_apply_ne hac.ne', neg_zero]⟩
  have e := h.eq_of_lact_eq h0 hρ hG G.one_mem hb (by
    rw [FundSetPf.lact_one]
    funext τ
    show (((-1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ : Matrix (Fin r) (Fin r) ℂ) =
      mat x0 τ * (-1 : Matrix (Fin r) (Fin r) ℂ)
    rw [Units.val_neg, Units.val_one, ← RingHom.mapMatrix_apply, map_neg, map_one]
    simp)
  have e2 := congrArg (fun γ : GL (Fin r) E => (γ : Matrix (Fin r) (Fin r) E) ⟨0, hr⟩ ⟨0, hr⟩) e
  simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at e2
  norm_num at e2

example {r : ℕ} (X : Data E r) (hd : dimX X = 0) (G : Subgroup (GL (Fin r) E)) {x0 : Frame X.Ψ r}
    (h0 : IsOrth X x0) {ρ0 : ℝ} (hρ : 0 < ρ0) (θ : ℝ) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < ρ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ ψ, IsPole X G x0 (dimX X * θ / ρ0) ε C δ ψ :=
  ⟨ρ0 / 2, 0, by linarith, by linarith, fun _ hδ _ =>
    ⟨_, isPole_zero h0 (by simp [hd]) hδ le_rfl (by simp [hd])⟩⟩

example {r : ℕ} (X : Data E r) (hd : 1 ≤ dimX X) (G : Subgroup (GL (Fin r) E)) {x0 : Frame X.Ψ r}
    (h0 : IsOrth X x0) (κ C : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ¬ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → IsPole X G x0 κ ε C δ fun _ => 0 := by
  intro h
  have h1 : (1 : ℝ) ≤ dimX X := by exact_mod_cast hd
  have h2 := (h (Real.exp (-(|C| + 1))) (Real.exp_pos _)
    (Real.exp_le_one_iff.2 (by linarith [abs_nonneg C]))).centre h0 hε
  rw [Real.log_exp] at h2
  nlinarith [abs_nonneg C, le_abs_self C]

example (X : Data E 2) (hp : X.p0 = 2) (τ : X.Ψ) : ¬ BlockConst X (kapW X) := by
  intro h
  have := h τ 0 1 (by simp [hp])
  simp [kapW] at this

example (D θ r : ℝ) : D * θ / (1 / (49 * r ^ 2)) = D * θ * (49 * r ^ 2) := by
  rw [one_div, div_inv_eq_mul]

end Checks

end GlobalTheory.Up
