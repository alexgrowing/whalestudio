import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnitaryRepUnimodularOfFiniteVolume
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjStarProj

noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows Formalism.L2.SG.RowsDef

def GfUnimod : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure], μf.IsMulRightInvariant

section Local

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def repHom {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : IsURepOn (UJset ε) σ) :
    Formalism.REAL.UJ ε →* (H →L[ℂ] H) where
  toFun g := σ (umat g)
  map_one' := (isURep_of_on hU).1
  map_mul' a b := ((isURep_of_on hU).2.1 a b).trans (ContinuousLinearMap.mul_def _ _).symm

theorem phLoc_conv {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : IsURepOn (UJset ε) σ) (w : H) (d : ℝ)
    (hF : IsFdeg (Formalism.REAL.muG ε) σ d) (hw : ‖w‖ = 1) (y : Formalism.REAL.UJ ε) :
    ∫ g, phLoc (ε := ε) σ w d g * phLoc (ε := ε) σ w d (g⁻¹ * y) ∂(Formalism.REAL.muG ε) = phLoc (ε := ε) σ w d y := by
  have hd : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hF.1.ne'
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]
    simp
  have hpt : ∀ g : Formalism.REAL.UJ ε, phLoc (ε := ε) σ w d g * phLoc (ε := ε) σ w d (g⁻¹ * y) =
      ((d : ℂ) * d) * (coefOn (ε := ε) σ w (σ (umat y) w) g * star (coefOn (ε := ε) σ w w g)) := by
    intro g
    have hsplit : σ (umat (g⁻¹ * y)) w = σ (umat g⁻¹) (σ (umat y) w) := by
      rw [show umat (g⁻¹ * y) = umat g⁻¹ * umat y from rfl, hU.1.2 _ (g⁻¹).2 _ y.2,
        ContinuousLinearMap.comp_apply]
    have hmul : umat g * umat g⁻¹ = 1 := by simp [umat]
    have key : ∀ x, σ (umat g) (σ (umat g⁻¹) x) = x := by
      intro x
      rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ g.2 _ (g⁻¹).2, hmul, hU.1.1,
        ContinuousLinearMap.one_apply]
    let L : H →ₗᵢ[ℂ] H := ⟨(σ (umat g)).toLinearMap, hU.2.1 _ g.2⟩
    have hin : ⟪w, σ (umat (g⁻¹ * y)) w⟫_ℂ = ⟪σ (umat g) w, σ (umat y) w⟫_ℂ := by
      rw [hsplit]
      have h1 : ⟪L w, L (σ (umat g⁻¹) (σ (umat y) w))⟫_ℂ = ⟪w, σ (umat g⁻¹) (σ (umat y) w)⟫_ℂ :=
        L.inner_map_map _ _
      have h2 : L (σ (umat g⁻¹) (σ (umat y) w)) = σ (umat y) w := key _
      rw [h2] at h1
      exact h1.symm
    show (d : ℂ) * star ⟪w, σ (umat g) w⟫_ℂ * ((d : ℂ) * star ⟪w, σ (umat (g⁻¹ * y)) w⟫_ℂ) =
      ((d : ℂ) * d) * (⟪σ (umat y) w, σ (umat g) w⟫_ℂ * star ⟪w, σ (umat g) w⟫_ℂ)
    rw [hin, ← inner_conj_symm (σ (umat y) w) (σ (umat g) w), starRingEnd_apply]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    (hF.2 w (σ (umat y) w) w w).2, hww, one_mul]
  show (d : ℂ) * d * (⟪σ (umat y) w, w⟫_ℂ / d) = (d : ℂ) * star ⟪w, σ (umat y) w⟫_ℂ
  rw [← inner_conj_symm (σ (umat y) w) w, starRingEnd_apply]
  first
  | (field_simp; done)
  | (field_simp; ring)

end Local

section Two

variable {G1 G2 : Type} [Group G1] [Group G2] [MeasurableSpace G1] [MeasurableSpace G2]
  (μ1 : Measure G1) (μ2 : Measure G2) [SFinite μ1] [SFinite μ2]
  {Hp : Type} [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]

theorem prod_op_eq (R : G1 × G2 → (Hp →L[ℂ] Hp)) (hmul : ∀ g h, R (g * h) = R g ∘L R h)
    (hU : ∀ g x, ‖R g x‖ = ‖x‖)
    (hmeas : ∀ x y : Hp, AEStronglyMeasurable (fun g => ⟪x, R g y⟫_ℂ) (μ1.prod μ2))
    (φ1 : G1 → ℂ) (φ2 : G2 → ℂ) (hφ : Integrable (fun p : G1 × G2 => φ1 p.1 * φ2 p.2) (μ1.prod μ2))
    (P1 P2 : Hp →L[ℂ] Hp)
    (hP1 : ∀ x y : Hp, ⟪x, P1 y⟫_ℂ = ∫ g, φ1 g * ⟪x, R (g, 1) y⟫_ℂ ∂μ1)
    (hP2 : ∀ x y : Hp, ⟪x, P2 y⟫_ℂ = ∫ k, φ2 k * ⟪x, R (1, k) y⟫_ℂ ∂μ2) (x y : Hp) :
    ∫ p, (φ1 p.1 * φ2 p.2) * ⟪x, R p y⟫_ℂ ∂(μ1.prod μ2) = ⟪x, P1 (P2 y)⟫_ℂ ∧
      ∫ p, (φ1 p.1 * φ2 p.2) * ⟪x, R p y⟫_ℂ ∂(μ1.prod μ2) = ⟪x, P2 (P1 y)⟫_ℂ := by
  have hR1 : ∀ z, R 1 z = z := by
    intro z
    have h1 : R 1 (R 1 z) = R 1 z := by
      rw [← ContinuousLinearMap.comp_apply, ← hmul, one_mul]
    have h2 : ‖R 1 (R 1 z - z)‖ = ‖R 1 z - z‖ := hU 1 _
    rw [map_sub, h1, sub_self, norm_zero] at h2
    exact sub_eq_zero.1 (norm_eq_zero.1 h2.symm)
  have hinn : ∀ g a b, ⟪R g a, R g b⟫_ℂ = ⟪a, b⟫_ℂ := by
    intro g a b
    let L : Hp →ₗᵢ[ℂ] Hp := ⟨(R g).toLinearMap, hU g⟩
    exact L.inner_map_map a b
  have hadj : ∀ g a b, ⟪a, R g b⟫_ℂ = ⟪R g⁻¹ a, b⟫_ℂ := by
    intro g a b
    rw [← hinn g⁻¹ a (R g b), ← ContinuousLinearMap.comp_apply, ← hmul, inv_mul_cancel, hR1]
  have hbd : ∀ p, ‖⟪x, R p y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := fun p =>
    (norm_inner_le_norm _ _).trans (le_of_eq (by rw [hU]))
  have hint : Integrable (fun p : G1 × G2 => (φ1 p.1 * φ2 p.2) * ⟪x, R p y⟫_ℂ) (μ1.prod μ2) := by
    refine (hφ.const_mul ((‖x‖ * ‖y‖ : ℝ) : ℂ)).mono (hφ.aestronglyMeasurable.mul (hmeas x y))
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_norm]
    nlinarith [hbd p, norm_nonneg (φ1 p.1), norm_nonneg (φ2 p.2),
      mul_nonneg (norm_nonneg (φ1 p.1)) (norm_nonneg (φ2 p.2))]
  constructor
  · rw [integral_prod _ hint, hP1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show ∫ k, φ1 g * φ2 k * ⟪x, R (g, k) y⟫_ℂ ∂μ2 = φ1 g * ⟪x, R (g, 1) (P2 y)⟫_ℂ
    rw [hadj, hP2, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show φ1 g * φ2 k * ⟪x, R (g, k) y⟫_ℂ = φ1 g * (φ2 k * ⟪R (g, 1)⁻¹ x, R (1, k) y⟫_ℂ)
    rw [← hadj, ← ContinuousLinearMap.comp_apply, ← hmul]
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
    ring
  · rw [integral_prod_symm _ hint, hP2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show ∫ g, φ1 g * φ2 k * ⟪x, R (g, k) y⟫_ℂ ∂μ1 = φ2 k * ⟪x, R (1, k) (P1 y)⟫_ℂ
    rw [hadj, hP1, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show φ1 g * φ2 k * ⟪x, R (g, k) y⟫_ℂ = φ2 k * (φ1 g * ⟪R (1, k)⁻¹ x, R (g, 1) y⟫_ℂ)
    rw [← hadj, ← ContinuousLinearMap.comp_apply, ← hmul]
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
    ring

end Two

section Inf

variable (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
  [∀ v, InnerProductSpace ℂ (H v)] {σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)}
  {dv : InfinitePlace I.F → ℝ} {w : ∀ v, H v}

theorem phInf_int (hL : ∀ v, Integrable (phLoc (ε := I.ε v) (σ v) (w v) (dv v)) (Formalism.REAL.muG (I.ε v))) :
    Integrable (phInf I σ w dv) (muInf I) := by
  have heq : phInf I σ w dv = fun g => ∏ v, phLoc (ε := I.ε v) (σ v) (w v) (dv v) (g v) := by
    funext g
    show ((∏ v, dv v : ℝ) : ℂ) * star (∏ v, ⟪w v, σ v (umat (g v)) (w v)⟫_ℂ) =
      ∏ v, ((dv v : ℂ) * star ⟪w v, σ v (umat (g v)) (w v)⟫_ℂ)
    rw [Finset.prod_mul_distrib, Complex.ofReal_prod, star_prod]
  rw [heq]
  exact Integrable.fintype_prod_dep (f := fun v => phLoc (ε := I.ε v) (σ v) (w v) (dv v))
    (μ := fun v => Formalism.REAL.muG (I.ε v)) hL

theorem phInf_conv (hU : ∀ v, IsURepOn (UJset (I.ε v)) (σ v)) (hF : ∀ v, IsFdeg (Formalism.REAL.muG (I.ε v)) (σ v) (dv v))
    (hw : ∀ v, ‖w v‖ = 1) (y : I.Ginf) :
    ∫ g, phInf I σ w dv g * phInf I σ w dv (g⁻¹ * y) ∂(muInf I) = phInf I σ w dv y := by
  have heq : phInf I σ w dv = fun g => ∏ v, phLoc (ε := I.ε v) (σ v) (w v) (dv v) (g v) := by
    funext g
    show ((∏ v, dv v : ℝ) : ℂ) * star (∏ v, ⟪w v, σ v (umat (g v)) (w v)⟫_ℂ) =
      ∏ v, ((dv v : ℂ) * star ⟪w v, σ v (umat (g v)) (w v)⟫_ℂ)
    rw [Finset.prod_mul_distrib, Complex.ofReal_prod, star_prod]
  have hpt : ∀ g : I.Ginf, phInf I σ w dv g * phInf I σ w dv (g⁻¹ * y) =
      ∏ v, (phLoc (ε := I.ε v) (σ v) (w v) (dv v) (g v) *
        phLoc (ε := I.ε v) (σ v) (w v) (dv v) ((g v)⁻¹ * y v)) := by
    intro g
    rw [heq]
    simp only [← Finset.prod_mul_distrib, Pi.mul_apply, Pi.inv_apply]
  have hI := integral_fintype_prod_eq_prod (ι := InfinitePlace I.F)
    (f := fun v (h : Formalism.REAL.UJ (I.ε v)) => phLoc (ε := I.ε v) (σ v) (w v) (dv v) h *
      phLoc (ε := I.ε v) (σ v) (w v) (dv v) (h⁻¹ * y v))
    (μ := fun v => Formalism.REAL.muG (I.ε v))
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hI, heq]
  exact Finset.prod_congr rfl fun v _ => phLoc_conv (hU v) (w v) (dv v) (hF v) (hw v) (y v)

end Inf

end Formalism.L2.SG.Pf
