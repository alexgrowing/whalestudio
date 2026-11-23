import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem rrkp_coef_cont {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn (UJset ε) σ) (w : H) :
    Continuous (coefOn (ε := ε) σ w w) :=
  continuous_const.inner (homOf_cont σ h w)

theorem rrk_phi_meas (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : Measurable X.φ := by
  have he : Measurable X.e := (hX.1.2.2.2.2.2.2.1.1).continuous.measurable
  have hc : ∀ v, Measurable (coefOn (ε := X.I.ε v) (X.σ v) (X.w v) (X.w v)) := fun v =>
    (rrkp_coef_cont (hX.2.1.1 v).2.2.1 (X.w v)).measurable
  have hp : Measurable (phOf X.I X.σ X.w) := by
    unfold phOf
    refine measurable_const.mul (continuous_star.measurable.comp ?_)
    exact Finset.measurable_prod _ fun v _ => (hc v).comp (measurable_pi_apply v)
  unfold CData.φ phe
  exact (hp.comp measurable_fst).mul (he.comp measurable_snd)

theorem rrkp_loc (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower)
    (v : InfinitePlace X.I.F) :
    (∀ g : Formalism.REAL.UJ (X.I.ε v), phLoc (X.I.ε v) (X.σ v) (X.w v) g⁻¹ = star (phLoc (X.I.ε v) (X.σ v) (X.w v) g)) ∧
      ∀ y : Formalism.REAL.UJ (X.I.ε v),
        ∫ g, phLoc (X.I.ε v) (X.σ v) (X.w v) g * phLoc (X.I.ε v) (X.σ v) (X.w v) (g⁻¹ * y) ∂(Formalism.REAL.muG (X.I.ε v)) =
          phLoc (X.I.ε v) (X.σ v) (X.w v) y := by
  obtain ⟨-, h2, h3, -⟩ := hloc X.I.n (X.I.ε v) (X.lam v) (hX.1.2.2.2.2.1 v) (X.H v) (X.σ v) (hX.2.1.1 v) (X.w v)
    (hX.2.1.2.1 v) X.h (hX.2.2 v) (h1 v)
  refine ⟨fun g => ?_, fun y => ?_⟩
  · rw [← h2 g, star_star]
  · have h := h3 1 y
    have hm : coefOn (X.σ v) (X.w v) (X.w v) (1 : Formalism.REAL.UJ (X.I.ε v)) = 1 := by
      have hσ : X.σ v 1 = 1 := (hX.2.1.1 v).2.2.1.1.1
      have hu : umat (1 : Formalism.REAL.UJ (X.I.ε v)) = 1 := rfl
      unfold coefOn
      rw [hu, hσ, one_apply_eq_self, inner_self_eq_norm_sq_to_K, (hX.2.1.2.1 v).1]
      simp
    rw [hm, one_mul] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp

theorem rrk_phi_star (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (h1 : X.GapAboveThreeHalvesPower) (z : X.I.GA) : X.φ z⁻¹ = star (X.φ z) := by
  have he : ∀ x, X.e x⁻¹ = star (X.e x) := hX.1.2.2.2.2.2.2.1.2.2.1
  unfold CData.φ phe
  rw [star_mul', X.phOf_eq_prod, X.phOf_eq_prod]
  have e1 : (z⁻¹).2 = (z.2)⁻¹ := rfl
  rw [e1, he]
  congr 1
  have e2 : star (∏ v, phLoc (X.I.ε v) (X.σ v) (X.w v) (z.1 v)) =
      ∏ v, star (phLoc (X.I.ε v) (X.σ v) (X.w v) (z.1 v)) := map_prod (starRingEnd ℂ) _ _
  rw [e2]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact (rrkp_loc D hloc X hX h1 v).1 (z.1 v)

theorem rrk_phi_idem (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (h1 : X.GapAboveThreeHalvesPower) (z : X.I.GA) : ∫ g, X.φ g * X.φ (g⁻¹ * z) ∂(X.I.muA X.μf) = X.φ z := by
  have he : X.I.convF X.μf X.e X.e = X.e := hX.1.2.2.2.2.2.2.1.2.1
  have he' : ∫ y, X.e y * X.e (y⁻¹ * z.2) ∂X.μf = X.e z.2 := congrFun he z.2
  have hfun : (fun g : X.I.GA => X.φ g * X.φ (g⁻¹ * z)) = fun g : X.I.GA =>
      (fun a : X.I.Ginf => ∏ v, (phLoc (X.I.ε v) (X.σ v) (X.w v) (a v) *
        phLoc (X.I.ε v) (X.σ v) (X.w v) ((a v)⁻¹ * z.1 v))) g.1 *
      (fun y : X.I.Gf => X.e y * X.e (y⁻¹ * z.2)) g.2 := by
    funext g
    unfold CData.φ phe
    beta_reduce
    rw [X.phOf_eq_prod, X.phOf_eq_prod, Finset.prod_mul_distrib]
    have e1 : (g⁻¹ * z).2 = (g.2)⁻¹ * z.2 := rfl
    have e2 : ∀ v, (g⁻¹ * z).1 v = (g.1 v)⁻¹ * z.1 v := fun v => rfl
    simp only [e1, e2]
    ring
  rw [hfun]
  unfold AutInst.muA
  refine (integral_prod_mul (μ := Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) (ν := X.μf)
    (fun a : X.I.Ginf => ∏ v, (phLoc (X.I.ε v) (X.σ v) (X.w v) (a v) *
        phLoc (X.I.ε v) (X.σ v) (X.w v) ((a v)⁻¹ * z.1 v)))
    (fun y : X.I.Gf => X.e y * X.e (y⁻¹ * z.2))).trans ?_
  rw [he', integral_fintype_prod_eq_prod (fun v (a : Formalism.REAL.UJ (X.I.ε v)) =>
    phLoc (X.I.ε v) (X.σ v) (X.w v) a * phLoc (X.I.ε v) (X.σ v) (X.w v) (a⁻¹ * z.1 v))]
  unfold CData.φ phe
  rw [X.phOf_eq_prod]
  congr 1
  exact Finset.prod_congr rfl fun v _ => (rrkp_loc D hloc X hX h1 v).2 (z.1 v)

end Formalism.MainNotions.LeviCoordinates

end
