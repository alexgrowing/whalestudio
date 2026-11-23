import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.CountSpanSingletonAlgebraMapEqZero
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

section

variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

theorem ordAt_eq_count (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    ordAt v x = FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x) := by
  rw [ordAt, valuation_eq_exp_neg_count v hx, WithZero.log_exp, neg_neg]

theorem ordAt_algebraMap_of_liesOver {w : HeightOneSpectrum (𝓞 K₁)} {v : HeightOneSpectrum (𝓞 K)}
    (h : LiesOver w v) (x : K) :
    ordAt w (algebraMap K K₁ x) = (w.asIdeal.ramificationIdx (𝓞 K) : ℤ) * ordAt v x := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨h.symm⟩
  rw [ordAt, ordAt, ← HeightOneSpectrum.valuation_liesOver K₁ v w x, WithZero.log_pow,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  simp

theorem count_bcI_of_liesOver {w : HeightOneSpectrum (𝓞 K₁)} {v : HeightOneSpectrum (𝓞 K)}
    (h : LiesOver w v) (N : MLine K) (hN : N.I ≠ 0) :
    FractionalIdeal.count K₁ w (bcI (K1 := K₁) N.I) =
      (w.asIdeal.ramificationIdx (𝓞 K) : ℤ) * FractionalIdeal.count K v N.I := by
  obtain ⟨c, hc⟩ := v.valuation_surjective K (WithZero.exp (-FractionalIdeal.count K v N.I))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have h1 : ordAt v c = FractionalIdeal.count K v N.I := by
    rw [ordAt, hc, WithZero.log_exp, neg_neg]
  have hg : IsLocGen v c N.I := ⟨hc0, by rw [← ordAt_eq_count v hc0, h1]⟩
  have h2 := local_generator_base_change K K₁ N ⟨bcI N.I, fun σ => N.n (σ.comp (algebraMap K K₁))⟩ v w c hN
    ⟨coe_bcI N.I, fun _ => rfl⟩ (fun a => by rw [← h]; rfl) hg
  rw [← h1, ← ordAt_algebraMap_of_liesOver h, ordAt_eq_count w h2.1]
  exact h2.2.symm

end

theorem numGood_comp : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (M : Set V) (S : (K →+* ℂ) → V → ℝ) (be : HeightOneSpectrum (𝓞 K) → ℝ) (Carch Bdeg : ℝ) (K' K₁ : Type) [Field K'] [NumberField K'] [Algebra K K'] [Field K₁] [NumberField K₁] [Algebra K K₁] (f : K' →ₐ[K] K₁) (φ : V →ₗ[K] K'), NumGood M S be Carch Bdeg K' φ → NumGood M S be Carch Bdeg K₁ (f.toLinearMap.comp φ) := by
  intro K V _ _ _ _ M S be Carch Bdeg K' K₁ _ _ _ _ _ _ f φ ⟨N, hG, hd, hc, hf, ha⟩
  letI : Algebra K' K₁ := f.toRingHom.toAlgebra
  haveI : IsScalarTower K K' K₁ := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hap : ∀ F, (f.toLinearMap.comp φ) F = algebraMap K' K₁ (φ F) := fun _ => rfl
  have hne : ∀ F, (f.toLinearMap.comp φ) F ≠ 0 → φ F ≠ 0 := fun F h h0 => h (by rw [hap, h0, map_zero])
  have hb := nondegenerate_base_change K' K₁ N ⟨bcI N.I, fun σ => N.n (σ.comp (algebraMap K' K₁))⟩ hG
    ⟨coe_bcI N.I, fun _ => rfl⟩
  refine ⟨⟨bcI N.I, fun σ => N.n (σ.comp (algebraMap K' K₁))⟩, hb.1, hb.2.le.trans hd, fun σ => ?_, ?_, ?_⟩
  · exact hc (σ.comp (algebraMap K' K₁))
  · intro la w hw F hF h0
    let v : HeightOneSpectrum (𝓞 K') := w.under (𝓞 K')
    have hwv : LiesOver w v := rfl
    have hv : LiesOver v la := by
      have hw' : w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K₁)) = la.asIdeal := hw
      rw [IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 K') (𝓞 K₁), ← Ideal.comap_comap] at hw'
      exact hw'
    have : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
    have h1 := hf la v hv F hF (hne F h0)
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) (w.asIdeal.ramificationIdx (𝓞 K')))
    rw [hap, ordAt_algebraMap_of_liesOver hwv, count_bcI_of_liesOver hwv N hG.1,
      Ideal.ramificationIdx_tower (R := 𝓞 K) v.asIdeal w.asIdeal]
    push_cast
    linarith
  · intro σ F hF h0
    have h1 := ha (σ.comp (algebraMap K' K₁)) F hF (hne F h0)
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] at h1
    exact h1

end GlobalTheory.ArcCM
