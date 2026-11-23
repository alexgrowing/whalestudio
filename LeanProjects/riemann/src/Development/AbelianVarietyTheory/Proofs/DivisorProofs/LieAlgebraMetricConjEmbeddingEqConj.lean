import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatum
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.ArchMetricCompare

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CM.LieMetricConj

variable {K : Type} [Field K]

theorem form_conj_of_single {g : ℕ} (h : HermFam K (Fin g → K)) (s : K →+* ℂ)
    (e : ∀ i j, h.form ((starRingEnd ℂ).comp s) (Pi.single i 1) (Pi.single j 1) =
      starRingEnd ℂ (h.form s (Pi.single i 1) (Pi.single j 1)))
    (a b : Fin g → K) : h.form ((starRingEnd ℂ).comp s) a b = starRingEnd ℂ (h.form s a b) := by
  have key : ∀ t : K →+* ℂ, h.form t a b =
      ∑ j, t (b j) * starRingEnd ℂ (∑ i, t (a i) * h.form t (Pi.single j 1) (Pi.single i 1)) := by
    intro t
    rw [LieMetric.form_sum_right h t a b]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← h.conj_symm t (Pi.single j 1) a, LieMetric.form_sum_right h t (Pi.single j 1) a]
  rw [key ((starRingEnd ℂ).comp s), key s]
  simp only [map_sum, map_mul, RingHom.comp_apply, e, Complex.conj_conj]

end GlobalTheory.CM.LieMetricConj

namespace GlobalTheory.CM.LieMetricConj

open GlobalTheory.ConjUnif

variable {K : Type} [Field K] [NumberField K]

theorem conj_conj_comp (s : K →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s :=
  RingHom.ext fun x => by simp

theorem single_conj (hU : ThetaUnifAV) {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K))
    (H : F.IsHerm h) (s : K →+* ℂ) (i j : Fin F.P₀.g) :
    h.form ((starRingEnd ℂ).comp s) (Pi.single i 1) (Pi.single j 1) =
      starRingEnd ℂ (h.form s (Pi.single i 1) (Pi.single j 1)) := by
  obtain ⟨Q, ψ, v, u, Hm, χ, W, a, b, c, d⟩ := H s
  obtain ⟨Q', ψ', v', u', Hm', χ', W', a', b', c', d'⟩ := H ((starRingEnd ℂ).comp s)
  obtain ⟨A'', _, ψc, hc⟩ : ∃ (A'' : Over (Sp ℂ)) (_ : GrpObj A'') (ψc : A''.left ⟶ Q'.A.left),
      IsGrpPullback A'' Q'.A cj ψc :=
    ⟨_, _, _, isGrpPullback_pullback Q'.A cj⟩
  let Q'' : Out.PolAV (Sp ℂ) := pullPol Q' hc
  have hQ : IsPolFibre (starRingEnd ℂ) Q' Q'' ψc := ⟨rfl, hc, ⟨idIso _, idIso_isGen (pull_isLB Q'.isLB ψc)⟩⟩
  have a'' : IsPolFibre s F.P₀ Q'' (ψc ≫ ψ') := by
    rw [← conj_conj_comp s]
    exact PolFibre.comp a' hQ
  choose v'' hv'' using fun k => (existsUnique_isVecOver hc.1 (v' k)).exists
  have ht : ∀ k, IsTangent (v' k) := fun k => (c' k).1.isTangent a'.2.1 (F.basis.1 k)
  have c'' : ∀ k, IsVecOver s (ψc ≫ ψ') (F.v k) (v'' k) ∧ (conjPull hc u').IsDiff (star (W' k)) (v'' k) := by
    intro k
    refine ⟨?_, cj_isDiff hc (pullId u') (ht k) (hv'' k) (c' k).2⟩
    rw [← conj_conj_comp s]
    exact (PolFibre.vec_iff a'.2.1.1 hc.1.w (c' k).1).1 (hv'' k)
  have e := LieMetric.hermForm_eq hU a a'' b (conjPull_isAH hc u' b') F.basis.1 c c'' j i
  rw [d, d', e]
  unfold hermForm
  rw [map_mul, Complex.conj_ofReal, star_star]
  congr 1
  simp [dotProduct, Matrix.mulVec, map_sum, Complex.star_def]

theorem form_conj : ∀ (K : Type) [Field K] [NumberField K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp (𝓞 K)))
    (F : GlobalTheory.CM.GenFib P) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (σ : K →+* ℂ)
    (a b : Fin F.P₀.g → K), h.form ((starRingEnd ℂ).comp σ) a b = starRingEnd ℂ (h.form σ a b) :=
  fun _ _ _ _ F h H σ a b => form_conj_of_single h σ (single_conj thetaUnifAV_all F h H σ) a b

end GlobalTheory.CM.LieMetricConj
