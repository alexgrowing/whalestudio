import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.HermNorm

section Form

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V) (s : K →+* ℂ)

theorem form_sum_right {J : Type} (t : Finset J) (x : V) (c : J → K) (y : J → V) :
    h.form s x (∑ j ∈ t, c j • y j) = ∑ j ∈ t, s (c j) * h.form s x (y j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using h.smul_right s 0 x 0
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, h.smul_right, ih]

theorem form_sum_left {J : Type} (t : Finset J) (c : J → K) (x : J → V) (y : V) :
    h.form s (∑ i ∈ t, c i • x i) y = ∑ i ∈ t, starRingEnd ℂ (s (c i)) * h.form s (x i) y := by
  rw [← h.conj_symm, form_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, h.conj_symm]

end Form

theorem hermForm_sum_sum {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : Fin n → ℂ) (W : Fin n → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • W i) (∑ i, a i • W i) =
      ∑ i, starRingEnd ℂ (a i) * ∑ j, a j * hermForm Hm (W j) (W i) := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul,
    sum_dotProduct, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem form_eq {K : Type} [Field K] {g n : ℕ} (h : HermFam K (Fin n → K)) (s : K →+* ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin n → Fin g → ℂ) (r : ℂ)
    (e : ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = r * hermForm Hm (W j) (W i)) (c : Fin n → K) :
    h.form s c c = r * hermForm Hm (∑ i, s (c i) • W i) (∑ i, s (c i) • W i) := by
  have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → K) := pi_eq_sum_univ' c
  rw [hermForm_sum_sum, Finset.mul_sum]
  conv_lhs => rw [hc, form_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [form_sum_right, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [e]; ring

theorem isLieNormSq_form : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (s : K →+* ℂ) u c, F.IsCoord u c → IsLieNormSq P u (s.comp (algebraMap (𝓞 K) K)) (h.form s c c).re := by
  rintro - - K _ _ P F h hh s u c ⟨-, w, hw, hc⟩
  obtain ⟨Q, ψ, v', U, Hm, χ, W, hQ, hA, hv, e⟩ := hh s
  refine (EllComp.isLieNormSq_iff F.fib hw s _).1 ?_
  obtain ⟨w', hw', -⟩ := existsUnique_isVecOver hQ.2.1.1 w
  have hc' := (lieComb_baseChange _ _ s _ _ ψ hQ.2.1 _ F.v w c v' w' (fun i => (hv i).1) hc).1 hw'
  refine ⟨Q, ψ, w', U, Hm, χ, ∑ i, s (c i) • W i, hQ, hw', hA,
    UnifDifferential.isDiff_of_isLieComb _ _ _ _ U W v' _ w'
      (fun i => (hv i).1.isTangent hQ.2.1 (F.basis.1 i)) (fun i => (hv i).2) hc', ?_⟩
  rw [form_eq h s Hm W _ e, Complex.re_ofReal_mul]

end GlobalTheory.CM.HermNorm
end
