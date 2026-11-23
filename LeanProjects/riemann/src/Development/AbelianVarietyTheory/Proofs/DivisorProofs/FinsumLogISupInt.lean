import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.RankOne

variable {K : Type} [Field K] [NumberField K]

theorem finsum_log_iSup_int {ι : Type} [Finite ι] {x : ι → 𝓞 K} (hx : x ≠ 0) :
    ∑ᶠ v : FinitePlace K, Real.log (⨆ i, v (x i)) = -Real.log (Ideal.absNorm (Ideal.span (Set.range x))) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx
  have hi : (x i₀ : K) ≠ 0 := by exact_mod_cast hi₀
  have hz : (fun i => (x i : K)) ≠ 0 := Function.ne_iff.2 ⟨i₀, hi⟩
  have hpos : ∀ v : FinitePlace K, 0 < ⨆ i, v (x i) := fun v =>
    lt_of_lt_of_le (FinitePlace.pos_iff.2 hi) (le_ciSup (f := fun i => v (x i)) (Set.finite_range _).bddAbove i₀)
  have h := NumberField.absNorm_mul_finprod_finitePlace_eq_one hx
  rw [← Real.log_finprod hpos, eq_inv_of_mul_eq_one_right h, Real.log_inv]

theorem finsum_log_iSup_div {n : ℕ} {b : Fin n → 𝓞 K} (hb : b ≠ 0) {d : 𝓞 K} (hd : d ≠ 0) :
    ∑ᶠ v : FinitePlace K, Real.log (⨆ k, v ((b k : K) / d)) =
      Real.log (Ideal.absNorm (Ideal.span {d})) - Real.log (Ideal.absNorm (Ideal.span (Set.range b))) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hb
  have hi : (b i₀ : K) ≠ 0 := by exact_mod_cast hi₀
  have hd' : (d : K) ≠ 0 := by exact_mod_cast hd
  have hz : (fun i => (b i : K)) ≠ 0 := Function.ne_iff.2 ⟨i₀, hi⟩
  have hdz : (fun _ : Unit => d) ≠ 0 := Function.ne_iff.2 ⟨(), hd⟩
  have hdz' : (fun _ : Unit => (d : K)) ≠ 0 := Function.ne_iff.2 ⟨(), hd'⟩
  have h1 := finsum_log_iSup_int hb
  have h2 := finsum_log_iSup_int hdz
  have f1 := GlobalTheory.Adelic.HeightExt.finite_support_log_iSup hz
  have f2 := GlobalTheory.Adelic.HeightExt.finite_support_log_iSup hdz'
  rw [Set.range_const] at h2
  have e : ∀ v : FinitePlace K, Real.log (⨆ k, v ((b k : K) / d)) =
      Real.log (⨆ k, v (b k : K)) - Real.log (⨆ _ : Unit, v (d : K)) := fun v => by
    have hpos : 0 < ⨆ i, v (b i : K) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.2 hi) (le_ciSup (f := fun i => v (b i : K)) (Set.finite_range _).bddAbove i₀)
    have hv : 0 < v (d : K) := FinitePlace.pos_iff.2 hd'
    rw [ciSup_const, ← Real.log_div hpos.ne' hv.ne']
    congr 1
    simp only [div_eq_mul_inv, map_mul, map_inv₀]
    exact (Real.iSup_mul_of_nonneg (inv_nonneg.2 hv.le) _).symm
  simp only [e]
  rw [finsum_sub_distrib f1 f2, h1, h2]
  ring

end GlobalTheory.HSCore.RankOne
