import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarComplexPointsCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralChernCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableRegularVarietyStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.ChernPoly

theorem chernPart_offSupp_null : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D →
    ∀ (σ : k →+* ℂ) (N : HermLB p) {r : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r)
    {M : LB Y} (φ : Weight p σ M) (ε : ℤˣ), φ.chernPart D ε (offSupp p σ (N.div hr))ᶜ = 0 := by
  intro k _ Y _ p D hp σ N r hr M φ ε
  have e : (offSupp p σ (N.div hr))ᶜ =
      {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((N.div hr).supp : Set Y)} := by
    ext y
    simp only [Set.mem_compl_iff, mem_offSupp, not_not]
    rfl
  rw [e]
  exact GlobalTheory.ChernNull.chernPart_over_closed hp _ (N.div hr).supp.isClosed
    (CartierDiv.genericPoint_notMem_supp _) σ φ ε

theorem chernPart_comb_eq_part : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (ε : ℤˣ),
    ((comb L n).φ σ).chernPart D ε = (hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε := GlobalTheory.T.chern_part_combination_power

theorem wInt_sum_lin_pow : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (g : CxPts p σ → ℝ) (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
    (∀ n ∈ s, ∀ ε : ℤˣ, Integrable g ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε)) →
    wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) =
      ∑ n ∈ s, c n * wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) := GlobalTheory.T.weighted_integral_chern_combination

theorem archIntegrable_of_isRegVar : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsRegVar p D →
    ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ} (hr : IsRatSec N.B r), M.ArchIntegrable N D hr := GlobalTheory.T.archIntegrable_regular_variety

theorem archInt_sum_eq_wInt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (ι : Type) [Fintype ι] (L : ι → HermLB p) (N : HermLB p)
    (r : N.B.ι → X.functionFieldˣ) (hr : IsRatSec N.B r) (g : ∀ σ : k →+* ℂ, CxPts p σ → ℝ),
    (∀ σ, ∀ y ∈ offSupp p σ (N.div hr), logNorm (N.φ σ) r y = g σ y) →
    ∀ (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
      ∑ n ∈ s, c n * (comb L n).archInt N D hr =
        ∑ᶠ σ : k →+* ℂ, wInt (hX.atlas σ) (g σ) (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) := by
  intro k _ X _ p D hX ι _ L N r hr g hg s c
  haveI : Finite (k →+* ℂ) := (GlobalTheory.T.arith_var_complex_points_compact hX.toIsArithVar).1
  haveI := Fintype.ofFinite (k →+* ℂ)
  have key : ∀ (n : ι → ℤ) (σ : k →+* ℂ),
      ((comb L n).φ σ).chernInt D (offSupp p σ (N.div hr)) (logNorm (N.φ σ) r) =
        wInt (hX.atlas σ) (g σ) (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ∧
      ∀ ε : ℤˣ, Integrable (g σ)
        ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε) := by
    intro n σ
    have hae : ∀ ε : ℤˣ, ∀ᵐ y ∂((comb L n).φ σ).chernPart D ε, y ∈ offSupp p σ (N.div hr) := fun ε =>
      measure_eq_zero_iff_ae_notMem.1
        (chernPart_offSupp_null hX.toIsArithVar σ N hr _ ε) |>.mono fun y hy => by simpa using hy
    have hres : ∀ ε : ℤˣ, (((comb L n).φ σ).chernPart D ε).restrict (offSupp p σ (N.div hr)) =
        ((comb L n).φ σ).chernPart D ε := fun ε => Measure.restrict_eq_self_of_ae_mem (hae ε)
    have hfg : ∀ ε : ℤˣ, logNorm (N.φ σ) r =ᵐ[((comb L n).φ σ).chernPart D ε] g σ := fun ε =>
      (hae ε).mono fun y hy => hg σ y hy
    have hint := archIntegrable_of_isRegVar hX (comb L n) N hr σ
    refine ⟨?_, fun ε => ?_⟩
    · rw [Weight.chernInt, hres, hres, integral_congr_ae (hfg 1), integral_congr_ae (hfg (-1)), wInt,
        chernPart_comb_eq_part hX σ L n, chernPart_comb_eq_part hX σ L n]
    · rw [← chernPart_comb_eq_part hX σ L n]
      have h1 : IntegrableOn (logNorm (N.φ σ) r) (offSupp p σ (N.div hr)) (((comb L n).φ σ).chernPart D ε) := by
        rcases Int.units_eq_one_or ε with rfl | rfl
        exacts [hint.1, hint.2]
      rw [IntegrableOn, hres] at h1
      exact h1.congr (hfg ε)
  have hL : ∀ n : ι → ℤ, (comb L n).archInt N D hr = ∑ σ, wInt (hX.atlas σ) (g σ)
      (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) := fun n => by
    rw [HermLB.archInt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun σ _ => (key n σ).1
  rw [finsum_eq_sum_of_fintype]
  simp only [hL, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [wInt_sum_lin_pow hX σ L (g σ) s c fun n _ ε => (key n σ).2 ε]

end GlobalTheory.ChernPoly
