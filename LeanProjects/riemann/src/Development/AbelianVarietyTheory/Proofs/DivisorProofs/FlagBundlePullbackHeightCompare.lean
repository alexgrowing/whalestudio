import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapRAevalIsHomogeneousFiveVars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntersectionCombinationLogNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSumSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEvalFormModRelationEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFunctionalChernIntegralStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.LogSinChern

open GlobalTheory.CxForm in

theorem isRegVar_of_isFlagBundle {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}
    (hB : IsRegVar q d) (hp : IsArithVar p (d + 1)) {π : Y ⟶ B} {E : B.Modules} (hE : GlobalTheory.VB.IsVB E 2)
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2}
    (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl)) : IsRegVar p (d + 1) := by
  have hπ := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π Unit (fun _ => E) (fun _ => 2) (fun _ => fl) (fun _ => hE) hfl
  have : Smooth π := @SmoothOfRelativeDimension.smooth _ _ _ π hπ
  have := hB.toIsArithVar.isLocallyNoetherian
  refine ⟨hp, fun y => ?_⟩
  have := GlobalTheory.ThetaExtend.isRegularRing_stalk hB.regular π y
  exact .of_isRegularRing_of_isLocalRing _

open GlobalTheory.LineForm GlobalTheory.CxForm in

theorem archInt_logSin_eq_chernNumber : ArCalc → ∃ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, Homog G ∧
    ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
    ∀ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v ∧
        ∀ y ∈ offSupp p σ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr), v y < 1 ∧ logNorm (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).φ σ) r y = Real.log (1 - v y) / 2) →
    ∀ (a b : ℤ) (F : MvPolynomial (Fin 5) ℝ), (X 4 - X 0) * F = onLine d a b - onBase d a b →
    ∀ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1) →
      -∑ n ∈ s, c n * (comb (fam5 π w H flB fl A) n).archInt ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)) (d + 1) hr = Ψ (G (d + 1) a b) := by
  intro _
  obtain ⟨R, hR⟩ := GlobalTheory.CovTest.SwapLine.exists_swap_coefficients
  refine ⟨fun D a b => Nat.casesOn D 0 fun d =>
    C (1 / 2 : ℝ) * X 0 * aeval ![X 0 + X 1, X 0 * X 1, X 2] (baseT d (R d a b)), ?_, ?_⟩
  · intro D a b
    cases D with
    | zero => exact isHomogeneous_zero _ _ _
    | succ d => exact (hR d a b).2.2.2
  intro k _ B Y _ _ q p d hq hp hreg π w E h H flB fl hfb A Ψ hΨ r hr hv a b F hF s c hc
  have hB : IsRegVar q d := ⟨hq, hreg⟩
  have hY : IsRegVar p (d + 1) := isRegVar_of_isFlagBundle hB hp h.isVB hfb
  choose v hv hv' using hv
  obtain ⟨h1, h2, h3, h4⟩ := hR d a b
  rw [GlobalTheory.T.arch_intersection_combination_log_norm k Y p (d + 1) hY (Fin 5) _ _ r hr (fun σ y => Real.log (1 - v σ y) / 2)
    (fun σ y hy => (hv' σ y hy).2) s c, ← hc, h1 F hF]
  erw [GlobalTheory.T.geometric_functional_chern_integral k Y p (d + 1) hY (Fin 3) _ Ψ hΨ _ h4]
  rw [← finsum_neg_distrib]
  refine finsum_congr fun σ => ?_
  rw [GlobalTheory.T.flag_bundle_chern_integral_pull_first k B Y q p d hB hY π w E h H flB fl hfb A σ (v σ) (hv σ) _ h2,
    GlobalTheory.T.flag_bundle_chern_integral_pull_second k B Y q p d hB hY π w E h H flB fl hfb A σ _ ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.1 E h H flB flB).1.1,
    GlobalTheory.LineForm.ChernFibre.fibre_integral_eq k B Y q p d hB hY π w E h H flB fl hfb A σ,
    GlobalTheory.T.integral_evalForm_mod_relation_eq k B q d hB E h H flB A σ _ _ h3,
    GlobalTheory.LineGysin.gysin k B Y q p d hB hY π w E h H flB fl hfb A σ]
  ring

end GlobalTheory.LogSinChern
