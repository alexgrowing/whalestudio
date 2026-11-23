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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFunctionalChernIntegralStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm GlobalTheory.Published
open scoped Classical

namespace GlobalTheory.LineGysin

theorem isForm_pow {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α) (m : ℕ) :
    A.IsForm (α ^ m) := by
  induction m with
  | zero => simpa using (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).1
  | succ m ih =>
    rw [pow_succ]
    exact ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 1 _ _ ih hα).2.1

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] [IsIntegral Y] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}

omit [IsIntegral B] [IsIntegral Y] in

theorem isRegVar_lines (hB : IsRegVar q d) (hp : IsArithVar p (d + 1)) {π : Y ⟶ B} {E : B.Modules} (hE : IsVB E 2)
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2}
    (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl)) : IsRegVar p (d + 1) := by
  have hπ := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π Unit (fun _ => E) (fun _ => 2) (fun _ => fl) (fun _ => hE) hfl
  have : Smooth π := @SmoothOfRelativeDimension.smooth _ _ _ π hπ
  have := hB.toIsArithVar.isLocallyNoetherian
  refine ⟨hp, fun y => ?_⟩
  have := GlobalTheory.ThetaExtend.isRegularRing_stalk hB.regular π y
  exact .of_isRegularRing_of_isLocalRing _

theorem integral_neg_taut_mul (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) {E : B.Modules}
    {h : VMetric q E 2} (H : h.IsCInf) (flB : Vert.Flag E 2) {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2}
    (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl)) (A : HermLB q) (σ : k →+* ℂ) :
    (hY.atlas σ).integral (-fld _ (c1F hY σ (VMetric.grLB fl 0 (H.pull π w))) * fld _ (c1F hY σ (A.pull π w)) ^ d) =
      (hB.atlas σ).integral (fld _ (c1F hB σ A) ^ d) := by
  have : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  have : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  have : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  obtain ⟨hLB, -, hP⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨hLY, hEY, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  have hφ := isForm_pow (hB.atlas σ) (hLB A A).1.1 d
  have hpull : pullF hB hY σ π w (fld _ (c1F hB σ A) ^ d) = fld _ (c1F hY σ (A.pull π w)) ^ d := by
    rw [(hP Y p (d + 1) hY π w).2.1 A]
    funext x
    exact map_pow (pull _) _ d
  have h0 := (GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl hfl A σ _ hφ 0).2
  have h1 := (GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl hfl A σ _ hφ 1).1
  have e1 : evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3] (hs 0)) = 1 := by
    funext x
    simp [evalF, fld, hs]
  rw [e1, hpull, pow_zero, mul_one, one_mul] at h0
  rw [hpull, pow_one] at h1
  have hω := (hEY _ (h.pull π w) (H.pull π w) fl fl).1.1
  have hS := (hLY (fam5 π w H flB fl A 0) (A.pull π w)).1.1
  have hA := isForm_pow (hY.atlas σ) (hLY (A.pull π w) (A.pull π w)).1.1 d
  have C := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hY.atlas σ)).2.1 1
  have e := GlobalTheory.T.integral_sub_of_isForm' (hY.atlas σ) _ _ (C _ _ hω hA).2.1 (C _ _ (C _ _ hS hω).1 hA).2.1
  rw [h0, h1, ← sub_mul, sub_add_cancel_right] at e
  simpa [fam5] using e

theorem geoFun_neg_taut_mul_pow : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y]
    (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf), Nonempty (Vert.Flag E 2) →
    ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
      IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Ψ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ),
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), A.pull π w] (d + 1) Ψ → Ψ (-X 0 * X 1 ^ d) = gdeg A d := by
  intro hC k _ B Y _ _ q p d hq hp hr π w E h H ⟨flB⟩ fl hfl A Ψ hΨ
  have hB : IsRegVar q d := ⟨hq, hr⟩
  have hY : IsRegVar p (d + 1) := isRegVar_lines hB hp h.isVB hfl
  obtain ⟨ΨB, hΨB⟩ := ((hC.arExists k B q d hq).2 Unit fun _ => A).2
  have hom : (-X 0 * X 1 ^ d : MvPolynomial (Fin 2) ℝ).IsHomogeneous (d + 1) := by
    have := (isHomogeneous_X ℝ (0 : Fin 2)).neg.mul ((isHomogeneous_X ℝ (1 : Fin 2)).pow d)
    rwa [one_mul, add_comm] at this
  have homB : (X () ^ d : MvPolynomial Unit ℝ).IsHomogeneous d := by
    simpa using (isHomogeneous_X ℝ ()).pow d
  have eB : gdeg A d = ΨB (X () ^ d) := by
    rw [← lin_single (), hΨB.1, (isometric_comb_single (fun _ : Unit => A) ()).gdeg_eq]
  rw [eB, GlobalTheory.T.geometric_functional_chern_integral k Y p (d + 1) hY _ _ Ψ hΨ _ hom, GlobalTheory.T.geometric_functional_chern_integral k B q d hB _ _ ΨB hΨB _ homB]
  refine finsum_congr fun σ => ?_
  have e := integral_neg_taut_mul hB hY π w H flB hfl A σ
  convert e using 2
  · funext x
    simp [evalF, fld]
  · funext x
    simp [evalF, fld]

end GlobalTheory.LineGysin

end
