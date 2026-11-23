import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernFormSecondChernClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntersectionCombinationLogNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSumSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEvalFormModRelationEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFunctionalChernIntegralStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockPoint.EvenPow

section Algebra
open MvPolynomial GlobalTheory.LineForm

def coefE (i : ℕ) (R : MvPolynomial (Fin 3) ℝ) (j : ℕ) : MvPolynomial (Fin 3) ℝ :=
  C ((-4) ^ j * (i.choose j : ℝ)) * (X 1 + X 2) ^ (2 * (i - j)) * rename (![1, 2, 0] : Fin 3 → Fin 3) R

theorem evenPow_eq_upP (i : ℕ) (R : MvPolynomial (Fin 3) ℝ) :
    ((X 3 + X 4 - 2 * X 0) ^ (2 * i) * rename (![3, 4, 2] : Fin 3 → Fin 5) R : MvPolynomial (Fin 5) ℝ) =
      upperParabolic (Finset.range (i + 1)) id (coefE i R) := by
  have e : (aeval ![X 2, X 3, X 4] (rename (![1, 2, 0] : Fin 3 → Fin 3) R) : MvPolynomial (Fin 5) ℝ) =
      rename (![3, 4, 2] : Fin 3 → Fin 5) R := by
    rw [aeval_rename, rename_eq_aeval]
    congr 2
    funext l; fin_cases l <;> simp
  have h4 : (C (-4 : ℝ) : MvPolynomial (Fin 5) ℝ) = -4 := by rw [map_neg, map_ofNat]
  rw [pow_mul, show ((X 3 + X 4 - 2 * X 0) ^ 2 : MvPolynomial (Fin 5) ℝ) =
    (-4) * (X 0 * (X 3 + X 4 - X 0)) + (X 3 + X 4) ^ 2 by ring, add_pow, upperParabolic, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [coefE, map_mul, map_pow, map_add, e, aeval_X, aeval_C, algebraMap_eq, h4, map_natCast, id]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_pow,
    ← pow_mul]
  ring

theorem sum_pm (i : ℕ) (a b : ℝ) :
    ∑ j ∈ Finset.range (i + 1), aeval ![a + b, a * b] (pm j) * ((-4) ^ j * (i.choose j : ℝ) * (a + b) ^ (2 * (i - j))) =
      1 / (2 * (i : ℝ) + 1) * (b - a) ^ (2 * i) := by
  simp_rw [GlobalTheory.LineFormModel.aeval_pm, ← intervalIntegral.integral_mul_const]
  rw [← intervalIntegral.integral_finsetSum fun j _ => by apply Continuous.intervalIntegrable; fun_prop]
  have hI : ∀ t : ℝ, ∑ j ∈ Finset.range (i + 1), ((a * t + b * (1 - t)) * (a * (1 - t) + b * t)) ^ j *
      ((-4) ^ j * (i.choose j : ℝ) * (a + b) ^ (2 * (i - j))) = (1 - 2 * t) ^ (2 * i) * (b - a) ^ (2 * i) := by
    intro t
    rw [← mul_pow, pow_mul, show ((1 - 2 * t) * (b - a)) ^ 2 =
      (-4) * ((a * t + b * (1 - t)) * (a * (1 - t) + b * t)) + (a + b) ^ 2 by ring, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow (-4 : ℝ), ← pow_mul]
    ring
  simp_rw [hI]
  rw [intervalIntegral.integral_mul_const]
  congr 1
  rw [intervalIntegral.integral_comp_sub_mul (fun x : ℝ => x ^ (2 * i)) two_ne_zero, integral_pow]
  have : (1 - 2 * 1 : ℝ) ^ (2 * i + 1) = -1 := by
    rw [show (1 - 2 * 1 : ℝ) = -1 by norm_num]
    exact Odd.neg_one_pow ⟨i, rfl⟩
  rw [this]
  simp only [mul_zero, sub_zero, one_pow, smul_eq_mul]
  push_cast
  field_simp
  norm_num

theorem dvd_sub_subst (Z : MvPolynomial (Fin 4) ℝ) :
    (X 3 - X 1 * X 2 : MvPolynomial (Fin 4) ℝ) ∣ Z - aeval ![X 0, X 1, X 2, X 1 * X 2] Z := by
  induction Z using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hP hQ
  | mul_X P n hP =>
    have hn : (X 3 - X 1 * X 2 : MvPolynomial (Fin 4) ℝ) ∣ X n - aeval ![X 0, X 1, X 2, X 1 * X 2] (X n : MvPolynomial (Fin 4) ℝ) := by
      fin_cases n <;> simp
    rw [map_mul, show ∀ a b c d : MvPolynomial (Fin 4) ℝ, a * b - c * d = (a - c) * b + c * (b - d) by intros; ring]
    exact dvd_add (hP.mul_right _) (hn.mul_left _)

theorem downP_subst (i : ℕ) (R : MvPolynomial (Fin 3) ℝ) :
    (aeval ![X 0, X 1, X 2, X 1 * X 2] (downP (Finset.range (i + 1)) id (coefE i R)) : MvPolynomial (Fin 4) ℝ) =
      rename (![1, 2, 0] : Fin 3 → Fin 4) (C (1 / (2 * (i : ℝ) + 1)) * ((X 1 - X 0) ^ (2 * i) * R)) := by
  apply MvPolynomial.funext
  intro x
  rw [← coe_aeval_eq_eval]
  change aeval x _ = aeval x _
  simp only [downP, coefE, map_sum, map_mul, map_pow, map_add, map_sub, aeval_rename, rename_C, rename_X, aeval_C, aeval_X, id]
  simp only [← AlgHom.comp_apply, comp_aeval]
  have e₁ : (fun l => (aeval fun l => (aeval x) ((![X 0, X 1, X 2, X 1 * X 2] : Fin 4 → MvPolynomial (Fin 4) ℝ) l))
      ((![X 1 + X 2, X 3] : Fin 2 → MvPolynomial (Fin 4) ℝ) l)) = ![x 1 + x 2, x 1 * x 2] := by
    funext l; fin_cases l <;> simp
  have e₂ : (fun l => (aeval fun l => (aeval x) ((![X 0, X 1, X 2, X 1 * X 2] : Fin 4 → MvPolynomial (Fin 4) ℝ) l))
      (((![X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 4) ℝ) ∘ (![1, 2, 0] : Fin 3 → Fin 3)) l)) = x ∘ (![1, 2, 0] : Fin 3 → Fin 4) := by
    funext l; fin_cases l <;> simp
  rw [e₁, e₂, ← mul_assoc]
  have := sum_pm i (x 1) (x 2)
  simp only [← mul_assoc, ← Finset.sum_mul] at this ⊢
  congr 1
  simpa using this

theorem evalF_rename {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {ι κ : Type} (f : ι → κ)
    (w : κ → A.Pt → GlobalTheory.CxForm.Ev n) (P : MvPolynomial ι ℝ) : evalF A w (rename f P) = evalF A (w ∘ f) P := by
  funext x
  simp only [evalF, fld, map_rename, aeval_rename]
  rfl

end Algebra

section Main
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

theorem archInt_evenPow : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (ΨB : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsGeoFun ![VMetric.grLB flB 0 H, VMetric.grLB flB 1 H, A] d ΨB →
    ∀ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v ∧
        ∀ y ∈ offSupp p σ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr), v y < 1 ∧ logNorm (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).φ σ) r y = Real.log (1 - v y) / 2) →
    ∀ (i : ℕ) (R : MvPolynomial (Fin 3) ℝ), 2 * i ≤ d → R.IsHomogeneous (d - 2 * i) →
    ∀ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ),
      ((X 3 - X 0) * ((X 3 + X 4 - 2 * X 0) ^ (2 * i) * rename (![3, 4, 2] : Fin 3 → Fin 5) R) : MvPolynomial (Fin 5) ℝ) =
        ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1) →
      -∑ n ∈ s, c n * (comb (fam5 π w H flB fl A) n).archInt ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)) (d + 1) hr =
        1 / (2 * (2 * (i : ℝ) + 1)) * ΨB ((X 1 - X 0) ^ (2 * i) * R) := by
  intro _ k _ B Y _ _ q p d hB hY hreg π w E h H flB fl hfl A ΨB hΨ r hr hv i R hi hR s c hs
  have hB' : GlobalTheory.CxForm.IsRegVar q d := ⟨hB, hreg⟩
  have hπ : Smooth π :=
    have := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π Unit (fun _ => E) (fun _ => 2) (fun _ => fl) (fun _ => h.isVB) hfl
    @SmoothOfRelativeDimension.smooth _ _ _ π this
  have hY' : GlobalTheory.CxForm.IsRegVar p (d + 1) := by
    refine ⟨hY, fun y => ?_⟩
    have := hB.isLocallyNoetherian
    have := GlobalTheory.ThetaExtend.isRegularRing_stalk hreg π y
    exact .of_isRegularRing_of_isLocalRing _
  choose v hv₁ hv₂ using hv
  have hK : ((X 3 + X 4 - 2 * X 0) ^ (2 * i) * rename (![3, 4, 2] : Fin 3 → Fin 5) R :
      MvPolynomial (Fin 5) ℝ).IsHomogeneous d := by
    have h1 : (X 3 + X 4 - 2 * X 0 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 := by
      rw [two_mul]
      exact ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).sub ((isHomogeneous_X _ _).add (isHomogeneous_X _ _))
    have := (h1.pow (2 * i)).mul (hR.rename_isHomogeneous (f := (![3, 4, 2] : Fin 3 → Fin 5)))
    rwa [show 1 * (2 * i) + (d - 2 * i) = d by omega] at this
  have hG : (C (1 / (2 * (i : ℝ) + 1)) * ((X 1 - X 0) ^ (2 * i) * R) : MvPolynomial (Fin 3) ℝ).IsHomogeneous d := by
    have h1 : (X 1 - X 0 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 1 := (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
    have := ((h1.pow (2 * i)).mul hR).C_mul (1 / (2 * (i : ℝ) + 1))
    rwa [show 1 * (2 * i) + (d - 2 * i) = d by omega] at this
  have hs' : ∑ n ∈ s, (-c n) • lin (fun i => (n i : ℝ)) ^ (d + 1) = (X 0 - X 3) * ((X 3 + X 4 - 2 * X 0) ^ (2 * i) *
      rename (![3, 4, 2] : Fin 3 → Fin 5) R : MvPolynomial (Fin 5) ℝ) := by
    simp only [neg_smul, Finset.sum_neg_distrib]
    rw [← hs]
    ring
  have h1 := GlobalTheory.T.arch_intersection_combination_log_norm k Y p (d + 1) hY' (Fin 5) (fam5 π w H flB fl A) _ r hr (fun σ y => Real.log (1 - v σ y) / 2)
    (fun σ y hy => (hv₂ σ y hy).2) s (fun n => -c n)
  have h2 := GlobalTheory.T.geometric_functional_chern_integral k B q d hB' (Fin 3) _ ΨB hΨ _ hG
  rw [C_mul', map_smul, smul_eq_mul] at h2
  simp only [neg_mul, Finset.sum_neg_distrib] at h1
  rw [h1, show ∀ t : ℝ, 1 / (2 * (2 * (i : ℝ) + 1)) * t = 1 / 2 * (1 / (2 * (i : ℝ) + 1) * t) by
    intro t; rw [← mul_assoc, div_mul_div_comm, one_mul], h2, ← C_mul']
  have := hB.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hs', GlobalTheory.T.flag_bundle_chern_integral_pull_first k B Y q p d hB' hY' π w E h H flB fl hfl A σ (v σ) (hv₁ σ) _ hK, evenPow_eq_upP,
    GlobalTheory.T.flag_bundle_chern_integral_pull_second k B Y q p d hB' hY' π w E h H flB fl hfl A σ _
      ((GlobalTheory.T.firstChern_form_properties k B q d hB' σ).2.1 E h H flB flB).1.1, sub_zero,
    GlobalTheory.LineForm.ChernFibre.fibre_integral_eq k B Y q p d hB' hY' π w E h H flB fl hfl A σ,
    GlobalTheory.T.integral_evalForm_mod_relation_eq k B q d hB' E h H flB A σ _ _ (dvd_sub_subst _), downP_subst, evalF_rename]
  congr 3
  funext l
  fin_cases l <;> rfl

end Main

end GlobalTheory.BlockPoint.EvenPow
