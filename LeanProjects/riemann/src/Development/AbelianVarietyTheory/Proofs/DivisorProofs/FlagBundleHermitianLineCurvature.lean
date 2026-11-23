import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem mul_sub_mul_of_add_eq {R : Type} [CommRing R] {a b c e : R} (h : a + b = c + e) :
    c * e - a * b = (e - a) * (c - a) := by
  linear_combination (-a) * h

section Calc

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem ddc_sub_of_isForm (α β : A.Fld) (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.IsForm (α - β) ∧ A.ddc (α - β) = A.ddc α - A.ddc β := by
  have C := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1
  have e : α - β = α + (-1 : ℂ) • β := by rw [neg_one_smul, sub_eq_add_neg]
  have hβ' : A.IsForm ((-1 : ℂ) • β) := (C (-1) β β hβ hβ).2.2.1
  have hdα : A.IsForm (A.dbar α) := (C 0 α α hα hα).2.2.2.2.1
  have hdβ : A.IsForm (A.dbar β) := (C 0 β β hβ hβ).2.2.2.2.1
  have hdβ' : A.IsForm ((-1 : ℂ) • A.dbar β) := (C (-1) _ _ hdβ hdβ).2.2.1
  refine ⟨e ▸ (C 0 α _ hα hβ').1, ?_⟩
  rw [e, HolAtlas.ddc, HolAtlas.ddc, HolAtlas.ddc, (C 0 α _ hα hβ').2.2.2.2.2.2.1, (C (-1) β β hβ hβ).2.2.2.2.2.2.2.2,
    (C 0 _ _ hdα hdβ').2.2.2.2.2.1, (C (-1) _ _ hdβ hdβ).2.2.2.2.2.2.2.1, smul_add, smul_comm GlobalTheory.HermFrame.kappa (-1 : ℂ),
    neg_one_smul, sub_eq_add_neg]

theorem ddc_pullback {M' : Type} [TopologicalSpace M'] {n' : ℕ} (A' : HolAtlas M' n') (f : M' → M) (hf : A.IsHolo A' f)
    (α : A.Fld) (hα : A.IsForm α) : A'.ddc (A.pullback A' f α) = A.pullback A' f (A.ddc α) := by
  have C := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1
  have P := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf).2
  have hdα : A.IsForm (A.dbar α) := (C 0 α α hα hα).2.2.2.2.1
  rw [HolAtlas.ddc, HolAtlas.ddc, ((P 0 α α).2.2.2 hα).2.2, ((P 0 (A.dbar α) (A.dbar α)).2.2.2 hdα).2.1,
    (P GlobalTheory.HermFrame.kappa (A.del (A.dbar α)) (A.del (A.dbar α))).2.2.1]

theorem fld_sub (f g : A.Pt → Ev n) : fld A (f - g) = fld A f - fld A g := by
  funext x; simp [fld]

theorem fld_mul (f g : A.Pt → Ev n) : fld A (f * g) = fld A f * fld A g := by
  funext x; simp [fld]

theorem pullback_sub {M' : Type} [TopologicalSpace M'] {n' : ℕ} (A' : HolAtlas M' n') (f : M' → M) (hf : A.IsHolo A' f)
    (α β : A.Fld) : A.pullback A' f (α - β) = A.pullback A' f α - A.pullback A' f β := by
  have P := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf).2
  rw [show α - β = α + (-1 : ℂ) • β by rw [neg_one_smul, sub_eq_add_neg], (P 0 α ((-1 : ℂ) • β)).1, (P (-1) β β).2.2.1,
    neg_one_smul, sub_eq_add_neg]

theorem pullback_mul {M' : Type} [TopologicalSpace M'] {n' : ℕ} (A' : HolAtlas M' n') (f : M' → M) (hf : A.IsHolo A' f)
    (α β : A.Fld) : A.pullback A' f (α * β) = A.pullback A' f α * A.pullback A' f β :=
  (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf).2 0 α β).2.1

end Calc

theorem ddc_omF_sub_pull : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) ∧ (hY.atlas σ).ddc (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) = evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * (X 3 - X 0)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl _ A σ
  have TY := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  have TB := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨hHolo, hc1, hE⟩ := TB.2.2 Y p (d + 1) hY π w
  obtain ⟨hc2, hsum⟩ := hE E h H flB fl
  have cY := TY.2.1 _ (h.pull π w) (H.pull π w) fl fl
  have cB := TB.2.1 E h H flB flB
  have hpf : ∀ α, pullF hB hY σ π w α =
      (hB.atlas σ).pullback (hY.atlas σ) (GlobalTheory.Points.PtsOver.map π w _) α := fun _ => rfl
  have hωB : (hB.atlas σ).IsForm (fld (hB.atlas σ) (omF hB σ h flB)) := cB.1.1
  have hpω : (hY.atlas σ).IsForm (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) := by
    rw [hpf]
    exact ((((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _ hHolo).2 0 (fld (hB.atlas σ) (omF hB σ h flB))
      (fld (hB.atlas σ) (omF hB σ h flB))).2.2.2 hωB).1
  obtain ⟨hF, hD⟩ := ddc_sub_of_isForm (hY.atlas σ) _ _ cY.1.1 hpω
  refine ⟨hF, ?_⟩
  rw [hD, hpf, ddc_pullback _ _ _ hHolo _ hωB, cY.2.2.2.2.2.2.2, cB.2.2.2.2.2.2.2, fld_sub (hB.atlas σ), fld_mul (hB.atlas σ),
    pullback_sub _ _ _ hHolo, pullback_mul _ _ _ hHolo, ← hpf, ← hpf, ← hpf, ← hc2, ← hc1, ← hc1]
  simp only [← fld_mul, ← fld_sub, evalF]
  congr 1
  funext x
  have hx := congrFun hsum x
  simp only [Pi.add_apply] at hx
  simp [fam5]
  exact mul_sub_mul_of_add_eq (R := Ev (d + 1)) hx

end GlobalTheory.LineForm

end
