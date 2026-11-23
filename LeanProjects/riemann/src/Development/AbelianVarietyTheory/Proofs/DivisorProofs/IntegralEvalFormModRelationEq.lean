import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDdcClosedFormZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOfValuesSesq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcFormLocFormChernFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernAtOneEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsFormStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement

set_option autoImplicit false

noncomputable section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder

namespace GlobalTheory.FlagChernWeil

open GlobalTheory.CxForm

variable {M : Type} [TopologicalSpace M] {n : ℕ}

end GlobalTheory.FlagChernWeil

namespace GlobalTheory.FlagChernWeil

open GlobalTheory.CxForm Filter Topology

variable {M : Type} [TopologicalSpace M] {n : ℕ}

end GlobalTheory.FlagChernWeil

namespace GlobalTheory.FlagChernWeil

open GlobalTheory.CxForm

variable {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n}

end GlobalTheory.FlagChernWeil

namespace GlobalTheory.FlagChernWeil

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

theorem evalF_sub {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (w : ι → A.Pt → Ev n)
    (P Q : MvPolynomial ι ℝ) : evalF A w (P - Q) = evalF A w P - evalF A w Q := by
  funext x
  simp only [evalF, fld, map_sub, Pi.sub_apply, AddSubgroupClass.coe_sub]

theorem evalF_mul {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (w : ι → A.Pt → Ev n)
    (P Q : MvPolynomial ι ℝ) : evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  funext x
  simp only [evalF, fld, map_mul, Pi.mul_apply, MulMemClass.coe_mul]

theorem integral_evalForm_flag_family_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (A : HermLB p) (σ : k →+* ℂ)
    (Z Z' : MvPolynomial (Fin 4) ℝ),
    (MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2 : MvPolynomial (Fin 4) ℝ) ∣ Z - Z' →
      (hX.atlas σ).integral (evalF (hX.atlas σ) (fam4 hX σ H fl A) Z) =
        (hX.atlas σ).integral (evalF (hX.atlas σ) (fam4 hX σ H fl A) Z') := by
  intro k _ X _ p D hX E h H fl A σ Z Z' ⟨W, hW⟩
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hX.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨hL, hE, -⟩ := GlobalTheory.T.firstChern_form_properties k X p D hX σ
  obtain ⟨hω, hc, hc₁, hc₂, -, -, -, hd⟩ := hE E h H fl fl
  have hev := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ D (hX.atlas σ)).2.2.2.1 (Fin 4) (fam4 hX σ H fl A)
  have f0 : ∀ i, (hX.atlas σ).IsForm (fld _ (fam4 hX σ H fl A i)) := by
    intro i
    fin_cases i
    exacts [(hL _ A).1.1, (hL _ A).1.1, (hL _ A).1.1, hc.1]
  have f1 : ∀ i, (hX.atlas σ).del (fld _ (fam4 hX σ H fl A i)) = 0 := by
    intro i
    fin_cases i
    exacts [(hL _ A).2.1, (hL _ A).2.1, (hL _ A).2.1, hc₁]
  have f2 : ∀ i, (hX.atlas σ).dbar (fld _ (fam4 hX σ H fl A i)) = 0 := by
    intro i
    fin_cases i
    exacts [(hL _ A).2.2.1, (hL _ A).2.2.1, (hL _ A).2.2.1, hc₂]
  have hX3 : evalF (hX.atlas σ) (fam4 hX σ H fl A) (MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2) =
      (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) := by
    rw [hd]
    funext x
    simp only [evalF, fld, map_sub, map_mul, map_X, aeval_X]
    rfl
  have e := GlobalTheory.T.integral_sub_of_isForm' (hX.atlas σ) _ _ (hev Z f0).1 (hev Z' f0).1
  rw [← evalF_sub, hW, evalF_mul, hX3,
    GlobalTheory.T.integral_ddc_closed_form_zero (hX.atlas σ) _ _ hω.1 (hev W f0).1 ((hev W f0).2.1 f1) ((hev W f0).2.2 f2)] at e
  linarith

end GlobalTheory.FlagChernWeil
