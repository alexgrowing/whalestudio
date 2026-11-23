import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondChernDegreeFubiniStudyLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveArithmeticKaehlerFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSecondChernDualBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeSecondChernFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodFormFromChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFormPullbackClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleRelativelyAcyclicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartFibreMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartFormEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqOfExactRealFormCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralOfContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPullbackHermitianIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDualIsometricDualDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsL2MetOfIsL2OnUnifChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealZeroFormEqSmoothFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralIsTopFormCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprRealCurveFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfExactTypeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCharacterLineBundleExpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToddPartLowDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharClassGradedDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveChernPartOmC1Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArakelovFormMulFunctionStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar BottChern ArRing ArChow HolAtlas Alt IsType IsReal dens chPart tdPart hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.AbelianRR

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {D : ℕ}

theorem isRealForm_zero {M : Type} [TopologicalSpace M] {n : ℕ} (B : HolAtlas M n) (j : ℕ) : B.IsRealForm j 0 := by
  have l (i) : B.loc 0 i = 0 := funext fun v => by
    unfold CxForm.HolAtlas.loc
    split_ifs <;> rfl
  exact ⟨⟨fun i T => by simpa [l] using contDiffOn_const, fun _ _ _ => by simp⟩,
    fun _ => ⟨fun T hT => by simp at hT, fun T => by simp⟩⟩

theorem isArForm_add (h : IsRegVar p D) {j : ℕ} {α β : h.Fld} (hα : h.IsArForm j α) (hβ : h.IsArForm j β) :
    h.IsArForm j (α + β) := by
  refine ⟨fun σ => ⟨((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ _).2.1 1 _ _ (hα.1 σ).1 (hβ.1 σ).1).1, fun x => ⟨fun T hT => ?_, fun T => ?_⟩⟩,
    fun σ σ' x x' e e' => ?_⟩
  · by_cases h0 : (bas D).repr (α σ x) T = 0
    · exact ((hβ.1 σ).2 x).1 T (by simpa [h0] using hT)
    · exact ((hα.1 σ).2 x).1 T h0
  · simp only [Pi.add_apply, map_add, Finsupp.add_apply, ((hα.1 σ).2 x).2 T, ((hβ.1 σ).2 x).2 T]
  · simp only [Pi.add_apply, map_add, smul_add, hα.2 σ σ' x x' e e', hβ.2 σ σ' x x' e e']

theorem isArForm_const (h : IsRegVar p D) (c : ℝ) : h.IsArForm 0 fun σ => (h.atlas σ).fn fun _ => c :=
  h.isArForm_fn (u := fun _ _ => c) (fun _ y => cInfAt_const c y) fun _ _ _ _ _ _ _ => rfl

theorem parts_eq {A : Type} [CommRing A] [Algebra ℚ A] (gr : ℕ → Submodule ℚ A) [GradedAlgebra gr]
    {a₀ a₁ a₂ b₀ b₁ b₂ : A} (h₀ : a₀ ∈ gr 0) (h₁ : a₁ ∈ gr 1) (h₂ : a₂ ∈ gr 2) (k₀ : b₀ ∈ gr 0) (k₁ : b₁ ∈ gr 1)
    (k₂ : b₂ ∈ gr 2) (e : a₀ + a₁ + a₂ = b₀ + b₁ + b₂) : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ := by
  have s {i : ℕ} {x : A} (hx : x ∈ gr i) : GradedAlgebra.proj gr i x = x := DirectSum.decompose_of_mem_same gr hx
  have n {i : ℕ} {x : A} (hx : x ∈ gr i) (j : ℕ) (hij : i ≠ j) : GradedAlgebra.proj gr j x = 0 :=
    DirectSum.decompose_of_mem_ne gr hx hij
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_add, s h₀, s k₀, n h₁ 0 (by decide), n h₂ 0 (by decide), n k₁ 0 (by decide), n k₂ 0 (by decide),
      add_zero] using congrArg (GradedAlgebra.proj gr 0) e
  · simpa only [map_add, s h₁, s k₁, n h₀ 1 (by decide), n h₂ 1 (by decide), n k₀ 1 (by decide), n k₂ 1 (by decide),
      add_zero, zero_add] using congrArg (GradedAlgebra.proj gr 1) e
  · simpa only [map_add, s h₂, s k₂, n h₀ 2 (by decide), n h₁ 2 (by decide), n k₀ 2 (by decide), n k₁ 2 (by decide),
      add_zero, zero_add] using congrArg (GradedAlgebra.proj gr 2) e

theorem parts_of_identity {A : Type} [CommRing A] [Algebra ℚ A] (gr : ℕ → Submodule ℚ A) [GradedAlgebra gr]
    (hb : ∀ j, 2 < j → gr j = ⊥) {m₁ m₂ α β x d w y₀ y₁ y₂ : A} (hm₁ : m₁ ∈ gr 1) (hm₂ : m₂ ∈ gr 2) (hα : α ∈ gr 1)
    (hβ : β ∈ gr 2) (hx : x ∈ gr 1) (hd : d ∈ gr 2) (hw : w ∈ gr 2) (h₀ : y₀ ∈ gr 0) (h₁ : y₁ ∈ gr 1) (h₂ : y₂ ∈ gr 2)
    (e : 1 + m₁ + m₂ - (α + β) = (1 + x + d) * (1 - w) * (y₀ + y₁ + y₂)) :
    m₁ - α = y₁ + x ∧ m₂ - β = y₂ + x * y₁ + d - w := by
  have z {i j : ℕ} {a b : A} (ha : a ∈ gr i) (hb' : b ∈ gr j) (hij : 2 < i + j) : a * b = 0 := by
    have := SetLike.mul_mem_graded ha hb'
    rwa [hb _ hij, Submodule.mem_bot] at this
  have hdw := sub_mem hd hw
  obtain ⟨e₀, e₁, e₂⟩ := parts_eq gr (SetLike.one_mem_graded gr) (sub_mem hm₁ hα) (sub_mem hm₂ hβ) h₀
    (add_mem h₁ (SetLike.mul_mem_graded hx h₀))
    (add_mem (add_mem h₂ (SetLike.mul_mem_graded hx h₁)) (SetLike.mul_mem_graded hdw h₀))
    (by
      linear_combination e - (y₀ + y₁ + y₂) * z hx hw (by decide) - (y₀ + y₁ + y₂) * z hd hw (by decide) +
        z hx h₂ (by decide) + z hdw h₁ (by decide) + z hdw h₂ (by decide))
  subst e₀
  exact ⟨by linear_combination e₁, by linear_combination e₂⟩

theorem ringdeg : ∀ (B : BottChern) (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (g : ℕ) (h : IsRegVar p 1) (h' : IsRegVar q (g + 1)) (f : Y ⟶ X) (hf : f ≫ p = q) (R : ArRing B h) (R' : ArRing B h') (F : R.CH →ₐ[ℚ] R'.CH) (G : R'.CH →ₗ[ℚ] R.CH), R.IsPull R' f hf F →
    (∀ i j : ℕ, i + 1 = j + (g + 1) →
    ∀ x ∈ R'.gr i, G x ∈ R.gr j) →
    (∀ i : ℕ, i + 1 < g + 1 →
    ∀ x ∈ R'.gr i, G x = 0) →
    (∀ x y, G (F x * y) = x * G y) →
    (∀ y, R.deg (G y) = R'.deg y) →
    ∀ (r : ℕ) (E : HermVB p r) (E' : HermVB q r), (∀ j, R'.cl E' j = F (R.cl E j)) →
    ∀ (L : HermLB q) (M : HermLB p) (θ₀ θ₁ : h.Fld), h.IsArForm 0 θ₀ →
    h.IsArForm 1 θ₁ →
    R.ch (.ofLB M) - R.a (θ₀ + θ₁) = G (R'.td E' * (1 - R'.a (R'.rForm E')) * R'.ch (.ofLB L)) →
    (∀ N : HermLB p, R.deg (R.c1 M * R.c1 N) - R.deg (R.a θ₀ * R.c1 N) = R'.deg (R'.c1 L ^ (g + 1) * F (R.c1 N)) / (g + 1).factorial + R.deg (R.cl E 1 * R.c1 N) / 2) ∧
    R.deg (R.c1 M ^ 2) / 2 - R.deg (R.a θ₁) = R'.deg (R'.c1 L ^ (g + 2)) / (g + 2).factorial + R'.deg (R'.c1 L ^ (g + 1) * F (R.cl E 1)) / (2 * (g + 1).factorial) + R.deg (R.cl E 1 ^ 2) / 8 - R.deg (R.char E (chPart r 2)) / 12 - R.deg (R.a (fun σ => (h.atlas σ).fn fun _ => rOne) * R.cl E 1) := by
  intro B k _ X Y p q g h h' f hf R R' F G hp hmem hzero hproj hGdeg r E E' hcl L M θ₀ θ₁ h₀ h₁ hid
  have hch (φ) : R'.char E' φ = F (R.char E φ) := by
    simp only [CxForm.ArRing.char, AlgHom.comp_apply, hcl]
    exact (MvPolynomial.comp_aeval_apply _ F _).symm
  have hz {j : ℕ} {x : R.CH} (hx : x ∈ R.gr j) (hj : 2 < j) : x = 0 := by
    rwa [R.gr_eq_bot j hj, Submodule.mem_bot] at hx
  have hm := GlobalTheory.T.char_class_graded_degree B k X p 1 h R r E
  set u := R.a fun σ => (h.atlas σ).fn fun _ => rOne with hu
  have htd : R'.td E' = F (1 + R.char E (tdPart r 1) + R.char E (tdPart r 2)) := by
    rw [CxForm.ArRing.td, show g + 1 + 2 = 3 + g by omega, Finset.sum_range_add,
      Finset.sum_eq_zero (s := Finset.range g), add_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hch, map_add, R.char_tdPart_zero]
    · intro j _
      rw [hch, hz (hm _).2 (by omega), map_zero]
  have hr : R'.a (R'.rForm E') = F (u * R.cl E 1) := by
    have e : h.pullFld h' f hf (fun σ => (h.atlas σ).fn fun _ => rOne) = fun σ => (h'.atlas σ).fn fun _ => rOne :=
      funext fun σ => funext fun x => AlgHom.commutes _ _
    have e' : CxForm.rCoeff 1 = rOne := by simp [CxForm.rCoeff, rOne]
    rw [map_mul, hu, hp.a 0 _ (isArForm_const h _), e, R'.a_mul 0 _ (isArForm_const h' _), CxForm.ArRing.rForm,
      Finset.sum_eq_single 1, hch, R.char_chPart_one, e']
    · exact congrArg _ (funext fun σ => funext fun x =>
        Algebra.smul_def (rOne : ℂ) (h'.coeFld (R'.om (F (R.cl E 1))) σ x))
    · intro j hj hj'
      have : Odd j := (Finset.mem_filter.1 hj).2
      rw [hch, hz (hm _).1 (by obtain ⟨i, rfl⟩ := this; omega), map_zero, map_zero]
      exact smul_zero _
    · simp
  let y (i : ℕ) : R.CH := (((g + i).factorial : ℚ)⁻¹) • G (R'.c1 L ^ (g + i))
  have hl (j : ℕ) : R'.c1 L ^ j ∈ R'.gr j := by simpa using SetLike.pow_mem_graded j (R'.constant_one_mem_nonvanishing L)
  have hy (i : ℕ) : y i ∈ R.gr i := Submodule.smul_mem _ _ (hmem (g + i) i (by omega) _ (hl _))
  have hL : G (R'.ch (.ofLB L)) = y 0 + y 1 + y 2 := by
    rw [GlobalTheory.T.chern_character_line_bundle_exp, show g + 1 + 2 = g + 3 by omega, Finset.sum_range_add, map_add, map_sum, Finset.sum_eq_zero, zero_add]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_add, map_smul, y]
    · intro j hj
      rw [map_smul, hzero j (by simpa using hj) _ (hl _), smul_zero]
  have hM : R.ch (.ofLB M) = 1 + R.c1 M + (1 / 2 : ℚ) • R.c1 M ^ 2 := by
    rw [GlobalTheory.T.chern_character_line_bundle_exp]
    simp [Finset.sum_range_succ]
  have hdeg (x : R.CH) (z : R'.CH) : R.deg (G z * x) = R'.deg (z * F x) := by
    rw [mul_comm, ← hproj, mul_comm]
    exact hGdeg _
  rw [htd, hr, ← map_one F, ← map_sub, ← map_mul, hproj, hL, hM, map_add] at hid
  have hu1 : u ∈ R.gr 1 := R.a_mem 0 _ (isArForm_const h _)
  obtain ⟨e₁, e₂⟩ := parts_of_identity R.gr R.gr_eq_bot (R.constant_one_mem_nonvanishing M)
    (Submodule.smul_mem _ _ (by simpa using SetLike.pow_mem_graded 2 (R.constant_one_mem_nonvanishing M))) (R.a_mem 0 _ h₀) (R.a_mem 1 _ h₁)
    (hm 1).2 (hm 2).2 (SetLike.mul_mem_graded hu1 (R.cl_mem E 1)) (hy 0) (hy 1) (hy 2) hid
  rw [(GlobalTheory.T.todd_part_low_degree r).1, map_smul, R.char_chPart_one] at e₁ e₂
  rw [(GlobalTheory.T.todd_part_low_degree r).2, map_sub, map_smul, map_smul, map_pow, R.char_chPart_one] at e₂
  refine ⟨fun N => ?_, ?_⟩
  · have := congrArg (fun z => R.deg (z * R.c1 N)) e₁
    simp only [sub_mul, add_mul, map_sub, map_add, y, smul_mul_assoc, map_smul, hdeg, Rat.smul_def] at this
    rw [this]
    push_cast
    ring
  · have := congrArg R.deg e₂
    have d₂ := hdeg 1 (R'.c1 L ^ (g + 2))
    rw [_root_.mul_one, map_one, _root_.mul_one] at d₂
    rw [mul_comm _ (y 1)] at this
    simp only [map_sub, map_add, y, smul_mul_assoc, mul_smul_comm, map_smul, hdeg, d₂, Rat.smul_def] at this
    push_cast at this
    linear_combination this

theorem deg_a_mul_c1 : ∀ (B : BottChern) (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (h : IsRegVar p 1) (R : ArRing B h) (N : HermLB p) (t : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ σ y, CInfAt (t σ) y) → h.IsArForm 0 (fun σ => (h.atlas σ).fn (t σ)) → R.deg (R.a (fun σ => (h.atlas σ).fn (t σ)) * R.c1 N) = chInt N 1 t / 2 := by
  intro B k _ X p h R N t ht h0
  have hN := R.om_isArForm 1 _ (R.constant_one_mem_nonvanishing N)
  rw [R.a_mul 0 _ h0, R.deg_a _ (GlobalTheory.T.arakelov_form_mul_function k X p 1 h t 1 _ h0 hN), one_div_mul_eq_div, chInt]
  congr 1
  refine finsum_congr fun σ => ?_
  have : CompactSpace (CxPts p σ) := CxPts.compactSpace σ h.isProjOver
  have : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ h.isProjOver
  have : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver
  refine (GlobalTheory.T.weighted_integral_of_continuous _ 1 (h.atlas σ) (t σ) (continuous_iff_continuousAt.2 fun y => (ht σ y).continuousAt) _
    (hN.1 σ).1).trans ?_
  rw [LineForm.wInt, GlobalTheory.T.curve_chern_part_om_c1, GlobalTheory.T.curve_chern_part_om_c1, Weight.chernInt, Measure.restrict_univ, Measure.restrict_univ]

set_option maxHeartbeats 800000 in
open MvPolynomial in

theorem main : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ArithRiemannRoch →
    GlobalTheory.Published.ArithRiemannRochAbelian := by
  rintro - - ⟨-, -, hBK, hAn, ⟨B, hG⟩, hV⟩ k _ S p _ hS A _ _ g hA hsm hAV w H L hL M ψ hch
  have h : IsRegVar p 1 := ⟨hS.toIsArithVar, hS.regular⟩
  have hsm' : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  have h' : IsRegVar (A.hom ≫ p) (g + 1) := by
    have := h.toIsArithVar.isLocallyNoetherian
    refine ⟨hAV, fun y => ?_⟩
    have := GlobalTheory.ThetaExtend.isRegularRing_stalk h.regular A.hom y
    exact .of_isRegularRing_of_isLocalRing _
  have hper (σ) (y : CxPts p σ) : ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin g) (Fin g) ℂ)
      (ex : Pt (V 1) g → CxPts (A.hom ≫ p) σ), y ∈ c.e.source ∧ IsPeriodChart w c τ ex :=
    have ⟨c, τ, ex, h₁, h₂, _⟩ := hch σ y
    ⟨c, τ, ex, h₁, h₂⟩
  obtain ⟨κ, hκ, hκ'⟩ := GlobalTheory.T.exists_positive_arithmetic_kaehler_form k S p 1 h
  obtain ⟨Ω, hΩ, hΩ'⟩ := GlobalTheory.T.exists_period_form_from_charts k S p 1 h A _ h' g hA hsm w hper
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.period_chart_fibre_metric k S p 1 A g hA hsm
  have hac := GlobalTheory.T.ample_line_bundle_relatively_acyclic hV k S p 1 h.toIsArithVar A hA L.B L.isLB hL
  obtain ⟨hpκ, hpκ'⟩ := GlobalTheory.T.arithmetic_form_pullback_closed k S A.left p _ 1 _ h h' A.hom rfl 1 κ hκ
  have hcov (σ) (y : CxPts p σ) : ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin g) (Fin g) ℂ)
      (ex : Pt (V 1) g → CxPts (A.hom ≫ p) σ), y ∈ c.e.source ∧ IsUnifChart c τ ex ∧
        IsFlatOn h' (Ω σ) c.e.target τ ex :=
    have ⟨c, τ, ex, h₁, h₂⟩ := hper σ y
    ⟨c, τ, ex, h₁, h₂.isUnifChart, (hΩ' σ).2.2 c τ ex h₂⟩
  have har : h'.IsArForm 1 fun σ => fibForm h h' (Ω σ) (κ σ) := isArForm_add h' hΩ hpκ
  have hfκ (σ) : IsFlatFibration g h h' (Ω σ) (κ σ) := by
    obtain ⟨-, -, -, -, -, e₁, e₂, -⟩ := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ _).2.1 1 _ _ (hΩ.1 σ).1 (hpκ.1 σ).1
    refine ⟨hκ.1 σ, har.1 σ, e₁.trans ?_, e₂.trans ?_, hcov σ⟩
    · rw [(hΩ' σ).1, (hpκ' σ).1 (hκ' σ).1, add_zero]
    · rw [(hΩ' σ).2.1, (hpκ' σ).2 (hκ' σ).2.1, add_zero]
  have hf0 (σ) : IsFlatFibration g h h' (Ω σ) 0 := by
    have e : fibForm h h' (Ω σ) 0 = Ω σ := funext fun x =>
      (congrArg (Ω σ x + ·) (map_zero (CxForm.pull _))).trans (add_zero _)
    rw [IsFlatFibration, e]
    exact ⟨isRealForm_zero _ _, hΩ.1 σ, (hΩ' σ).1, (hΩ' σ).2.1, hcov σ⟩
  obtain ⟨C, P, hGRS⟩ := hG k
  obtain ⟨T, T', hT, hT', hid⟩ := hGRS S p 1 h A _ h' g hsm (.of_smooth _) Ω κ hfκ har
    (fun σ => GlobalTheory.T.period_chart_form_equation k S p 1 h A _ h' g hA hsm w hper σ _ _ (hΩ.1 σ) (hκ.1 σ) (hΩ' σ).2.2 (hκ' σ).2.2)
    ((w.pull A.hom rfl).map φ) ((H.pull _ _).map φ) L hac 1 (.ofLB M) ψ fun σ y =>
      have ⟨c, τ, ex, h₁, h₂, h₃⟩ := hch σ y
      ⟨c, τ, ex, h₁, h₂.isUnifChart, (hΩ' σ).2.2 c τ ex h₂, hφ w σ c τ ex h₂,
        GlobalTheory.T.isL2Metric_of_isUnifChart_of_isL2OnDiagonal k S p σ A g 1 L M ψ c τ ex h₂.isUnifChart h₃⟩
  choose T₀ hT₀ using fun σ => hBK k S p 1 h A _ h' g hsm L hac σ (Ω σ) 0 (hf0 σ)
  have hex (σ) (i) := hAn k S p 1 h A _ h' g hsm L hac σ (Ω σ) _ _ (hfκ σ) (hf0 σ) _ _ (hT σ) (hT₀ σ) i
  choose t ht ht' using fun σ => GlobalTheory.T.real_zero_form_eq_smooth_function k S p 1 h σ _ ((hT₀ σ).1 0)
  have e₀ : T' 0 = fun σ => (h.atlas σ).fn (t σ) := funext fun σ => by
    have z₁ : T 0 σ = T' 0 σ := GlobalTheory.T.eq_of_exact_type_zero _ 1 (h.atlas σ) (T 0 σ) (T' 0 σ) (fun x => (((hT σ).1 0).2 x).1)
      (fun x => (((hT' 0).1.1 σ).2 x).1) ((hT' 0).2 σ)
    have z₂ : T 0 σ = T₀ σ 0 := GlobalTheory.T.eq_of_exact_type_zero _ 1 (h.atlas σ) (T 0 σ) (T₀ σ 0) (fun x => (((hT σ).1 0).2 x).1)
      (fun x => (((hT₀ σ).1 0).2 x).1) (hex σ 0)
    rw [← z₁, z₂, ht' σ]
  have e₁ : h.integral (T' 1) = h.integral fun σ => T₀ σ 1 := by
    refine finsum_congr fun σ => ?_
    have z₁ := GlobalTheory.T.integral_eq_of_exact_real_form_curve k S p h σ (T 1 σ) (T' 1 σ) ((hT σ).1 1) ((hT' 1).2 σ)
    have z₂ := GlobalTheory.T.integral_eq_of_exact_real_form_curve k S p h σ (T 1 σ) (T₀ σ 1) ((hT σ).1 1) (hex σ 1)
    exact z₁.symm.trans z₂
  refine ⟨t, _, _, ht, GlobalTheory.T.integral_is_top_form_curve k S p h (fun σ => T₀ σ 1) fun σ => ((hT₀ σ).1 1).1,
    fun σ c τ ex j m hc hj y hy => ?_, fun N Ψ Φ hΨ hΦ => ?_⟩
  · have h₁ := (hT₀ σ).2 c τ ex j m hc.isUnifChart ((hΩ' σ).2.2 c τ ex hc) hj _ (c.e.map_source hy)
    let x : (h.atlas σ).Pt := ⟨(c, y), hy⟩
    have l (α : (h.atlas σ).Fld) : (h.atlas σ).loc α c (c.e y) = α x := (h.atlas σ).loc_crd α x
    have e₂ : hermMat ((0 : (h.atlas σ).Fld) x) = 0 := by ext; simp [hermMat]
    have e₃ : (GoodMetric.coordVec : Fin 1 → V 1) = ![EuclideanSpace.single 0 1] := by
      funext a; fin_cases a; rfl
    rw [l, l, e₂, isTorsionFormWith_zero, e₃, Finset.sum_range_succ, Finset.sum_range_one, ht' σ] at h₁
    rw [l, ← GlobalTheory.T.repr_real_curve_form _ _ (((hT₀ σ).1 1).2 x).1 (((hT₀ σ).1 1).2 x).2]
    exact h₁
  · set R := C.ring h
    set R' := C.ring h'
    let E : HermVB p g := ⟨_, w, H⟩
    have hp := C.isPull h h' A.hom rfl
    obtain ⟨χ, hχ⟩ := GlobalTheory.T.dual_pullback_hermitian_isometry k S A.left p _ A.hom rfl g E _ φ
    rw [Finset.sum_range_succ, Finset.sum_range_one] at hid
    obtain ⟨q₁, q₂⟩ := ringdeg B k S A.left p _ g h h' A.hom rfl R R' _ _ hp
      (P.mem h h' _ _ _) (P.eq_zero h h' _ _ _) (P.proj h h' _ _ _) (P.deg h h' _ _ _) g E.dual _
      (fun j => ((R'.cl_congr _ (HermVB.dual ⟨_, _, (H.pull _ _).map φ⟩) χ hχ j).symm.trans (hp.cl _ j).symm))
      L M _ _ (hT' 0).1 (hT' 1).1 hid
    have c₁ : R.cl E.dual 1 = -R.c1 (VMetric.det H) := by
      rw [R.cl_one, R.firstChernCongr _ _ (GlobalTheory.T.det_dual_isometric_dual_det k S p g E), R.firstChern_dual]; rfl
    have dΨ := R.deg_aeval hΨ
    have dΦ := R'.deg_aeval hΦ
    have a₁ := dΨ (X 0 * X 2)
    have a₂ := dΨ (X 1 * X 2)
    have a₃ := dΨ (X 0 ^ 2)
    have a₄ := dΨ (X 1 ^ 2)
    have b₁ := dΦ (X 0 ^ (g + 1) * X 2)
    have b₂ := dΦ (X 0 ^ (g + 2))
    have b₃ := dΦ (X 0 ^ (g + 1) * X 1)
    simp only [map_mul, map_pow, aeval_X, map_X, cons_val_zero, cons_val_one, cons_val_two, Nat.succ_eq_add_one,
      Nat.reduceAdd, tail_cons, head_cons] at a₁ a₂ a₃ a₄ b₁ b₂ b₃
    refine ⟨?_, fun fl a ha => ?_⟩
    · have := q₁ N
      rw [e₀, deg_a_mul_c1 B k S p h R N t ht (e₀ ▸ (hT' 0).1), c₁, neg_mul, map_neg, hp.c1, a₁, a₂, b₁] at this
      linarith
    · obtain ⟨fl', ha'⟩ := GlobalTheory.T.flag_second_chern_dual_bundle k S p g E fl a hS ha
      have g₁ : chInt (VMetric.det H) 1 (fun _ _ => rOne) = rOne * gdeg (VMetric.det H) 1 := by
        rw [gdeg, chInt, chInt, mul_finsum]
        refine finsum_congr fun σ => ?_
        rw [← Weight.chernInt_const_mul]
        simp only [_root_.mul_one]
      rw [GlobalTheory.T.arithmetic_degree_second_chern_flag B k S p h R g E.dual fl' a ha', c₁, R.deg_a _ (hT' 1).1, e₁, neg_sq, map_neg, mul_neg, mul_neg,
        map_neg, map_neg, deg_a_mul_c1 B k S p h R _ _ (fun _ y => cInfAt_const _ y) (isArForm_const h _), g₁, hp.c1, a₃, a₄, b₂,
        b₃] at q₂
      rw [neg_div] at q₂
      linarith

end GlobalTheory.AbelianRR
