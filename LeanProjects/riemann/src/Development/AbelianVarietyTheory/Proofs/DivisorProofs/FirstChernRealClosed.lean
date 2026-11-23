import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosedStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LineForm.FirstChern

open Filter Topology GlobalTheory.HermFrame GlobalTheory.Points
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder ComplexConjugate

theorem dz_mul_dzb {n : ℕ} (a b : Fin n) : ∃ ε : ℤˣ, dz a * dzb b =
    ((ε : ℤ) : ℂ) • bas n ({finSumFinEquiv (.inl a)} ∪ {finSumFinEquiv (.inr b)}) := by
  obtain ⟨ε, h⟩ := bas_mul (S := {finSumFinEquiv (.inl a)}) (T := {finSumFinEquiv (.inr b)})
    (Finset.disjoint_singleton.2 (finSumFinEquiv.injective.ne Sum.inl_ne_inr))
  exact ⟨ε, by rw [dz, dzb, ← bas_singleton, ← bas_singleton, h, Units.smul_def, Int.cast_smul_eq_zsmul ℂ]⟩

theorem coe_ofValues {n : ℕ} (α : V n → V n → ℂ) :
    (ofValues α : Alt n) = ∑ a, ∑ b, α (coordVec a) (coordVec b) • (dz a * dzb b) := by
  simp only [ofValues, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym]

theorem isType_ofValues {n : ℕ} (α : V n → V n → ℂ) : IsType 1 1 (ofValues α : Alt n) := by
  intro S hS
  rw [coe_ofValues, map_sum, Finsupp.finsetSum_apply] at hS
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  rw [map_sum, Finsupp.finsetSum_apply] at ha
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  obtain ⟨ε, h⟩ := dz_mul_dzb a b
  obtain rfl : ({finSumFinEquiv (.inl a)} ∪ {finSumFinEquiv (.inr b)} : Finset (Fin (n + n))) = S := by
    by_contra hne
    rw [h] at hb
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero,
      ne_eq, not_true_eq_false] at hb
  have := a.isLt
  constructor
  · rw [Finset.card_eq_one]
    refine ⟨finSumFinEquiv (.inl a), ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, Fin.ext_iff, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]
    omega
  · rw [Finset.card_eq_one]
    refine ⟨finSumFinEquiv (.inr b), ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, Fin.ext_iff, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]
    omega

theorem isReal_ofValues {n : ℕ} {α : V n → V n → ℂ} (hα : ∀ ξ η, conj (α ξ η) = -α η ξ) :
    IsReal (ofValues α : Alt n) := by
  intro S
  have h1 (a b : Fin n) : swap (dz a * dzb b) = -(dz b * dzb a) := by
    rw [map_mul, (swap_dz a).1, (swap_dz b).2, dz, dzb,
      eq_neg_of_add_eq_zero_right (ExteriorAlgebra.ι_add_mul_swap _ _)]
  have h2 (a b : Fin n) : conj ((bas n).repr (dz a * dzb b) S) = (bas n).repr (dz a * dzb b) S := by
    obtain ⟨ε, h⟩ := dz_mul_dzb a b
    rw [h]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs <;> simp
  rw [coe_ofValues]
  simp only [map_sum, map_smul, h1, map_neg, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.neg_apply,
    smul_eq_mul]
  simp only [map_mul (starRingEnd ℂ), h2, hα]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem conj_ddc {n : ℕ} {u : V n → ℝ} {v : V n} (hu : ContDiffAt ℝ 2 u v) (ξ η : V n) :
    conj (ddc u v ξ η) = -ddc u v η ξ := by
  have hk : conj kappa = -kappa := by
    simp [kappa, neg_div, map_ofNat]
  rw [ddc, ddc, map_mul, hk, leviForm_conj_symm hu, neg_mul]

theorem chernAt_exp_neg {n : ℕ} {u : V n → ℝ} {v : V n} (hu : ContDiffAt ℝ 2 u v) :
    chernAt (fun x => (Matrix.of fun _ _ : Unit => ((Real.exp (-u x) : ℝ) : ℂ))) v 1 = ofValues (ddc u v) := by
  have h1 (G : V n → Matrix Unit Unit ℂ) : chernAt G v 1 = ofValues (chernOne G v) := by
    unfold chernAt ofValues GlobalTheory.GoodMetric.chernPoly chernOne
    rw [Matrix.coeff_charpolyRev_eq_neg_trace, Matrix.trace_neg, neg_neg, pow_one]
    simp only [Matrix.trace, Matrix.diag, GlobalTheory.GoodMetric.curvPoly, Matrix.of_apply, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, ← Algebra.smul_def, mul_smul, ← Finset.smul_sum, Finset.sum_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [h1]
  congr 1
  funext ξ η
  rw [chernOne_line (f := fun x => Real.exp (-u x)) (Real.contDiff_exp.contDiffAt.comp v hu.neg) (Real.exp_ne_zero _)
    (Eventually.of_forall fun _ => rfl)]
  simp only [Real.log_exp, ddc, leviForm_neg]
  simp

theorem c1F_isRealForm_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L : HermLB p, (hX.atlas σ).IsRealForm 1 (fld _ (c1F hX σ L)) ∧ (hX.atlas σ).del (fld _ (c1F hX σ L)) = 0 ∧
      (hX.atlas σ).dbar (fld _ (c1F hX σ L)) = 0 := by
  intro k _ X _ p D hX σ L
  have hφ : ∀ a (x : (hX.atlas σ).Pt), x.pt ∈ ptsIn p σ (L.B.U a) →
      ContDiffAt ℝ 2 (fun v => (L.φ σ).φ a (x.ch.symm v)) x.crd := by
    intro a x hx
    exact ((vInfAt_iff_cInfAt.2 (L.cInf σ a _ hx)).contDiffAt_chart x.1.1 x.2).of_le (by norm_cast)
  obtain ⟨hfr, hP⟩ := GlobalTheory.T.chernForms_frame_independent_closed (hX.atlas σ) (ι := Unit) (fun a => ptsIn p σ (L.B.U a)) (fun _ => isOpen_ptsIn _)
    (fun y => ⟨_, mem_pick L.isLB y⟩) (fun a b y => Matrix.of fun _ _ => gv p σ L.B a b y)
    (fun a b _ _ c => (AlgChart.holo c _ _).mono fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.1, hv.2.2⟩⟩)
    (fun a y => Matrix.of fun _ _ => ((Real.exp (-(L.φ σ).φ a y) : ℝ) : ℂ))
    (fun a => hX.smoothOn fun y hy _ _ => (vInfAt_iff_cInfAt.2 (L.cInf σ a y hy)).comp_contDiff
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_neg)))
    (fun a y _ => by
      have : (Matrix.of fun _ _ : Unit => ((Real.exp (-(L.φ σ).φ a y) : ℝ) : ℂ)) =
          Matrix.diagonal fun _ => ((Real.exp (-(L.φ σ).φ a y) : ℝ) : ℂ) := by
        ext; simp
      rw [this, Matrix.posDef_diagonal_iff]
      exact fun _ => Complex.zero_lt_real.2 (Real.exp_pos _))
    (fun a b y hy => by
      ext
      have h0 : 0 < ‖gv p σ L.B a b y‖ ^ 2 := by have := gv_ne_zero hy.1 hy.2; positivity
      rw [(L.φ σ).trans a b y hy.1 hy.2, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log h0]
      simp only [chg, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        Fintype.sum_unique, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', Complex.star_def]
      ring) 1
  obtain ⟨h1, h2, h3⟩ := hP (fld _ (c1F hX σ L)) fun a x hx => by
    rw [hfr a _ x hx (mem_pick (L.φ σ).isLB x.pt)]
    exact congrArg Subtype.val (chernAt_exp_neg (hφ _ x (mem_pick _ _))).symm
  exact ⟨⟨h1, fun x => ⟨isType_ofValues _, isReal_ofValues (conj_ddc (hφ _ x (mem_pick _ _)))⟩⟩, h2, h3⟩

end GlobalTheory.LineForm.FirstChern
