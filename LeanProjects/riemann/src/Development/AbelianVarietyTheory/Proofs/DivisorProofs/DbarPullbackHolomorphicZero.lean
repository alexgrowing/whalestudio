import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import ReciprocityTheory.SemistableReduction.ShareDetA
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.PullClosed

open GlobalTheory.CxForm.FormMul

variable {n m : ℕ}

open Set Filter Topology in
open scoped ComplexConjugate ContDiff in
set_option autoImplicit false in
variable {n m : ℕ} in

theorem _root_.GlobalTheory.CxForm.PullClosed.repr_sum_smul {ι : Type} [Fintype ι] (f : ι → _root_.ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (e : ι → _root_.GlobalTheory.CxForm.Alt n) (S : Finset (Fin (n + n))) :
    (fun x => (_root_.GlobalTheory.CxForm.bas n).repr (∑ i, f i x • e i) S) =
      fun x => ∑ i, f i x * (_root_.GlobalTheory.CxForm.bas n).repr (e i) S := by
  funext x
  simp [map_sum, Finsupp.finset_sum_apply]

open Set Filter Topology in
open scoped ComplexConjugate ContDiff in
set_option autoImplicit false in
variable {n m : ℕ} in

theorem _root_.GlobalTheory.CxForm.PullClosed.dbarAt_sum_smul {ι : Type} [Fintype ι] {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    {f : ι → _root_.ReciprocityTheory.L2DbarEstimates.V n → ℂ} (e : ι → _root_.GlobalTheory.CxForm.Alt n)
    (hf : ∀ i, DifferentiableAt ℝ (f i) v) :
    _root_.GlobalTheory.CxForm.dbarAt (fun x => ∑ i, f i x • e i) v =
      ∑ a, ∑ i, _root_.GlobalTheory.dbar (f i) v (_root_.GlobalTheory.GoodMetric.coordVec a) •
        (_root_.GlobalTheory.CxForm.dzb a * e i) := by
  unfold _root_.GlobalTheory.CxForm.dbarAt
  refine Finset.sum_congr rfl fun a _ => ?_
  have key : _root_.GlobalTheory.CxForm.coefwise
      (fun g => _root_.GlobalTheory.dbar g v (_root_.GlobalTheory.GoodMetric.coordVec a))
      (fun x => ∑ i, f i x • e i) =
      ∑ i, _root_.GlobalTheory.dbar (f i) v (_root_.GlobalTheory.GoodMetric.coordVec a) • e i := by
    apply (_root_.GlobalTheory.CxForm.bas n).repr.injective
    ext S
    rw [_root_.GlobalTheory.CxForm.FormMul.repr_coefwise,
      _root_.GlobalTheory.CxForm.PullClosed.repr_sum_smul]
    simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [_root_.GlobalTheory.dbar_sum fun i _ => (hf i).mul_const _]
    simp [ContinuousLinearMap.sum_apply,
      _root_.GlobalTheory.dbar_mul (hf _) (differentiableAt_const _),
      _root_.GlobalTheory.dbar_const]
  rw [key, Finset.mul_sum]
  simp [mul_smul_comm]

open Set Filter Topology in
open scoped ComplexConjugate ContDiff in
set_option autoImplicit false in
variable {n m : ℕ} in

theorem _root_.GlobalTheory.CxForm.PullClosed.sum_symm_dzb {s : Fin n → Fin n → ℂ}
    (hs : ∀ a c, s a c = s c a) :
    ∑ a, ∑ c, s a c • (_root_.GlobalTheory.CxForm.dzb a * _root_.GlobalTheory.CxForm.dzb c :
      _root_.GlobalTheory.CxForm.Alt n) = 0 := by
  have hanti : ∀ a c : Fin n,
      (_root_.GlobalTheory.CxForm.dzb a * _root_.GlobalTheory.CxForm.dzb c :
        _root_.GlobalTheory.CxForm.Alt n) =
        -(_root_.GlobalTheory.CxForm.dzb c * _root_.GlobalTheory.CxForm.dzb a) := by
    intro a c
    unfold _root_.GlobalTheory.CxForm.dzb
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  set X := ∑ a, ∑ c, s a c • (_root_.GlobalTheory.CxForm.dzb a *
    _root_.GlobalTheory.CxForm.dzb c : _root_.GlobalTheory.CxForm.Alt n) with hX
  have hneg : X = -X := by
    calc X = ∑ c, ∑ a, s a c • (_root_.GlobalTheory.CxForm.dzb a *
          _root_.GlobalTheory.CxForm.dzb c : _root_.GlobalTheory.CxForm.Alt n) := Finset.sum_comm
      _ = ∑ c, ∑ a, -(s c a • (_root_.GlobalTheory.CxForm.dzb c *
          _root_.GlobalTheory.CxForm.dzb a : _root_.GlobalTheory.CxForm.Alt n)) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
        rw [hanti a c, hs a c, smul_neg]
      _ = -X := by simp [hX, Finset.sum_neg_distrib]
  have h2 : (2 : ℂ) • X = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hneg]
    exact add_neg_cancel X
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

open Set Filter Topology in
open scoped ComplexConjugate ContDiff in
set_option autoImplicit false in
variable {n m : ℕ} in

theorem _root_.GlobalTheory.CxForm.PullClosed.analyticOnNhd_of_holo {φ : _root_.ReciprocityTheory.L2DbarEstimates.V n → _root_.ReciprocityTheory.L2DbarEstimates.V m}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) :
    AnalyticOnNhd ℂ φ U := by
  have hj : ∀ j : Fin m, AnalyticOnNhd ℂ (fun x => EuclideanSpace.proj j (φ x)) U := fun j =>
    _root_.ReciprocityTheory.MultiplicativeHeights.analyticOnNhd_V_of_differentiableOn hU ((EuclideanSpace.proj j : _root_.ReciprocityTheory.L2DbarEstimates.V m →L[ℂ] ℂ).differentiable.comp_differentiableOn hφ)
  have h := (analyticOnNhd_pi_iff (𝕜 := ℂ)).mpr hj
  intro x hx
  have := ((EuclideanSpace.equiv (Fin m) ℂ).symm.toContinuousLinearMap.analyticAt _).comp (h x hx)
  convert this using 1
  funext y
  rfl

open Set Filter Topology in
open scoped ComplexConjugate ContDiff in
set_option autoImplicit false in
variable {n m : ℕ} in
private theorem dbarAt_add_of_differentiableAt {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    {F G : _root_.ReciprocityTheory.L2DbarEstimates.V n → _root_.GlobalTheory.CxForm.Alt n}
    (hF : ∀ S, DifferentiableAt ℝ (fun x => (_root_.GlobalTheory.CxForm.bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (_root_.GlobalTheory.CxForm.bas n).repr (G x) S) v) :
    _root_.GlobalTheory.CxForm.dbarAt (fun x => F x + G x) v =
      _root_.GlobalTheory.CxForm.dbarAt F v + _root_.GlobalTheory.CxForm.dbarAt G v := by
  unfold _root_.GlobalTheory.CxForm.dbarAt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_add]
  congr 1
  apply (_root_.GlobalTheory.CxForm.bas n).repr.injective
  ext S
  simp only [map_add, Finsupp.add_apply, _root_.GlobalTheory.CxForm.FormMul.repr_coefwise]
  rw [_root_.GlobalTheory.dbar_add (hF S) (hG S), ContinuousLinearMap.add_apply]

open Set Filter Topology in
open scoped ComplexConjugate ContDiff in
set_option autoImplicit false in
variable {n m : ℕ} in

theorem _root_.GlobalTheory.CxForm.PullClosed.diff_and_closed {φ : _root_.ReciprocityTheory.L2DbarEstimates.V n → _root_.ReciprocityTheory.L2DbarEstimates.V m} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hφ : ContDiffAt ℂ 2 φ v) (θ : _root_.GlobalTheory.CxForm.Alt m) :
    (∀ S, DifferentiableAt ℝ (fun x => (_root_.GlobalTheory.CxForm.bas n).repr
        (_root_.GlobalTheory.CxForm.pull (fderiv ℂ φ x) θ) S) v) ∧
      _root_.GlobalTheory.CxForm.dbarAt (fun x => _root_.GlobalTheory.CxForm.pull (fderiv ℂ φ x) θ) v = 0 := by
  classical
  have hd : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm : IsSymmSndFDerivAt ℂ φ v :=
    hφ.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  set D := fderiv ℂ (fderiv ℂ φ) v with hDdef
  have hD : HasFDerivAt (fderiv ℂ φ) D v := hd.hasFDerivAt

  let Λ : Fin m → Fin n → (_root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V m) →L[ℂ] ℂ := fun a b =>
    (EuclideanSpace.proj a : _root_.ReciprocityTheory.L2DbarEstimates.V m →L[ℂ] ℂ).comp
      (ContinuousLinearMap.apply ℂ (_root_.ReciprocityTheory.L2DbarEstimates.V m) (_root_.GlobalTheory.GoodMetric.coordVec b))
  have hf : ∀ a b, HasFDerivAt (fun x => (fderiv ℂ φ x (_root_.GlobalTheory.GoodMetric.coordVec b)).ofLp a)
      ((Λ a b).comp D) v := fun a b => (Λ a b).hasFDerivAt.comp v hD
  have hfR : ∀ a b, DifferentiableAt ℝ
      (fun x => (fderiv ℂ φ x (_root_.GlobalTheory.GoodMetric.coordVec b)).ofLp a) v := fun a b =>
    (hf a b).differentiableAt.restrictScalars ℝ
  let P : _root_.GlobalTheory.CxForm.Alt m → Prop := fun θ =>
    (∀ S, DifferentiableAt ℝ (fun x => (_root_.GlobalTheory.CxForm.bas n).repr
        (_root_.GlobalTheory.CxForm.pull (fderiv ℂ φ x) θ) S) v) ∧
      _root_.GlobalTheory.CxForm.dbarAt
        (fun x => _root_.GlobalTheory.CxForm.pull (fderiv ℂ φ x) θ) v = 0
  have hconst : ∀ r : ℂ, P (algebraMap ℂ _ r) := by
    intro r
    simp only [P, AlgHom.commutes]
    refine ⟨fun S => differentiableAt_const _, ?_⟩
    have := _root_.GlobalTheory.CxForm.PullClosed.dbarAt_sum_smul (ι := Unit) (v := v)
      (f := fun _ _ => (1 : ℂ)) (fun _ => algebraMap ℂ (_root_.GlobalTheory.CxForm.Alt n) r)
      (fun _ => differentiableAt_const _)
    simpa [_root_.GlobalTheory.dbar_const] using this
  have hmul : ∀ θ₁ θ₂, P θ₁ → P θ₂ → P (θ₁ * θ₂) := by
    intro θ₁ θ₂ h₁ h₂
    simp only [P, map_mul]
    refine ⟨fun S => ?_, ?_⟩
    · have e : (fun x => (_root_.GlobalTheory.CxForm.bas n).repr
          (_root_.GlobalTheory.CxForm.pull (fderiv ℂ φ x) θ₁ *
            _root_.GlobalTheory.CxForm.pull (fderiv ℂ φ x) θ₂) S) = _ :=
        funext fun x => _root_.GlobalTheory.CxForm.FormMul.repr_mul _ _ S
      rw [e]
      exact DifferentiableAt.fun_sum fun p _ => ((h₁.1 p.1).mul (h₂.1 p.2)).mul_const _
    · obtain ⟨y, hy⟩ := _root_.GlobalTheory.CxForm.FormMul.dbarAt_mul h₁.1 h₂.1
      rw [hy, h₁.2, h₂.2]
      simp
  have hadd : ∀ θ₁ θ₂, P θ₁ → P θ₂ → P (θ₁ + θ₂) := by
    intro θ₁ θ₂ h₁ h₂
    simp only [P, map_add]
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Finsupp.add_apply]
      exact (h₁.1 S).add (h₂.1 S)
    · rw [dbarAt_add_of_differentiableAt h₁.1 h₂.1, h₁.2, h₂.2, add_zero]
  have hsmul : ∀ (c : ℂ) θ, P θ → P (c • θ) := by
    intro c θ h
    rw [Algebra.smul_def]
    exact hmul _ _ (hconst c) h
  have hsum : ∀ (w : Fin m → _root_.GlobalTheory.CxForm.Alt m) (c : Fin m → ℂ), (∀ b, P (w b)) →
      P (∑ b, c b • w b) := by
    intro w c h
    refine Finset.sum_induction _ P (fun x y hx hy => hadd x y hx hy) ?_
      (fun b _ => hsmul _ _ (h b))
    simpa using hconst 0
  have hdz : ∀ a : Fin m, P (_root_.GlobalTheory.CxForm.dz a) := by
    intro a
    have hg : ∀ L : _root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V m, _root_.GlobalTheory.CxForm.pull L
        (_root_.GlobalTheory.CxForm.dz a) =
        ∑ b, (L (_root_.GlobalTheory.GoodMetric.coordVec b)).ofLp a • _root_.GlobalTheory.CxForm.dz b :=
      fun L => (_root_.GlobalTheory.CxForm.pull_dz L a).1
    simp only [P, hg]
    refine ⟨fun S => ?_, ?_⟩
    · rw [_root_.GlobalTheory.CxForm.PullClosed.repr_sum_smul]
      exact DifferentiableAt.fun_sum fun b _ => (hfR a b).mul_const _
    · rw [_root_.GlobalTheory.CxForm.PullClosed.dbarAt_sum_smul _ (fun b => hfR a b)]
      simp [_root_.GlobalTheory.dbar_eq_zero (hf a _).differentiableAt]
  have hdzb : ∀ a : Fin m, P (_root_.GlobalTheory.CxForm.dzb a) := by
    intro a
    have hg : ∀ L : _root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V m, _root_.GlobalTheory.CxForm.pull L
        (_root_.GlobalTheory.CxForm.dzb a) =
        ∑ b, conj ((L (_root_.GlobalTheory.GoodMetric.coordVec b)).ofLp a) • _root_.GlobalTheory.CxForm.dzb b :=
      fun L => (_root_.GlobalTheory.CxForm.pull_dz L a).2
    have hgR : ∀ b, DifferentiableAt ℝ
        (fun x => conj ((fderiv ℂ φ x (_root_.GlobalTheory.GoodMetric.coordVec b)).ofLp a)) v := fun b =>
      (Complex.conjCLE.differentiableAt).comp v (hfR a b)
    simp only [P, hg]
    refine ⟨fun S => ?_, ?_⟩
    · rw [_root_.GlobalTheory.CxForm.PullClosed.repr_sum_smul]
      exact DifferentiableAt.fun_sum fun b _ => (hgR b).mul_const _
    · rw [_root_.GlobalTheory.CxForm.PullClosed.dbarAt_sum_smul _ hgR]
      apply _root_.GlobalTheory.CxForm.PullClosed.sum_symm_dzb
      intro c b
      rw [_root_.GlobalTheory.dbar_conj, _root_.GlobalTheory.dbar_conj,
        _root_.GlobalTheory.del_eq_fderiv (hf a b).differentiableAt,
        _root_.GlobalTheory.del_eq_fderiv (hf a c).differentiableAt,
        (hf a b).fderiv, (hf a c).fderiv]
      simp only [ContinuousLinearMap.comp_apply]
      show conj ((D (_root_.GlobalTheory.GoodMetric.coordVec c) (_root_.GlobalTheory.GoodMetric.coordVec b)).ofLp a) =
        conj ((D (_root_.GlobalTheory.GoodMetric.coordVec b) (_root_.GlobalTheory.GoodMetric.coordVec c)).ofLp a)
      rw [hsymm]
  have hι : ∀ x, P (ExteriorAlgebra.ι ℂ x) := by
    intro x
    have hx : ExteriorAlgebra.ι ℂ x = ∑ a, x (Sum.inl a) • _root_.GlobalTheory.CxForm.dz a +
        ∑ a, x (Sum.inr a) • _root_.GlobalTheory.CxForm.dzb a := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      rw [map_sum, Fintype.sum_sum_type]
      congr 1 <;> refine Finset.sum_congr rfl fun a _ => ?_ <;>
        [unfold _root_.GlobalTheory.CxForm.dz; unfold _root_.GlobalTheory.CxForm.dzb] <;>
        (rw [← map_smul]; congr 1; ext j; simp [Pi.single_apply])
    rw [hx]
    exact hadd _ _ (hsum _ _ hdz) (hsum _ _ hdzb)
  exact ExteriorAlgebra.induction hconst hι hmul hadd θ

open Set Filter Topology in
open scoped ComplexConjugate ContDiff in
set_option autoImplicit false in
variable {n m : ℕ} in

theorem _root_.GlobalTheory.CxForm.PullClosed.dbarAt_pull_fderiv : ∀ {n m : ℕ}
    {φ : _root_.ReciprocityTheory.L2DbarEstimates.V n → _root_.ReciprocityTheory.L2DbarEstimates.V m} {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)}, IsOpen U → DifferentiableOn ℂ φ U →
    ∀ {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}, v ∈ U → ∀ (θ : _root_.GlobalTheory.CxForm.Alt m),
      _root_.GlobalTheory.CxForm.dbarAt (fun x => _root_.GlobalTheory.CxForm.pull (fderiv ℂ φ x) θ) v = 0 := by
  intro n m φ U hU hφ v hv θ
  exact (_root_.GlobalTheory.CxForm.PullClosed.diff_and_closed
    ((_root_.GlobalTheory.CxForm.PullClosed.analyticOnNhd_of_holo hU hφ v hv).contDiffAt) θ).2

end GlobalTheory.CxForm.PullClosed
