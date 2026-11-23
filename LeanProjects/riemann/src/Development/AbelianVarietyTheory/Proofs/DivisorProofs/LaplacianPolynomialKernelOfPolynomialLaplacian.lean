import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealBasisGlLieAlgebraSumSqElementaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsRestrictionSmoothRightDerivEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothFunAndRightDerivEqLeftInvariantVectorFieStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
noncomputable section

namespace GlobalTheory.HCA

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def glRho : glL E a →ₗ[ℝ] Module.End ℂ ((glH E a).smoothFuns (F := ℂ)) where
  toFun X := (glH E a).rightDerivEnd X
  map_add' X Y := by ext1 f; ext1; exact (glH E a).rightDeriv_add_left _ _ _
  map_smul' r X := by ext1 f; ext1; exact (glH E a).rightDeriv_smul_left r _ _

variable (E a) in

def glLap : Module.End ℂ ((glH E a).smoothFuns (F := ℂ)) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    ((glH E a).rightDerivEnd ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
      (glH E a).rightDerivEnd ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2)

theorem aeval_intertwine {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (Φ : M →ₗ[ℂ] N) (A : Module.End ℂ M) (B : Module.End ℂ N) (h : ∀ x, Φ (A x) = B (Φ x))
    (p : Polynomial ℂ) (x : M) : Φ (Polynomial.aeval A p x) = Polynomial.aeval B p (Φ x) := by
  have hp : ∀ n : ℕ, ∀ x, Φ ((A ^ n) x) = (B ^ n) (Φ x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add, LinearMap.add_apply, hp', hq']
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hp]

theorem contDiffOn_finsum {ι : Type*} (s : Finset ι) (g : ι → Lie E a → ℂ)
    (hg : ∀ i ∈ s, ContDiffOn ℝ ∞ (g i) (invSet E a)) : ContDiffOn ℝ ∞ (∑ i ∈ s, g i) (invSet E a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact contDiffOn_const (c := (0 : ℂ))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hg i (Finset.mem_insert_self _ _)).add (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem rightDeriv_glF {f : Lie E a → ℂ} (hf : ContDiffOn ℝ ∞ f (invSet E a)) (X : glL E a)
    (g : (glH E a).smoothFuns (F := ℂ)) (hg : g.1 = fun y : glG E a => f (toL y.1.val)) :
    ((glH E a).rightDerivEnd X g).1 = fun y : glG E a => vecF E a (toL X.1) f (toL y.1.val) := by
  rw [IsExpLieAlgebra.coe_rightDerivEnd, hg]
  exact ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).2 X).2

theorem glLap_glF {f : Lie E a → ℂ} (hf : ContDiffOn ℝ ∞ f (invSet E a))
    (g : (glH E a).smoothFuns (F := ℂ)) (hg : g.1 = fun y : glG E a => f (toL y.1.val)) :
    (glLap E a g).1 = (fun y : glG E a => lapF E a f (toL y.1.val)) ∧ ContDiffOn ℝ ∞ (lapF E a f) (invSet E a) := by
  have key : ∀ X : glL E a, ((glH E a).rightDerivEnd X ((glH E a).rightDerivEnd X g)).1 =
      fun y : glG E a => vecF E a (toL X.1) (vecF E a (toL X.1) f) (toL y.1.val) := fun X =>
    rightDeriv_glF ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).2 X).1 X _ (rightDeriv_glF hf X g hg)
  have hv : ∀ X : Lie E a, ContDiffOn ℝ ∞ (vecF E a X f) (invSet E a) := fun X =>
    ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).2 ⟨Matrix.of X, Submodule.mem_top⟩).1
  have hvv : ∀ X : Lie E a, ContDiffOn ℝ ∞ (vecF E a X (vecF E a X f)) (invSet E a) := fun X =>
    ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a _ (hv X)).2 ⟨Matrix.of X, Submodule.mem_top⟩).1
  refine ⟨?_, ?_⟩
  · simp only [glLap, LinearMap.sum_apply, LinearMap.add_apply, sq, Module.End.mul_apply,
      Submodule.coe_sum, Submodule.coe_add, key]
    funext y
    simp only [lapF, Finset.sum_apply, Pi.add_apply]
  · unfold lapF
    exact contDiffOn_finsum _ _ fun τ _ => contDiffOn_finsum _ _ fun i _ => contDiffOn_finsum _ _ fun j _ =>
      (hvv _).add (hvv _)

theorem glLap_pow_glF (k : ℕ) : ∀ {f : Lie E a → ℂ}, ContDiffOn ℝ ∞ f (invSet E a) →
    ∀ (g : (glH E a).smoothFuns (F := ℂ)), g.1 = (fun y : glG E a => f (toL y.1.val)) →
    ((glLap E a ^ k) g).1 = (fun y : glG E a => (lapF E a)^[k] f (toL y.1.val)) ∧
      ContDiffOn ℝ ∞ ((lapF E a)^[k] f) (invSet E a) := by
  induction k with
  | zero => intro f hf g hg; exact ⟨hg, hf⟩
  | succ k ih =>
    intro f hf g hg
    obtain ⟨h1, h2⟩ := glLap_glF hf g hg
    rw [pow_succ, Module.End.mul_apply, Function.iterate_succ_apply]
    exact ih h2 _ h1

theorem glLap_glRes (φ : Sm E a) (x : GA E a) :
    glLap E a ⟨glRes φ.1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a φ x).1⟩ = ⟨glRes (lapOp E a φ).1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a _ x).1⟩ := by
  have key : ∀ (i j : Fin a) (z : Cinf E) (ψ : Sm E a),
      (glH E a).rightDerivEnd ⟨Matrix.single i j z, Submodule.mem_top⟩ ⟨glRes ψ.1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a ψ x).1⟩ =
        ⟨glRes (lieS E a i j z ψ).1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a _ x).1⟩ := by
    intro i j z ψ
    apply Subtype.ext
    rw [IsExpLieAlgebra.coe_rightDerivEnd, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a ψ x).2, lieS_apply]
  apply Subtype.ext
  simp only [glLap, lapOp, LinearMap.sum_apply, LinearMap.add_apply, sq, Module.End.mul_apply,
    key, Submodule.coe_sum, Submodule.coe_add]
  funext y
  simp only [glRes, Finset.sum_apply, Pi.add_apply, Submodule.coe_sum, Submodule.coe_add]

theorem solG_of_polyLap : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ p : Polynomial ℂ, p ≠ 0 → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)) (P : Polynomial ℂ), P.Monic ∧ (∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) → (fun y : glG E a => f (toL y.1.val)) ∈ solG (glH E a) b P) ∧ ∀ φ : Sm E a, Polynomial.aeval (lapOp E a) p φ = 0 → ∀ x, glRes φ.1 x ∈ solG (glH E a) b P := by
  intro E _ _ _ a p hp
  obtain ⟨d, b, hb⟩ := GlobalTheory.T.exists_realBasis_glLieAlgebra_sum_sq_elementary E a
  have hΔ : (∑ i, (glH E a).rightDerivEnd (F := ℂ) (b i) * (glH E a).rightDerivEnd (F := ℂ) (b i)) = glLap E a := by
    rw [glLap]
    simp only [sq]
    exact hb _ (glRho E a)
  refine ⟨d, b, p * Polynomial.C p.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hp, ?_, ?_⟩
  · have hP : ∀ g, Polynomial.aeval (glLap E a) (p * Polynomial.C p.leadingCoeff⁻¹) g =
        p.leadingCoeff⁻¹ • Polynomial.aeval (glLap E a) p g := by
      intro g
      rw [Polynomial.aeval_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    intro f hf h0
    rw [mem_solG]
    refine ⟨(GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).1, ?_⟩
    rw [hΔ, hP]
    have hk : ∀ k : ℕ, ((glLap E a ^ k) ⟨_, (GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).1⟩).1 =
        (fun y : glG E a => (lapF E a)^[k] f (toL y.1.val)) := fun k => (glLap_pow_glF k hf _ rfl).1
    suffices h : Polynomial.aeval (glLap E a) p ⟨_, (GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).1⟩ = 0 by rw [h, smul_zero]
    apply Subtype.ext
    rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum]
    funext y
    simp only [Finset.sum_apply, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, hk, Submodule.coe_zero,
      Pi.zero_apply]
    have := h0 _ (val_mem_invSet y.1)
    simpa only [polyF, Finset.sum_apply, Pi.smul_apply] using this
  · intro φ hφ x
    rw [mem_solG]
    refine ⟨(GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a φ x).1, ?_⟩
    rw [hΔ, Polynomial.aeval_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    let Φ : Sm E a →ₗ[ℂ] (glH E a).smoothFuns (F := ℂ) :=
      { toFun := fun ψ => ⟨glRes ψ.1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a ψ x).1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have e := aeval_intertwine Φ (lapOp E a) (glLap E a) (fun ψ => (glLap_glRes ψ x).symm) p φ
    change p.leadingCoeff⁻¹ • Polynomial.aeval (glLap E a) p (Φ φ) = 0
    rw [← e, hφ, map_zero, smul_zero]

end GlobalTheory.HCA
