import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityHom
import GroundTheory.GlobalFields.ComplexMultiplication.AutCFixed

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IntermediateField
open scoped nonZeroDivisors

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {K : Type*} [Field K] [NumberField K]

theorem CMCurve.toEll_eq_of_curve_eq {E E' : CMCurve K} (h : E.curve = E'.curve) :
    E.toEll = E'.toEll :=
  (CMCurve.toEll_eq_iff E E').2 ⟨1, by rw [one_smul, h]⟩

def CMCurve.map (σ : ℂ ≃+* ℂ) (E : CMCurve K) : CMCurve K where
  curve := E.curve.map (σ : ℂ →+* ℂ)
  endIso := ⟨(endMapEquiv σ).symm.trans E.endIso.some⟩

omit [NumberField K] in
theorem CMCurve.map_curve (σ : ℂ ≃+* ℂ) (E : CMCurve K) :
    (E.map σ).curve = E.curve.map (σ : ℂ →+* ℂ) :=
  rfl

def ELL.map (σ : ℂ ≃+* ℂ) : ELL K → ELL K :=
  Quotient.lift (fun E : CMCurve K ↦ (E.map σ).toEll) fun E E' h ↦ by
    obtain ⟨C, hC⟩ := h
    rw [CMCurve.toEll_eq_iff]
    exact ⟨C.map (σ : ℂ →+* ℂ), by
      rw [CMCurve.map_curve, CMCurve.map_curve, map_variableChange, hC]⟩

theorem ELL.map_toEll (σ : ℂ ≃+* ℂ) (E : CMCurve K) : ELL.map σ E.toEll = (E.map σ).toEll :=
  rfl

theorem ELL.map_one (x : ELL K) : ELL.map 1 x = x := by
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  rw [ELL.map_toEll]
  apply CMCurve.toEll_eq_of_curve_eq
  rw [CMCurve.map_curve]
  exact WeierstrassCurve.map_id E.curve

theorem ELL.map_mul (σ τ : ℂ ≃+* ℂ) (x : ELL K) : ELL.map (σ * τ) x = ELL.map σ (ELL.map τ x) := by
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  rw [ELL.map_toEll, ELL.map_toEll, ELL.map_toEll]
  apply CMCurve.toEll_eq_of_curve_eq
  rw [CMCurve.map_curve, CMCurve.map_curve, CMCurve.map_curve, WeierstrassCurve.map_map]
  rfl

theorem j_congr {W W' : WeierstrassCurve ℂ} [W.IsElliptic] [W'.IsElliptic] (h : W = W') :
    W.j = W'.j := by
  subst h
  rfl

def ELL.j : ELL K → ℂ :=
  Quotient.lift (fun E : CMCurve K ↦ E.curve.j) fun E E' h ↦ by
    obtain ⟨C, hC⟩ := h
    show E.curve.j = E'.curve.j
    rw [← variableChange_j E.curve C]
    exact j_congr hC

omit [NumberField K] in
theorem ELL.j_toEll (E : CMCurve K) : ELL.j E.toEll = E.curve.j :=
  rfl

theorem ELL.j_injective : Function.Injective (ELL.j (K := K)) := by
  intro x y h
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  obtain ⟨E', rfl⟩ := ELL.exists_eq y
  rw [ELL.j_toEll, ELL.j_toEll] at h
  exact (CMCurve.toEll_eq_iff E E').2 (exists_variableChange_of_j_eq E.curve E'.curve h)

theorem ELL.j_map (σ : ℂ ≃+* ℂ) (x : ELL K) : ELL.j (ELL.map σ x) = σ (ELL.j x) := by
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  rw [ELL.map_toEll, ELL.j_toEll, ELL.j_toEll]
  exact map_j E.curve (σ : ℂ →+* ℂ)

section Quadratic

variable (hK : finrank ℚ K = 2) [IsTotallyComplex K]
include hK

theorem ELL.finite_range_conj (x : ELL K) :
    (Set.range fun σ : ℂ ≃+* ℂ ↦ σ (ELL.j x)).Finite := by
  have := finite_ell hK
  refine (Set.finite_range (ELL.j (K := K))).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨ELL.map σ x, ELL.j_map σ x⟩

theorem ELL.isAlgebraic_j (x : ELL K) : IsAlgebraic ℚ (ELL.j x) :=
  Complex.isAlgebraic_of_finite_conjugates (ELL.finite_range_conj hK x)

end Quadratic

omit [NumberField K] in

theorem CMCurve.exists_model (E : CMCurve K) :
    ∃ (W : WeierstrassCurve ℚ⟮E.curve.j⟯) (_ : W.IsElliptic) (C : VariableChange ℂ),
      C • W.baseChange ℂ = E.curve := by
  classical
  set W := WeierstrassCurve.ofJ (⟨E.curve.j, mem_adjoin_simple_self ℚ _⟩ : ℚ⟮E.curve.j⟯)
  refine ⟨W, inferInstance, ?_⟩
  have hj : (W.baseChange ℂ).j = E.curve.j := by
    show (W.map (algebraMap ℚ⟮E.curve.j⟯ ℂ)).j = _
    rw [map_j, ofJ_j]
    rfl
  exact exists_variableChange_of_j_eq _ _ hj

end Elliptic
end GroundTheory.Global
