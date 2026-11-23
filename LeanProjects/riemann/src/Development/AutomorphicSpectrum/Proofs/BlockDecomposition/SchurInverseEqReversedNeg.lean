import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyVariationInequality
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.SchurDual

open GroundTheory.Automorphic.Spherical

variable {n : ℕ}

noncomputable def negHom (n : ℕ) : LaurentRing n →ₐ[ℂ] LaurentRing n :=
  AddMonoidAlgebra.lift ℂ (LaurentRing n) (Fin n → ℤ)
    { toFun := fun l => monomial (-(Multiplicative.toAdd l))
      map_one' := by
        simp only [toAdd_one, neg_zero]
        rfl
      map_mul' := fun a b => by
        rw [toAdd_mul, neg_add, monomial_add] }

theorem negHom_monomial (μ : Fin n → ℤ) : negHom n (monomial μ) = monomial (-μ) := by
  rw [negHom, AddMonoidAlgebra.lift_single, one_smul]
  rfl

theorem monomialChar_inv (l : Fin n → ℤ) (z : Fin n → ℂˣ) :
    monomialChar l (fun i => (z i)⁻¹) = monomialChar (-l) z := by
  simp only [monomialChar_apply, Pi.neg_apply, _root_.inv_zpow, _root_.zpow_neg]

theorem evalAt_inv (z : Fin n → ℂˣ) (p : LaurentRing n) :
    evalAt (fun i => (z i)⁻¹) p = evalAt z (negHom n p) := by
  have h : evalAt (fun i => (z i)⁻¹) = (evalAt z).comp (negHom n) := by
    refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
    rw [AlgHom.comp_apply, negHom_monomial, evalAt_single, evalAt_single, monomialChar_inv]
  rw [h, AlgHom.comp_apply]

theorem negHom_alternant (μ : Fin n → ℤ) : negHom n (alternant μ) = alternant (-μ) := by
  simp only [alternant, antisymm_apply, map_sum, Units.smul_def, map_zsmul, permAct_monomial,
    negHom_monomial]
  rfl

theorem alternant_comp_rev (μ : Fin n → ℤ) :
    alternant (μ ∘ Fin.rev) = Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) • alternant μ := by
  have h := antisymm_permAct (Fin.revPerm : Equiv.Perm (Fin n)) (monomial μ)
  rw [permAct_monomial] at h
  exact h

theorem neg_staircase_comp_rev :
    (-(staircase n)) ∘ Fin.rev = staircase n + fun _ => (1 - (n : ℤ)) := by
  funext i
  have hi := i.isLt
  simp only [Function.comp_apply, Pi.neg_apply, Pi.add_apply, staircase, Fin.val_rev]
  omega

theorem neg_add_staircase_comp_rev (l : Fin n → ℤ) :
    (-(l + staircase n)) ∘ Fin.rev =
      ((fun i => -l (Fin.rev i)) + staircase n) + fun _ => (1 - (n : ℤ)) := by
  funext i
  have hi := i.isLt
  simp only [Function.comp_apply, Pi.neg_apply, Pi.add_apply, staircase, Fin.val_rev]
  omega

theorem negHom_schur (l : Fin n → ℤ) :
    negHom n (schur l) = schur (fun i => -l (Fin.rev i)) := by
  have h1 : alternant (-(staircase n)) * negHom n (schur l) = alternant (-(l + staircase n)) := by
    rw [← negHom_alternant, ← negHom_alternant, ← map_mul, alternant_mul_schur]
  have h2 := congrArg (fun x => Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) • x) h1
  simp only [← smul_mul_assoc, ← alternant_comp_rev, neg_staircase_comp_rev,
    neg_add_staircase_comp_rev, alternant_add_const] at h2
  rw [← alternant_mul_schur, mul_assoc] at h2
  have hM : (monomial (fun _ => (1 - (n : ℤ))) : LaurentRing n) ≠ 0 := by
    intro h
    have h3 := congrArg (evalAt (fun _ : Fin n => (1 : ℂˣ))) h
    simp [evalAt_single, monomialChar_apply] at h3
  exact mul_left_cancel₀ alternant_staircase_ne_zero (mul_left_cancel₀ hM h2)

theorem evalAt_inv_schur (n : ℕ) (z : Fin n → ℂˣ) (l : Fin n → ℤ) :
    evalAt (fun i => (z i)⁻¹) (schur l) = evalAt z (schur (fun i => -l (Fin.rev i))) := by
  rw [evalAt_inv, negHom_schur]

end GlobalTheory.CompanionTheory.SchurDual
