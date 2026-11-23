import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFiniteStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.ConjDesc

noncomputable section

theorem smul_of_X {F : Type} [Field F] {M N : Type} [AddCommGroup M] [Module F M] [Module F[X] M]
    [IsScalarTower F F[X] M] [AddCommGroup N] [Module F N] [Module F[X] N] [IsScalarTower F F[X] N]
    (e : M ≃ₗ[F] N) (h : ∀ m, e ((X : F[X]) • m) = (X : F[X]) • e m) (p : F[X]) (m : M) :
    e (p • m) = p • e m := by
  revert m
  induction p using Polynomial.induction_on with
  | C a =>
    intro m
    rw [← Polynomial.algebraMap_eq, algebraMap_smul, algebraMap_smul]
    exact e.map_smul a m
  | add p q hp hq =>
    intro m
    rw [add_smul, add_smul, map_add, hp, hq]
  | monomial k a ih =>
    intro m
    rw [pow_succ, ← mul_assoc, mul_smul (C a * X ^ k) X m, ih, h, ← mul_smul]

def equivOfX {F : Type} [Field F] {M N : Type} [AddCommGroup M] [Module F M] [Module F[X] M]
    [IsScalarTower F F[X] M] [AddCommGroup N] [Module F N] [Module F[X] N] [IsScalarTower F F[X] N]
    (e : M ≃ₗ[F] N) (h : ∀ m, e ((X : F[X]) • m) = (X : F[X]) • e m) : M ≃ₗ[F[X]] N :=
  { e with
    map_smul' := fun p m => smul_of_X e h p m }

def swapE (F : Type) [Field F] (a b : ℕ) : (Fin a → Fin b → F) ≃ₗ[F] (Fin b → Fin a → F) :=
  { Equiv.piComm (fun (_ : Fin a) (_ : Fin b) => F) with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

def coordE {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ) :
    (Fin n → F') ≃ₗ[F] (Fin l → Fin n → F) :=
  (LinearEquiv.piCongrRight fun _ : Fin n => b.equivFun).trans (swapE F n l)

theorem coordE_apply {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ)
    (v : Fin n → F') (k : Fin l) (i : Fin n) : coordE b n v k i = b.equivFun (v i) k := rfl

theorem coordE_mulVec {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ)
    (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F') :
    coordE b n (Matrix.mulVec (A.map (algebraMap F F')) v) = fun k => Matrix.mulVec A (coordE b n v k) := by
  funext k i
  rw [coordE_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, ← Algebra.smul_def, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordE_apply]

end

end GlobalTheory.Shin.ConjDesc

namespace GlobalTheory.Shin

open ConjDesc in

theorem isConj_of_isConj_incl : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (n : ℕ)
    (γ γ' : GL (Fin n) F), IsConj (incl F F' n γ) (incl F F' n γ') → IsConj γ γ' := by
  intro F F' _ _ _ _ n γ γ' hc
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have hcA : (c : Matrix (Fin n) (Fin n) F') * ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) =
      ((γ' : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) * (c : Matrix (Fin n) (Fin n) F') := by
    have h2 : c * incl F F' n γ = incl F F' n γ' * c := by rw [← hc]; group
    exact congrArg (fun x : GL (Fin n) F' => (x : Matrix (Fin n) (Fin n) F')) h2
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : FiniteDimensional F F' := inferInstance
  have hl : 0 < Module.finrank F F' := Module.finrank_pos
  let b := Module.finBasis F F'
  let f := Matrix.toLin' (γ : Matrix (Fin n) (Fin n) F)
  let g := Matrix.toLin' (γ' : Matrix (Fin n) (Fin n) F)
  let Fc : (Fin n → F') ≃ₗ[F] (Fin n → F') :=
    (LinearEquiv.ofLinear (Matrix.toLin' (c : Matrix (Fin n) (Fin n) F'))
      (Matrix.toLin' ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F'))
      (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])).restrictScalars F
  have hFc : ∀ w, Fc w = Matrix.mulVec (c : Matrix (Fin n) (Fin n) F') w := fun w => rfl
  let core : (Fin (Module.finrank F F') → Fin n → F) ≃ₗ[F] (Fin (Module.finrank F F') → Fin n → F) :=
    (coordE b n).symm.trans (Fc.trans (coordE b n))
  have hcore : ∀ x, core (fun k => f (x k)) = fun k => g (core x k) := by
    intro x
    obtain ⟨v, rfl⟩ := (coordE b n).surjective x
    have h1 : (fun k => f (coordE b n v k)) =
        coordE b n (Matrix.mulVec ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) v) := by
      rw [coordE_mulVec]; rfl
    rw [h1]
    show coordE b n (Fc ((coordE b n).symm (coordE b n
        (Matrix.mulVec ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) v)))) =
      fun k => g (coordE b n (Fc ((coordE b n).symm (coordE b n v))) k)
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hFc, hFc, Matrix.mulVec_mulVec, hcA,
      ← Matrix.mulVec_mulVec, coordE_mulVec]
    rfl
  let Θ : (Fin (Module.finrank F F') → Module.AEval' f) ≃ₗ[F] (Fin (Module.finrank F F') → Module.AEval' g) :=
    (LinearEquiv.piCongrRight fun _ => (Module.AEval'.of f).symm).trans
      (core.trans (LinearEquiv.piCongrRight fun _ => Module.AEval'.of g))
  have hΘ : ∀ x, Θ ((X : F[X]) • x) = (X : F[X]) • Θ x := by
    intro x
    have h3 : (fun k => (Module.AEval'.of f).symm (((X : F[X]) • x) k)) =
        fun k => f ((Module.AEval'.of f).symm (x k)) :=
      funext fun k => Module.AEval'.of_symm_X_smul f (x k)
    funext k
    show Module.AEval'.of g (core (fun k => (Module.AEval'.of f).symm (((X : F[X]) • x) k)) k) =
      (X : F[X]) • Module.AEval'.of g (core (fun k => (Module.AEval'.of f).symm (x k)) k)
    rw [h3, hcore, Module.AEval'.X_smul_of]
  haveI : Finite (Module.AEval' f) := Finite.of_equiv _ (Module.AEval'.of f).toEquiv
  haveI : Finite (Module.AEval' g) := Finite.of_equiv _ (Module.AEval'.of g).toEquiv
  obtain ⟨ψ⟩ := GlobalTheory.T.nonempty_linearEquiv_of_pi_fin_pow_finite F[X] (Module.AEval' f) (Module.AEval' g) (Module.finrank F F') hl
    ⟨equivOfX Θ hΘ⟩
  let e : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    (Module.AEval'.of f).trans ((ψ.restrictScalars F).trans (Module.AEval'.of g).symm)
  have he : ∀ v, e (f v) = g (e v) := by
    intro v
    have h1 : Module.AEval'.of f (f v) = (X : F[X]) • Module.AEval'.of f v :=
      (Module.AEval'.X_smul_of f v).symm
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, h1, map_smul]
    exact Module.AEval'.of_symm_X_smul g _
  let P : GL (Fin n) F := ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine isConj_iff.mpr ⟨P, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  have h4 : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap := LinearMap.ext he
  have h5 := congrArg LinearMap.toMatrix' h4
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp] at h5
  simpa [P, f, g, LinearMap.toMatrix'_toLin'] using h5

end GlobalTheory.Shin
