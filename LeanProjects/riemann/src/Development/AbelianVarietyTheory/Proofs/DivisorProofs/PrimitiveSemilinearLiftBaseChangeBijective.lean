import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionCartierDualTangentBijectiveStatement

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDiv

section PrimBaseChange

variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A]
  [Module.Projective R A] [IsCocomm R A] [CommRing R'] [Algebra R R']

theorem counit_comp_cartierBaseChange :
    (counitAlgHom R' (CartierDual R' (R' ⊗[R] A))).comp
        ((CartierDual.baseChange R R' A).toAlgEquiv : R' ⊗[R] CartierDual R A →ₐ[R'] _) =
      AugCot.baseChangeAug R' (counitAlgHom R (CartierDual R A)) := by
  refine AlgHom.ext fun x => ?_
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r φ =>
    simp [Algebra.TensorProduct.one_def, Algebra.smul_def, mul_comm]

def cotBaseChange :
    Cot R' (CartierDual R' (R' ⊗[R] A)) ≃ₗ[R'] R' ⊗[R] Cot R (CartierDual R A) :=
  ((AugCot.baseChangeEquiv R' (counitAlgHom R (CartierDual R A))).trans
    (AugCot.congr (CartierDual.baseChange R R' A).toAlgEquiv
      (counit_comp_cartierBaseChange R'))).symm

theorem cotBaseChange_d (φ : CartierDual R A) :
    cotBaseChange R' (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) =
      (1 : R') ⊗ₜ dUnit R φ := by
  rw [cotBaseChange, LinearEquiv.symm_apply_eq, LinearEquiv.trans_apply,
    AugCot.baseChangeEquiv_tmul_d, one_smul, AugCot.congr_d]
  rfl

theorem cotBaseChange_hom_ext {N : Type} [AddCommGroup N] [Module R' N]
    {f g : Cot R' (CartierDual R' (R' ⊗[R] A)) →ₗ[R'] N}
    (h : ∀ φ : CartierDual R A, f (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) =
      g (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ)))) : f = g := by
  refine AugCot.hom_ext fun ψ => ?_
  obtain ⟨x, rfl⟩ := EquivLike.surjective (CartierDual.baseChange R R' A) ψ
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r φ =>
    have e : r ⊗ₜ[R] φ = r • ((1 : R') ⊗ₜ[R] φ) := by simp [smul_tmul']
    rw [e, map_smul, map_smul, map_smul, map_smul]
    exact congrArg (r • ·) (h φ)

end PrimBaseChange

theorem liftSemi_prim_toBaseChange_bijective {R A : Type} (R' : Type) [CommRing R] [CommRing A]
    [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] [CommRing R']
    [Algebra R R'] (hC : Module.Projective R (Cot R (CartierDual R A))) :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  let u := (CartierDual.toDual R (Cot R (CartierDual R A))).symm.toLinearMap ∘ₗ primTangent R A
  have hu : Function.Bijective u :=
    (CartierDual.toDual R _).symm.bijective.comp (GlobalTheory.T.additiveFunctionCartierDualTangent_bijective (R := R) (A := A))
  have key : ⇑(primTangent R' (R' ⊗[R] A)) ∘ ⇑(liftSemi (toBaseChange R R' A).prim) =
      ⇑(CartierDual.toDual R' _) ∘
        ⇑(CartierDual.transpose (cotBaseChange (R := R) (A := A) R').toLinearMap) ∘
        ⇑(CartierDual.baseChangeLinear R R' (Cot R (CartierDual R A))) ∘
        ⇑(LinearMap.lTensor R' u) := by
    funext x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
    | tmul r b =>
      refine cotBaseChange_hom_ext R' fun φ => ?_
      have h1 : primTangent R' (R' ⊗[R] A) (liftSemi (toBaseChange R R' A).prim (r ⊗ₜ b))
          (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) = φ b.1 • r := by
        rw [liftSemi_tmul, map_smul, LinearMap.smul_apply, primTangent_d, SemiBialgHom.prim_val,
          toBaseChange_apply, CartierDual.baseChange_tmul_tmul, smul_comm, mul_one, smul_eq_mul,
          mul_one]
      refine h1.trans (Eq.symm ?_)
      change CartierDual.baseChangeLinear R R' (Cot R (CartierDual R A)) (r ⊗ₜ u b)
        (cotBaseChange R' (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ)))) = _
      rw [cotBaseChange_d, CartierDual.baseChangeLinear_tmul_tmul, mul_one]
      exact congrArg (· • r) (primTangent_d b φ)
  refine (Function.Bijective.of_comp_iff' (GlobalTheory.T.additiveFunctionCartierDualTangent_bijective (R := R') (A := R' ⊗[R] A)) _).1 ?_
  rw [key]
  exact (CartierDual.toDual R' _).bijective.comp <|
    (CartierDual.transpose_bijective (cotBaseChange R').bijective).comp <|
    (CartierDual.baseChangeLinear_bijective R').comp
      (LinearEquiv.lTensor R' (LinearEquiv.ofBijective u hu)).bijective

end PDiv

end GlobalTheory
