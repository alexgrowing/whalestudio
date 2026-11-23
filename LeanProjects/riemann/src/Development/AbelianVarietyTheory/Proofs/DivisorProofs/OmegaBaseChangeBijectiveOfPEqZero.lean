import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDiv

theorem liftSemi_toBaseChange_cot_bijective (R R' A : Type) [CommRing R] [CommRing R'] [Algebra R R']
    [CommRing A] [Bialgebra R A] : Function.Bijective (liftSemi (toBaseChange R R' A).cot) := by
  have heq : (counitAlgHom R' (R' ⊗[R] A)).comp
      ((AlgEquiv.refl : (R' ⊗[R] A) ≃ₐ[R'] (R' ⊗[R] A)) : (R' ⊗[R] A) →ₐ[R'] (R' ⊗[R] A)) =
      AugCot.baseChangeAug R' (counitAlgHom R A) := by
    apply Algebra.TensorProduct.ext'
    intro r a
    simp [AugCot.baseChangeAug_tmul, Algebra.smul_def, mul_comm]
  let E : R' ⊗[R] Cot R A ≃ₗ[R'] Cot R' (R' ⊗[R] A) :=
    (AugCot.baseChangeEquiv R' (counitAlgHom R A)).trans (AugCot.congr AlgEquiv.refl heq)
  have key : ∀ x, liftSemi (toBaseChange R R' A).cot x = E x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul r m =>
      obtain ⟨a, rfl⟩ := AugCot.d_surjective (counitAlgHom R A) m
      have h1 := SemiBialgHom.cot_d (toBaseChange R R' A) a
      simp only [liftSemi_tmul, E, LinearEquiv.trans_apply]
      rw [show AugCot.d (counitAlgHom R A) a = dUnit R a from rfl, h1, AugCot.baseChangeEquiv_tmul_d,
        map_smul, AugCot.congr_d]
      rfl
  have hfun : ⇑(liftSemi (toBaseChange R R' A).cot) = ⇑E := funext key
  rw [hfun]
  exact E.bijective

end PDiv

namespace PDivGroup

theorem omega_baseChange_bijective {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (R' : Type)
    [CommRing R'] [Algebra R R'] (hp : (p : R) = 0) :
    Function.Bijective (liftSemi (G.toBase R').omega) := by
  have hp' : (p : R') = 0 := by rw [← map_natCast (algebraMap R R'), hp, map_zero]
  have hL := G.omegaLevel_one_bijective hp
  have hL' := (G.baseChange R').omegaLevel_one_bijective hp'
  have hg := liftSemi_toBaseChange_cot_bijective R R' (G.A 1)
  let e : R' ⊗[R] G.omega ≃ₗ[R'] R' ⊗[R] Cot R (G.A 1) :=
    LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofBijective (G.omegaLevel 1) hL)
  have key : ∀ x, (G.baseChange R').omegaLevel 1 (liftSemi (G.toBase R').omega x) =
      liftSemi (toBaseChange R R' (G.A 1)).cot (e x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul r w =>
      simp only [liftSemi_tmul, map_smul, e, LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
      congr 1
  have hcomp : ⇑((G.baseChange R').omegaLevel 1) ∘ ⇑(liftSemi (G.toBase R').omega) =
      ⇑(liftSemi (toBaseChange R R' (G.A 1)).cot) ∘ ⇑e := funext key
  exact (Function.Bijective.of_comp_iff' hL' _).1 (hcomp ▸ hg.comp e.bijective)

end PDivGroup

end GlobalTheory
