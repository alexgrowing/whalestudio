import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureOfIsArtinianRing
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.PiClosure

noncomputable def integralClosurePiEquiv (R : Type) [CommRing R] (ι : Type) [Finite ι]
    (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra R (E i)] :
    integralClosure R (∀ i, E i) ≃ₐ[R] ∀ i, integralClosure R (E i) :=
  AlgEquiv.ofBijective
    (AlgHom.pi fun i =>
      ((Pi.evalAlgHom R E i).comp (integralClosure R (∀ i, E i)).val).codRestrict
        (integralClosure R (E i)) fun x => x.2.map (Pi.evalAlgHom R E i))
    (by
      constructor
      · intro x y hxy
        apply Subtype.ext
        funext i
        exact congrArg Subtype.val (congrFun hxy i)
      · intro l
        refine ⟨⟨fun i => (l i).1,
          GlobalTheory.PurityProd.isIntegral_of_forall_apply (fun i => (l i).1) fun i => (l i).2⟩, ?_⟩
        funext i
        rfl)

theorem etale_integralClosure_pi : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (E : ι → Type) [∀ i, CommRing (E i)]
    [∀ i, Algebra R (E i)], (∀ i, Algebra.Etale R (integralClosure R (E i))) →
    Algebra.Etale R (integralClosure R (∀ i, E i)) := by
  intro R _ ι _ E _ _ h
  haveI : Algebra.Etale R (∀ i, integralClosure R (E i)) := inferInstance
  exact Algebra.Etale.of_equiv (integralClosurePiEquiv R ι E).symm

end GlobalTheory.PiClosure
