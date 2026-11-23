import Mathlib

open TensorProduct KaehlerDifferential

namespace GlobalTheory.AuxiliaryLemmaFirst

theorem main : ∀ (R R' B C B' K : Type) [inst : CommRing R] [inst_1 : CommRing R'] [inst_2 : CommRing B] [inst_3 : CommRing C] [inst_4 : CommRing B'] [inst_5 : Field K] [inst_6 : Algebra R R'] [inst_7 : Algebra R B] [inst_8 : Algebra R C] [inst_9 : Algebra R' C] [inst_10 : Algebra B C] [inst_11 : IsScalarTower R R' C] [inst_12 : IsScalarTower R B C] [Algebra.IsPushout R R' B C] [inst_14 : Algebra C B'] [inst_15 : Algebra R' B'] [IsScalarTower R' C B'] [Algebra.FormallyEtale C B'] [inst_18 : Algebra B' K] [inst_19 : Algebra B K], (∀ (x : B), (Algebra.algebraMap B K : B → K) x = (Algebra.algebraMap B' K : B' → K) ((Algebra.algebraMap C B' : C → B') ((Algebra.algebraMap B C : B → C) x))) → ∃ (e : TensorProduct B K Ω[B⁄R] ≃ₗ[K] TensorProduct B' K Ω[B'⁄R']), ∀ (x : B), (e : TensorProduct B K Ω[B⁄R] → TensorProduct B' K Ω[B'⁄R']) ((1 : K) ⊗ₜ[B] (KaehlerDifferential.D R B : B → Ω[B⁄R]) x) = (1 : K) ⊗ₜ[B'] (KaehlerDifferential.D R' B' : B' → Ω[B'⁄R']) ((Algebra.algebraMap C B' : C → B') ((Algebra.algebraMap B C : B → C) x)) := by
  intro R R' B C B' K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx
  letI : Algebra C K := ((algebraMap B' K).comp (algebraMap C B')).toAlgebra
  haveI : IsScalarTower C B' K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B C K := IsScalarTower.of_algebraMap_eq (fun x => hx x)
  let e1 := (AlgebraTensorModule.cancelBaseChange B C K K Ω[B⁄R]).symm
  let e2 := AlgebraTensorModule.congr (LinearEquiv.refl K K) (tensorKaehlerEquiv R R' B C)
  let e3 := (AlgebraTensorModule.cancelBaseChange C B' K K Ω[C⁄R']).symm
  let e4 := AlgebraTensorModule.congr (LinearEquiv.refl K K) (tensorKaehlerEquivOfFormallyEtale R' C B')
  refine ⟨e1 ≪≫ₗ e2 ≪≫ₗ e3 ≪≫ₗ e4, fun x => ?_⟩
  simp [e1, e2, e3, e4]

end GlobalTheory.AuxiliaryLemmaFirst
