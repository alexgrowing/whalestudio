import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer

set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.TranslFree

variable {R A B : Type} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing B] [Bialgebra R B]
  (f : A →ₐc[R] B)

theorem coassoc (a : A) :
    TensorProduct.assoc R A B B (((f : A →ₗ[R] B).lTensor A ∘ₗ comul).rTensor B
      ((f : A →ₗ[R] B).lTensor A (comul a))) =
      (comul (R := R) (A := B)).lTensor A ((f : A →ₗ[R] B).lTensor A (comul a)) := by
  let F : A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] (B ⊗[R] B) :=
    (TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B)).lTensor A
  have h1 : ∀ w : A ⊗[R] A,
      TensorProduct.assoc R A B B (((f : A →ₗ[R] B).lTensor A ∘ₗ comul).rTensor B
        ((f : A →ₗ[R] B).lTensor A w)) =
      F (TensorProduct.assoc R A A A ((comul (R := R)).rTensor A w)) := by
    intro w
    induction w with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply]
      generalize comul (R := R) a = w
      induction w with
      | zero => simp
      | add u v hu hv => simp only [map_add, add_tmul, hu, hv]
      | tmul u v => simp [F]
  have h2 : ∀ w : A ⊗[R] A,
      (comul (R := R) (A := B)).lTensor A ((f : A →ₗ[R] B).lTensor A w) =
      F ((comul (R := R)).lTensor A w) := by
    intro w
    induction w with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, F]
      congr 1
      exact (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) b).symm
  rw [h1, h2, Coalgebra.coassoc_apply]

theorem counit_law (a : A) :
    TensorProduct.rid R A ((counit (R := R) (A := B)).lTensor A
      ((f : A →ₗ[R] B).lTensor A (comul a))) = a := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, CoalgHomClass.counit_comp,
    Coalgebra.lTensor_counit_comul]
  simp

end GlobalTheory.TranslFree

theorem GlobalTheory.PDivGroup.transl_free :
    ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ), (∀ a, TensorProduct.assoc R (G.A (n + 1)) (G.A 1) (G.A 1) ((G.transl n).toLinearMap.rTensor (G.A 1) (G.transl n a)) = (Coalgebra.comul (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) ∧ (∀ a, TensorProduct.rid R (G.A (n + 1)) ((Coalgebra.counit (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) = a) ∧ Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1) (G.transl n)) := by
  intro p R _ G n
  refine ⟨fun a => GlobalTheory.TranslFree.coassoc (G.resOne n) a,
    fun a => GlobalTheory.TranslFree.counit_law (G.resOne n) a, fun z => ?_⟩
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (G.A (n + 1))
    (g := (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1)) (G.resOne_surjective n) z
  obtain ⟨x, rfl⟩ := GlobalTheory.HopfQuot.shear_surjective (R := R) y
  refine ⟨x, ?_⟩
  induction x with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul u v =>
    rw [Algebra.TensorProduct.productMap_apply_tmul, GlobalTheory.HopfQuot.shear_tmul, transl_apply]
    generalize comul (R := R) v = w
    induction w with
    | zero => simp
    | add s t hs ht => simp only [map_add, mul_add, smul_add, hs, ht]
    | tmul s t => simp [TensorProduct.smul_tmul']
