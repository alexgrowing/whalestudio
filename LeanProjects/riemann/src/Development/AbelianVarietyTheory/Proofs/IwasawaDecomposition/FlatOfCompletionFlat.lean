import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

open IsLocalRing TensorProduct

namespace GlobalTheory.CompletionFlat

theorem flat_of_finite_of_flat_comp : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing R] (ψ : AdicCompletion (maximalIdeal A) A →+* R), ψ.Finite →
    (ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A))).Flat → ψ.Flat := by
  intro A R _ _ _ _ ψ hfin hflat
  let B := AdicCompletion (maximalIdeal A) A
  letI : Algebra B R := ψ.toAlgebra
  letI : Algebra A R := (ψ.comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : Module.Finite B R := hfin
  haveI : Module.Flat A R := hflat
  haveI : Module.FinitePresentation B R := Module.finitePresentation_of_finite B R
  suffices H : Function.Injective ((maximalIdeal B).subtype.rTensor R) by
    haveI := Module.free_of_maximalIdeal_rTensor_injective H
    exact (inferInstance : Module.Flat B R)
  let mA := maximalIdeal A
  let mB := maximalIdeal B
  have hmap : mB = mA.map (algebraMap A B) := AdicCompletion.maximalIdeal_eq_map
  have hmem : ∀ a ∈ mA, algebraMap A B a ∈ mB := fun a ha => hmap ▸ Ideal.mem_map_of_mem _ ha
  let j : mA →+ mB :=
    { toFun := fun a => ⟨algebraMap A B a, hmem a a.2⟩
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  let F : mA →+ R →+ (mB ⊗[B] R) :=
    { toFun := fun a => (TensorProduct.mk B mB R (j a)).toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [add_tmul] }
  have hF : ∀ (r : A) (a : mA) (n : R), F (r • a) n = F a (r • n) := by
    intro r a n
    have h1 : j (r • a) = algebraMap A B r • j a := Subtype.ext (by simp [j, Algebra.smul_def])
    show TensorProduct.mk B mB R (j (r • a)) n = TensorProduct.mk B mB R (j a) (r • n)
    rw [h1, TensorProduct.mk_apply, TensorProduct.mk_apply, TensorProduct.smul_tmul, algebraMap_smul]
  let φ : mA ⊗[A] R →+ mB ⊗[B] R := TensorProduct.liftAddHom F hF
  have hφ : ∀ (a : mA) (n : R), φ (a ⊗ₜ n) = j a ⊗ₜ n := fun a n => TensorProduct.liftAddHom_tmul _ _ _ _
  have key : ∀ y : mA ⊗[A] R, TensorProduct.lid B R (mB.subtype.rTensor R (φ y)) =
      TensorProduct.lid A R (mA.subtype.rTensor R y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a n => rw [hφ]; simp [j, algebraMap_smul]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]
  have gen : ∀ (b : B) (hb : b ∈ mB) (n : R), ∃ y, φ y = (⟨b, hb⟩ : mB) ⊗ₜ n := by
    intro b hb
    have hb' : b ∈ Ideal.map (algebraMap A B) mA := hmap ▸ hb
    refine Submodule.span_induction (p := fun b _ => ∀ hb : b ∈ mB, ∀ n : R,
      ∃ y, φ y = (⟨b, hb⟩ : mB) ⊗ₜ n) ?_ ?_ ?_ ?_ hb' hb
    · rintro x ⟨a, ha, rfl⟩ hx n
      exact ⟨(⟨a, ha⟩ : mA) ⊗ₜ n, by rw [hφ]; rfl⟩
    · intro hz n
      exact ⟨0, by rw [map_zero]; exact (zero_tmul mB n).symm⟩
    · intro x y hx hy ihx ihy hxy n
      obtain ⟨u, hu⟩ := ihx (hmap ▸ hx) n
      obtain ⟨v, hv⟩ := ihy (hmap ▸ hy) n
      refine ⟨u + v, ?_⟩
      rw [map_add, hu, hv, ← add_tmul]
      rfl
    · intro c x hx ihx hcx n
      obtain ⟨u, hu⟩ := ihx (hmap ▸ hx) (c • n)
      refine ⟨u, ?_⟩
      rw [hu, ← TensorProduct.smul_tmul]
      rfl
  have surj : ∀ x : mB ⊗[B] R, ∃ y, φ y = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul m n => exact gen m.1 m.2 n
    | add x z hx hz =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hz
      exact ⟨u + v, by rw [map_add, hu, hv]⟩
  have hinjA : Function.Injective (mA.subtype.rTensor R) :=
    Module.Flat.rTensor_preserves_injective_linearMap mA.subtype Subtype.val_injective
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := surj x
  have h1 : TensorProduct.lid A R (mA.subtype.rTensor R y) = 0 := by rw [← key, hx, map_zero]
  have h0 : mA.subtype.rTensor R y = 0 := (TensorProduct.lid A R).injective (by rw [h1, map_zero])
  have hy : y = 0 := hinjA (by rw [h0, map_zero])
  rw [hy, map_zero]

end GlobalTheory.CompletionFlat
