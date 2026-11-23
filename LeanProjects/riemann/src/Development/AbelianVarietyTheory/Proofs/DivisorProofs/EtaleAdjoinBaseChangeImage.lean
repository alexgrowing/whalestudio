import Mathlib
open TensorProduct

namespace GlobalTheory

theorem etale_adjoin_baseChange_image (R S B : Type) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] (A₀ : Subalgebra R S)
    (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.Etale A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀)
    (S' : Subalgebra R S) (h : A₀ ≤ S') :
    ∃ (_ : Algebra S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))))
      (_ : IsScalarTower R S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))),
      Algebra.Etale S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))) := by
  set C := Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))) with hC
  letI : Algebra A₀ S' := (Subalgebra.inclusion h).toRingHom.toAlgebra
  let ι : S' →ₐ[A₀] S :=
    { toRingHom := S'.val.toRingHom
      commutes' := fun _ => rfl }
  let Φ : S' ⊗[A₀] B₀ →ₐ[A₀] S ⊗[A₀] B₀ := Algebra.TensorProduct.map ι (AlgHom.id A₀ B₀)
  let Ψ : S' ⊗[A₀] B₀ →+* B := (e.symm : S ⊗[A₀] B₀ →+* B).comp Φ.toRingHom
  haveI : Module.Flat A₀ B₀ := inferInstance
  have hΦ : Function.Injective Φ := by
    have hl : (Φ.toLinearMap : S' ⊗[A₀] B₀ →ₗ[A₀] S ⊗[A₀] B₀) = LinearMap.rTensor B₀ ι.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      rfl
    have : Function.Injective (LinearMap.rTensor B₀ ι.toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b hab => Subtype.ext hab)
    rw [← hl] at this
    exact this
  have hΨ : Function.Injective Ψ := e.symm.injective.comp hΦ
  have htmul : ∀ (s : S') (b : B₀), Ψ (s ⊗ₜ b) = algebraMap S B s * e.symm (1 ⊗ₜ b) := by
    intro s b
    have : ((s : S) ⊗ₜ[A₀] b : S ⊗[A₀] B₀) = algebraMap S (S ⊗[A₀] B₀) s * (1 ⊗ₜ b) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    show e.symm ((s : S) ⊗ₜ[A₀] b) = _
    rw [this, map_mul, AlgEquiv.commutes]
  have h1 : e.symm ((1 : S) ⊗ₜ[A₀] (1 : B₀)) = 1 := by
    rw [← Algebra.TensorProduct.one_def, map_one]
  have hsub : ∀ x, Ψ x ∈ C := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      rw [htmul]
      exact C.mul_mem (Algebra.subset_adjoin (Or.inl ⟨s, s.2, rfl⟩))
        (Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => rw [map_add]; exact C.add_mem hx hy
  have hsurj : (C : Set B) ⊆ Set.range Ψ := by
    have := Algebra.adjoin_eq_ring_closure (R := R)
      ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))
    intro y hy
    have hy' : y ∈ (C.toSubring) := hy
    rw [hC, this] at hy'
    have hle : Subring.closure (Set.range (algebraMap R B) ∪
        ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))
        ≤ Ψ.range := by
      rw [Subring.closure_le]
      rintro z (⟨r, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨b, rfl⟩)
      · refine ⟨(algebraMap R S' r) ⊗ₜ 1, ?_⟩
        rw [htmul, h1, mul_one, IsScalarTower.algebraMap_apply R S B]
        rfl
      · refine ⟨(⟨s, hs⟩ : S') ⊗ₜ 1, ?_⟩
        rw [htmul, h1, mul_one]
      · refine ⟨1 ⊗ₜ b, ?_⟩
        rw [htmul]; simp
    exact hle hy'
  let f : S' ⊗[A₀] B₀ →+* C := Ψ.codRestrict C.toSubring hsub
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => hΨ (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj hy
    exact ⟨x, rfl⟩
  let eqv : S' ⊗[A₀] B₀ ≃+* C := RingEquiv.ofBijective f hf
  letI alg : Algebra S' C := (f.comp (algebraMap S' (S' ⊗[A₀] B₀))).toAlgebra
  have tower : IsScalarTower R S' C := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    apply Subtype.ext
    show algebraMap R B r = Ψ (algebraMap S' (S' ⊗[A₀] B₀) (algebraMap R S' r))
    rw [Algebra.TensorProduct.algebraMap_apply, htmul, h1, mul_one,
      IsScalarTower.algebraMap_apply R S B]
    rfl
  refine ⟨alg, tower, ?_⟩
  let eA : S' ⊗[A₀] B₀ ≃ₐ[S'] C := AlgEquiv.ofRingEquiv (f := eqv) (fun _ => rfl)
  haveI : Algebra.Etale S' (S' ⊗[A₀] B₀) := Algebra.Etale.baseChange A₀ B₀ S'
  exact Algebra.Etale.of_equiv eA

end GlobalTheory
