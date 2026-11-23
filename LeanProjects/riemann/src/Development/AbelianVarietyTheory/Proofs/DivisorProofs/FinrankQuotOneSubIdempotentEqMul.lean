import Mathlib
open scoped TensorProduct
universe u

namespace GlobalTheory

theorem finrank_quot_one_sub_idem_eq_mul : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k) (e : A), IsIdempotentElem e → φ e = 1 → (∀ a, φ a = 0 → IsNilpotent (e * a)) → ∀ (H : Type u) [AddCommGroup H] [Module A H] [Module k H] [IsScalarTower k A H] [FiniteDimensional k H] [Module.Projective A H], Module.finrank k (H ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A H)) = Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) * Module.finrank k (A ⧸ Ideal.span {1 - e}) := by
  intro k _ A _ _ _ φ e he hφe hnil H _ _ _ _ _ _
  have : Module.Finite A H := Module.Finite.of_restrictScalars_finite k A H
  set I : Ideal A := Ideal.span {1 - e} with hI
  have hIφ : ∀ a ∈ I, φ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [hφe]
  have hItop : I ≠ ⊤ := by
    intro h
    have := hIφ 1 (h ▸ Submodule.mem_top)
    simp at this
  let B := A ⧸ I
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hItop
  have hloc : IsLocalRing B := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    have key : ∀ x : A, φ x ≠ 0 → IsUnit (Ideal.Quotient.mk I x) := by
      intro x hx
      have he1 : Ideal.Quotient.mk I e = 1 := by
        rw [eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      set a := x - algebraMap k A (φ x) with ha
      have hφa : φ a = 0 := by simp [ha]
      have hxa : x = algebraMap k A (φ x) + a := by simp [ha]
      rw [hxa, map_add]
      have hn : IsNilpotent (Ideal.Quotient.mk I a) := by
        have : Ideal.Quotient.mk I a = Ideal.Quotient.mk I (e * a) := by rw [map_mul, he1, one_mul]
        rw [this]; exact (hnil a hφa).map _
      apply hn.isUnit_add_left_of_commute _ (Commute.all _ _)
      have : IsUnit (algebraMap k B (φ x)) := (isUnit_iff_ne_zero.mpr hx).map _
      simpa [Ideal.Quotient.mk_algebraMap] using this
    intro b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    by_cases hx : φ x = 0
    · right
      rw [← map_one (Ideal.Quotient.mk I), ← map_sub]
      exact key _ (by simp [hx])
    · left; exact key x hx
  let T := B ⊗[A] H
  have : Module.Free B T := Module.free_of_flat_of_isLocalRing

  have h3 : Module.finrank k (H ⧸ (I • ⊤ : Submodule A H)) = Module.finrank B T * Module.finrank k B := by
    let b := Module.Free.chooseBasis B T
    let e1 : T ≃ₗ[A] H ⧸ (I • ⊤ : Submodule A H) := TensorProduct.quotTensorEquivQuotSMul H I
    let e3 : (H ⧸ (I • ⊤ : Submodule A H)) ≃ₗ[A] (Module.Free.ChooseBasisIndex B T → B) :=
      e1.symm.trans (b.equivFun.restrictScalars A)
    rw [(e3.restrictScalars k).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Module.finrank_eq_card_chooseBasisIndex (R := B) (M := T)]
  have h4 : Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) = Module.finrank B T := by
    have hsurj : Function.Surjective φ := fun c => ⟨algebraMap k A c, φ.commutes c⟩
    let φB : B →ₐ[k] k := Ideal.Quotient.liftₐ I φ hIφ
    letI : Algebra A k := φ.toRingHom.toAlgebra
    letI : Algebra B k := φB.toRingHom.toAlgebra
    haveI : IsScalarTower A B k := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
    let f := Ideal.quotientKerAlgEquivOfSurjective hsurj
    let g : (A ⧸ RingHom.ker φ) ≃ₗ[A] k :=
      { f.toLinearEquiv with
        map_smul' := by
          intro a x
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
          change f (Ideal.Quotient.mk _ (a * y)) = φ a * f (Ideal.Quotient.mk _ y)
          simp [f, Ideal.quotientKerAlgEquivOfSurjective_apply] }
    let e6 : (k ⊗[A] H) ≃ₗ[A] H ⧸ (RingHom.ker φ • ⊤ : Submodule A H) :=
      (LinearEquiv.rTensor H g.symm).trans (TensorProduct.quotTensorEquivQuotSMul H (RingHom.ker φ))
    rw [← (e6.restrictScalars k).finrank_eq,
      ← (TensorProduct.AlgebraTensorModule.cancelBaseChange A B k k H).finrank_eq,
      Module.finrank_baseChange]
  rw [h3, h4]

end GlobalTheory
