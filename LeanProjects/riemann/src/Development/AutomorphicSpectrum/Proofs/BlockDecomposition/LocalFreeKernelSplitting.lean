import Mathlib
open TensorProduct

namespace GlobalTheory.CompanionTheory.LocalSplit

theorem injective_of_basis_image {k V U ι : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup U] [Module k U] (b : Module.Basis ι k V) (g : V →ₗ[k] U)
    (h : LinearIndependent k (g ∘ b)) : Function.Injective g := by
  have hg : ⇑g = (Finsupp.linearCombination k (g ∘ b)) ∘ b.repr := by
    funext x
    conv_lhs => rw [← b.linearCombination_repr x]
    simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  rw [hg]
  exact (show Function.Injective (Finsupp.linearCombination k (g ∘ b)) from h).comp b.repr.injective

theorem ker_facts {A Q : Type} [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Free A Q] (s : ℕ)
    (f : (Fin s → A) →ₗ[A] Q) (p : Q →ₗ[A] (Fin s → A)) (h : p ∘ₗ f = LinearMap.id) :
    Module.Free A (LinearMap.ker p) ∧ Module.Finite A (LinearMap.ker p) ∧
      s + Module.finrank A (LinearMap.ker p) = Module.finrank A Q := by
  have hpf : ∀ y, p (f y) = y := fun y => LinearMap.congr_fun h y
  let e : Q ≃ₗ[A] (LinearMap.ker p) × (Fin s → A) := LinearEquiv.ofLinear
    (LinearMap.prod
      (LinearMap.codRestrict (LinearMap.ker p) (LinearMap.id - f ∘ₗ p)
        (fun x => by simp [hpf]))
      p)
    (LinearMap.coprod (LinearMap.ker p).subtype f)
    (by
      ext x <;> simp [hpf])
    (by
      ext x
      simp)
  have hproj : Module.Projective A ((LinearMap.ker p) × (Fin s → A)) :=
    Module.Projective.of_equiv e
  have hker : Module.Projective A (LinearMap.ker p) :=
    Module.Projective.of_split (LinearMap.inl A (LinearMap.ker p) (Fin s → A))
      (LinearMap.fst A (LinearMap.ker p) (Fin s → A)) (by ext; simp)
  have hfin : Module.Finite A (LinearMap.ker p) :=
    Module.Finite.of_surjective (LinearMap.fst A (LinearMap.ker p) (Fin s → A) ∘ₗ e.toLinearMap)
      (fun y => ⟨e.symm (y, 0), by simp⟩)
  have hfree : Module.Free A (LinearMap.ker p) := Module.free_of_flat_of_isLocalRing
  refine ⟨hfree, hfin, ?_⟩
  have := e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_fin_fun] at this
  omega

theorem exists_section {A Q P : Type} [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup P] [Module A P] [Module.Finite A Q] [Module.Free A Q] [Module.Finite A P]
    [Module.Free A P] (d : Q →ₗ[A] P) :
    ∃ (s : ℕ) (f : (Fin s → A) →ₗ[A] Q) (t : P →ₗ[A] (Fin s → A)),
      t ∘ₗ (d ∘ₗ f) = LinearMap.id ∧
      s + Module.finrank (IsLocalRing.ResidueField A)
        (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) = Module.finrank A Q := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl
    (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A)))
  let v := Module.finBasis (IsLocalRing.ResidueField A) C
  have hsurj : Function.Surjective (TensorProduct.mk A (IsLocalRing.ResidueField A) Q 1) :=
    TensorProduct.mk_surjective A Q (IsLocalRing.ResidueField A) IsLocalRing.residue_surjective
  choose a ha using fun i => hsurj (v i : (IsLocalRing.ResidueField A) ⊗[A] Q)
  let f : (Fin (Module.finrank (IsLocalRing.ResidueField A) C) → A) →ₗ[A] Q :=
    Fintype.linearCombination A a
  have hf : ∀ i, f (Pi.single i 1) = a i := by
    intro i
    simp [f, Fintype.linearCombination_apply_single]
  have hgk : LinearMap.ker ((d.baseChange (IsLocalRing.ResidueField A)) ∘ₗ C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hx1 : (x : (IsLocalRing.ResidueField A) ⊗[A] Q) ∈
        LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A)) := hx
    have := hC.disjoint.le_bot ⟨hx1, x.2⟩
    simpa using this
  have hinj : Function.Injective ((d ∘ₗ f).lTensor (IsLocalRing.ResidueField A)) := by
    rw [← LinearMap.baseChange_eq_ltensor]
    apply injective_of_basis_image
      (Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) (Pi.basisFun A _))
    have hl := v.linearIndependent.map' _ hgk
    have key : ⇑((d ∘ₗ f).baseChange (IsLocalRing.ResidueField A)) ∘
        ⇑(Algebra.TensorProduct.basis (IsLocalRing.ResidueField A)
          (Pi.basisFun A (Fin (Module.finrank (IsLocalRing.ResidueField A) C)))) =
        ⇑((d.baseChange (IsLocalRing.ResidueField A)) ∘ₗ C.subtype) ∘ ⇑v := by
      funext i
      have h2 := ha i
      simp only [TensorProduct.mk_apply] at h2
      simp [Algebra.TensorProduct.basis_apply, hf, ← h2]
    rw [key]
    exact hl
  obtain ⟨t, ht⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective (d ∘ₗ f)).2 hinj
  refine ⟨_, f, t, ht, ?_⟩
  rw [← Module.finrank_baseChange (R := IsLocalRing.ResidueField A) (S := A) (M' := Q),
    ← Submodule.finrank_add_eq_of_isCompl hC]
  omega

theorem exists_idempotent_of_residueField (A Q P : Type) [CommRing A] [IsLocalRing A]
    [AddCommGroup Q] [Module A Q] [AddCommGroup P] [Module A P] [Module.Finite A Q]
    [Module.Free A Q] [Module.Finite A P] [Module.Free A P] (d : Q →ₗ[A] P) :
    ∃ r : P →ₗ[A] Q, (r ∘ₗ d ∘ₗ r ∘ₗ d = r ∘ₗ d) ∧ Module.Free A (LinearMap.ker (r ∘ₗ d)) ∧
      Module.Finite A (LinearMap.ker (r ∘ₗ d)) ∧
      Module.finrank A (LinearMap.ker (r ∘ₗ d)) =
        Module.finrank (IsLocalRing.ResidueField A)
          (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) := by
  obtain ⟨s, f, t, ht, hs⟩ := exists_section d
  have hpf : ∀ y, t (d (f y)) = y := fun y => LinearMap.congr_fun ht y
  have hfinj : Function.Injective f := fun x y hxy => by
    rw [← hpf x, ← hpf y, hxy]
  have hker : LinearMap.ker ((f ∘ₗ t) ∘ₗ d) = LinearMap.ker (t ∘ₗ d) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    exact ⟨fun h => hfinj (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  obtain ⟨h1, h2, h3⟩ := ker_facts s f (t ∘ₗ d) ht
  refine ⟨f ∘ₗ t, ?_, ?_, ?_, ?_⟩
  · ext x
    simp [hpf]
  · rw [hker]; exact h1
  · rw [hker]; exact h2
  · rw [hker]; omega

end GlobalTheory.CompanionTheory.LocalSplit
