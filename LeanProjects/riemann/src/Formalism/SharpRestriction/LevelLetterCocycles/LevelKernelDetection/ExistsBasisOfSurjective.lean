import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Module

private theorem exists_linear_rightInverse_of_surjective {R : Type} [CommRing R] {m₁ m₂ : ℕ}
    (f : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R)) (hf : Function.Surjective f) :
    ∃ s : (Fin m₂ → R) →ₗ[R] (Fin m₁ → R), ∀ y, f (s y) = y := by
  refine ⟨(Pi.basisFun R (Fin m₂)).constr R (fun j => (hf (Pi.single j 1)).choose), ?_⟩
  have h : f ∘ₗ (Pi.basisFun R (Fin m₂)).constr R (fun j => (hf (Pi.single j 1)).choose)
      = LinearMap.id := by
    refine (Pi.basisFun R (Fin m₂)).ext fun j => ?_
    rw [LinearMap.comp_apply, Basis.constr_basis, LinearMap.id_apply, Pi.basisFun_apply]
    exact (hf (Pi.single j 1)).choose_spec
  intro y
  exact LinearMap.congr_fun h y

theorem exists_basis_of_surjective {R : Type} [CommRing R] [IsLocalRing R] {m₁ m₂ : ℕ}
    (f : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R)) (hf : Function.Surjective f) :
    ∃ B : Module.Basis (Fin m₂ ⊕ Fin (m₁ - m₂)) R (Fin m₁ → R),
      (∀ j, f (B (Sum.inl j)) = Pi.single j 1) ∧ ∀ j, f (B (Sum.inr j)) = 0 := by
  obtain ⟨s, hs⟩ := exists_linear_rightInverse_of_surjective f hf
  have hfk : ∀ k : LinearMap.ker f, f (k : Fin m₁ → R) = 0 := fun k => LinearMap.mem_ker.mp k.2
  let q : (Fin m₁ → R) →ₗ[R] (Fin m₁ → R) := LinearMap.id - s ∘ₗ f
  have hq : ∀ x, q x = x - s (f x) := fun x => by
    first
    | rfl
    | simp [q]
  have hmem : ∀ x, q x ∈ LinearMap.ker f := fun x => by
    rw [hq, LinearMap.mem_ker, map_sub, hs, sub_self]
  let r : (Fin m₁ → R) →ₗ[R] LinearMap.ker f := LinearMap.codRestrict (LinearMap.ker f) q hmem
  have hr : ∀ x, (r x : Fin m₁ → R) = x - s (f x) := fun x => by
    first
    | exact hq x
    | simp [r, hq]
  have hrk : ∀ k : LinearMap.ker f, r k = k := fun k => by
    apply Subtype.ext
    rw [hr, hfk k, map_zero, sub_zero]
  have hfg : ∀ p : (Fin m₂ → R) × LinearMap.ker f, f (s p.1 + (p.2 : Fin m₁ → R)) = p.1 :=
    fun p => by rw [map_add, hs, hfk, add_zero]
  let g : (Fin m₂ → R) × LinearMap.ker f →ₗ[R] (Fin m₁ → R) :=
    LinearMap.coprod s (LinearMap.ker f).subtype
  let h : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R) × LinearMap.ker f := LinearMap.prod f r
  have hg : ∀ p, g p = s p.1 + (p.2 : Fin m₁ → R) := fun p => by
    first
    | rfl
    | simp [g]
  have hh : ∀ x, h x = (f x, r x) := fun x => by
    first
    | rfl
    | simp [h]
  have h₁ : g ∘ₗ h = LinearMap.id := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hh, hg, LinearMap.id_apply]
    show s (f x) + (r x : Fin m₁ → R) = x
    rw [hr]
    abel
  have h₂ : h ∘ₗ g = LinearMap.id := LinearMap.ext fun p => by
    rw [LinearMap.comp_apply, hg, hh, LinearMap.id_apply, hfg p]
    refine Prod.ext rfl (Subtype.ext ?_)
    show (r (s p.1 + (p.2 : Fin m₁ → R)) : Fin m₁ → R) = p.2
    rw [hr, hfg p]
    abel
  let e : ((Fin m₂ → R) × LinearMap.ker f) ≃ₗ[R] (Fin m₁ → R) := LinearEquiv.ofLinear g h h₁ h₂
  have he : ∀ p, f (e p) = p.1 := fun p => by
    show f (g p) = p.1
    rw [hg, hfg p]
  have hproj : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype r (LinearMap.ext fun k => by
      rw [LinearMap.comp_apply, Submodule.subtype_apply, hrk, LinearMap.id_apply])
  have hfin : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_surjective r (fun k => ⟨k, hrk k⟩)
  have hfree : Module.Free R (LinearMap.ker f) := by
    first
    | exact Module.free_of_flat_of_isLocalRing
    | exact Module.free_of_projective_of_isLocalRing
    | infer_instance
  let bk := Module.Free.chooseBasis R (LinearMap.ker f)
  let bp := (Pi.basisFun R (Fin m₂)).prod bk
  let b := bp.map e
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R (LinearMap.ker f)) = m₁ - m₂ := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
    omega
  have hb : ∀ i, f (b i) = (bp i).1 := fun i => by
    rw [Basis.map_apply, he]
  refine ⟨b.reindex (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFinOfCardEq hcard)),
    fun j => ?_, fun j => ?_⟩
  · rw [Basis.reindex_apply, hb]
    first
    | simp [bp, Basis.prod_apply]
    | simp [bp]
  · rw [Basis.reindex_apply, hb]
    first
    | simp [bp, Basis.prod_apply]
    | simp [bp]

end Formalism.MainNotions.N.Ln03.Pf
