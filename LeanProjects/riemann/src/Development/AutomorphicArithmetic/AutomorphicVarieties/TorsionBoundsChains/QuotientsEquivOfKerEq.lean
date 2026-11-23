import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.KerOrb

open CategoryTheory UpperTheory.V.KH

private theorem UpperTheory.V.KH.quotients_equiv_of_ker_eq {A B C : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (a : A →+ B) (b : A →+ C) (ha : Function.Surjective a)
    (hb : Function.Surjective b) (h : a.ker = b.ker) : Nonempty (B ≃+ C) :=
  ⟨(QuotientAddGroup.quotientKerEquivOfSurjective a ha).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq h).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective b hb))⟩

private theorem UpperTheory.V.KH.hZero_push {R G : Type} [CommRing R] [Group G] (N M : Rep.{0} R G) (e : N ⟶ M) (x : N)
    (hx : x ∈ Representation.Coinvariants.ker N.ρ) :
    e.hom x ∈ Representation.Coinvariants.ker M.ρ := by
  have := (Representation.Coinvariants.mk_eq_zero N.ρ).2 hx
  rw [← Representation.Coinvariants.mk_eq_zero, ← Representation.Coinvariants.map_mk, this,
    map_zero]

private theorem UpperTheory.V.KH.hZero_lift {R G : Type} [CommRing R] [Group G] (N M : Rep.{0} R G) (e : N ⟶ M)
    (he : Function.Surjective e.hom) (y : M)
    (hy : y ∈ Representation.Coinvariants.ker M.ρ) :
    ∃ x ∈ Representation.Coinvariants.ker N.ρ, e.hom x = y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨g, v⟩, rfl⟩ := hy
    obtain ⟨u, rfl⟩ := he v
    exact ⟨N.ρ g u - u, Representation.Coinvariants.sub_mem_ker g u, by
      rw [map_sub, Rep.hom_comm_apply]⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨v, hv, rfl⟩ := hb
    exact ⟨u + v, Submodule.add_mem _ hu hv, map_add _ _ _⟩
  | smul c a _ ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    exact ⟨_, Submodule.smul_mem _ c hu, map_smul e.hom c u⟩

private theorem UpperTheory.V.KH.hZero_gen {R G : Type} [CommRing R] [Group G] (N M : Rep.{0} R G)
    (e : N ⟶ M) (he : Function.Surjective e.hom) :
    ∃ a : N →+ groupHomology M 0, Function.Surjective a ∧
      ∀ f, a f = 0 ↔ ∃ x ∈ Representation.Coinvariants.ker N.ρ, e.hom (f - x) = 0 := by
  let ψ : groupHomology M 0 ≃ₗ[R] M.ρ.Coinvariants := (groupHomology.H0Iso M).toLinearEquiv
  let a : N →ₗ[R] groupHomology M 0 :=
    ψ.symm.toLinearMap ∘ₗ Representation.Coinvariants.mk M.ρ ∘ₗ e.hom.toLinearMap
  refine ⟨a.toAddMonoidHom, ψ.symm.surjective.comp
    ((Representation.Coinvariants.mk_surjective M.ρ).comp he), fun f => ?_⟩
  have h1 : a.toAddMonoidHom f = 0 ↔ e.hom f ∈ Representation.Coinvariants.ker M.ρ :=
    ψ.symm.map_eq_zero_iff.trans (Representation.Coinvariants.mk_eq_zero M.ρ)
  rw [h1]
  constructor
  · intro h
    obtain ⟨k, hk, hkf⟩ := hZero_lift N M e he _ h
    exact ⟨k, hk, by rw [map_sub, hkf, sub_self]⟩
  · rintro ⟨x, hx, h⟩
    rw [map_sub, sub_eq_zero] at h
    rw [h]
    exact hZero_push N M e x hx

theorem UpperTheory.V.KH.hZero :
    ∀ (G X : Type) [Group G] [MulAction G X] (M : Rep ℤ G) (e : permRep G X ⟶ M) (S : Set (X →₀ ℤ)),
      Function.Surjective e.hom → (∀ f : X →₀ ℤ, e.hom f = 0 ↔ f ∈ Submodule.span ℤ S) →
      Nonempty (groupHomology M 0 ≃+ ((MulAction.orbitRel.Quotient G X →₀ ℤ) ⧸
        Submodule.span ℤ (Finsupp.mapDomain
          (Quotient.mk (MulAction.orbitRel G X) : X → MulAction.orbitRel.Quotient G X) '' S))) := by
  intro G X _ _ M e S he hS
  set q : X → MulAction.orbitRel.Quotient G X := Quotient.mk (MulAction.orbitRel G X) with hq
  let L : (X →₀ ℤ) →ₗ[ℤ] (MulAction.orbitRel.Quotient G X →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ q
  have hL : LinearMap.ker L = Representation.Coinvariants.ker (perm G X) := kerOrb G X
  have hsp : Submodule.span ℤ (Finsupp.mapDomain q '' S) = (Submodule.span ℤ S).map L :=
    (Submodule.map_span L S).symm
  rw [hsp]
  obtain ⟨a, ha, hak⟩ := hZero_gen (permRep G X) M e he
  let a' : (X →₀ ℤ) →+ groupHomology M 0 := a
  have hak' : ∀ f : X →₀ ℤ, a' f = 0 ↔
      ∃ x ∈ LinearMap.ker L, f - x ∈ Submodule.span ℤ S := by
    intro f
    rw [hL]
    simp only [← hS]
    exact hak f
  let b : (X →₀ ℤ) →+ (_ ⧸ (Submodule.span ℤ S).map L) :=
    (((Submodule.span ℤ S).map L).mkQ ∘ₗ L).toAddMonoidHom
  have hb : Function.Surjective b :=
    (Submodule.mkQ_surjective _).comp (Finsupp.mapDomain_surjective Quotient.mk_surjective)
  have hab : a'.ker = b.ker := by
    ext f
    have h2 : f ∈ b.ker ↔ L f ∈ (Submodule.span ℤ S).map L :=
      Submodule.Quotient.mk_eq_zero _
    rw [AddMonoidHom.mem_ker, hak', h2]
    constructor
    · rintro ⟨k, hk, h⟩
      exact ⟨f - k, h, by rw [map_sub, LinearMap.mem_ker.1 hk, sub_zero]⟩
    · rintro ⟨s, hs, hsf⟩
      exact ⟨f - s, by rw [LinearMap.mem_ker, map_sub, hsf, sub_self],
        by rwa [sub_sub_cancel]⟩
  obtain ⟨φ⟩ := quotients_equiv_of_ker_eq a' b ha hb hab
  exact ⟨φ⟩
