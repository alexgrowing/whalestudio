import Mathlib
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.AlgStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeightContract

theorem step (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S]
    (f : R →+* S) (hf : Function.Injective f) (x : S) (hgen : Function.Surjective (Polynomial.eval₂RingHom f x))
    (halg : ∃ g : Polynomial R, g ≠ 0 ∧ Polynomial.eval₂ f x g = 0) (q : Ideal S) [q.IsPrime] :
    q.height ≤ (q.comap f).height :=
  ReciprocityTheory.CA.height_le_height_comap_of_eval₂_surjective f hf x hgen halg q

theorem height_le_height_comap : ∀ (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S]
    [IsDomain S] [Algebra R S] [FaithfulSMul R S] [Algebra.FiniteType R S] [Algebra.IsAlgebraic R S]
    (q : Ideal S) [q.IsPrime], q.height ≤ (q.comap (algebraMap R S)).height := by
  intro A B _ _ _ _ _ _ _ _ _ q _
  classical
  have key : ∀ s : Finset B, ∀ (q : Ideal (Algebra.adjoin A (s : Set B))) [q.IsPrime],
      q.height ≤ (q.comap (algebraMap A (Algebra.adjoin A (s : Set B)))).height := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro q _
      refine step A _ (algebraMap A _) (FaithfulSMul.algebraMap_injective _ _) 0 ?_
        ⟨Polynomial.X, Polynomial.X_ne_zero, by simp⟩ q
      rintro ⟨y, hy⟩
      rw [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot] at hy
      obtain ⟨a, rfl⟩ := hy
      exact ⟨Polynomial.C a, Subtype.ext (by simp)⟩
    | insert x s _ ih =>
      intro q _
      have hle : Algebra.adjoin A (s : Set B) ≤ Algebra.adjoin A ((insert x s : Finset B) : Set B) :=
        Algebra.adjoin_mono (by simp)
      have : Algebra.FiniteType A (Algebra.adjoin A (s : Set B)) :=
        Algebra.FiniteType.adjoin_of_finite s.finite_toSet
      have : IsNoetherianRing (Algebra.adjoin A (s : Set B)) := Algebra.FiniteType.isNoetherianRing A _
      have hx : x ∈ Algebra.adjoin A ((insert x s : Finset B) : Set B) := Algebra.subset_adjoin (by simp)
      have h1 := step _ _ (Subalgebra.inclusion hle).toRingHom (Subalgebra.inclusion_injective hle) ⟨x, hx⟩
        ?_ ?_ q
      · have h2 := ih (q.comap (Subalgebra.inclusion hle).toRingHom)
        rw [Ideal.comap_comap] at h2
        have hc : (Subalgebra.inclusion hle).toRingHom.comp (algebraMap A (Algebra.adjoin A (s : Set B))) =
            algebraMap A (Algebra.adjoin A ((insert x s : Finset B) : Set B)) :=
          RingHom.ext fun a => Subtype.ext rfl
        rw [hc] at h2
        exact h1.trans h2
      · rintro ⟨y, hy⟩
        induction hy using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Finset.coe_insert] at hy
          rcases hy with rfl | hy
          · exact ⟨Polynomial.X, by simp⟩
          · exact ⟨Polynomial.C ⟨y, Algebra.subset_adjoin hy⟩, Subtype.ext (by simp)⟩
        | algebraMap a => exact ⟨Polynomial.C (algebraMap A _ a), Subtype.ext (by simp)⟩
        | add y z _ _ hy hz =>
          obtain ⟨p, hp⟩ := hy
          obtain ⟨q, hq⟩ := hz
          exact ⟨p + q, by rw [map_add, hp, hq]; rfl⟩
        | mul y z _ _ hy hz =>
          obtain ⟨p, hp⟩ := hy
          obtain ⟨q, hq⟩ := hz
          exact ⟨p * q, by rw [map_mul, hp, hq]; rfl⟩
      · obtain ⟨g, hg, h0⟩ := Algebra.IsAlgebraic.isAlgebraic (R := A) x
        refine ⟨g.map (algebraMap A _), (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective _ _)).2 hg, ?_⟩
        apply Subtype.ext
        rw [Polynomial.eval₂_map]
        have := Polynomial.hom_eval₂ g
          ((Subalgebra.inclusion hle).toRingHom.comp (algebraMap A (Algebra.adjoin A (s : Set B))))
          (Algebra.adjoin A ((insert x s : Finset B) : Set B)).val.toRingHom ⟨x, hx⟩
        exact this.trans h0
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  have : Algebra.FiniteType A (Algebra.adjoin A (s : Set B)) :=
    Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  have : IsNoetherianRing (Algebra.adjoin A (s : Set B)) := Algebra.FiniteType.isNoetherianRing A _

  have h1 := step _ _ (Algebra.adjoin A (s : Set B)).val.toRingHom Subtype.val_injective 0 ?_
    ⟨Polynomial.X, Polynomial.X_ne_zero, by simp⟩ q
  · have h2 := key s (q.comap (Algebra.adjoin A (s : Set B)).val.toRingHom)
    rw [Ideal.comap_comap] at h2
    have hc : (Algebra.adjoin A (s : Set B)).val.toRingHom.comp (algebraMap A (Algebra.adjoin A (s : Set B))) =
        algebraMap A B := RingHom.ext fun a => rfl
    rw [hc] at h2
    exact h1.trans h2
  · intro y
    have hy : y ∈ Algebra.adjoin A (s : Set B) := hs ▸ Algebra.mem_top
    exact ⟨Polynomial.C ⟨y, hy⟩, by simp⟩

end GlobalTheory.HeightContract
