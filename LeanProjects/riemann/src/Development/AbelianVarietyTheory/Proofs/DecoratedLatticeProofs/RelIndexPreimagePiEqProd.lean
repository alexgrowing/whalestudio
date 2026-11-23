import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMemProjEqOnFinset

namespace GlobalTheory

theorem relIndex_preimage_pi_eq_prod :
    ∀ {G : Type} [Group G] {r : ℕ} {H : Fin r → Type} [∀ i, Group (H i)]
      (φ : G →* ((i : Fin r) → H i)) (U U' : Subgroup G) (K J : (i : Fin r) → Subgroup (H i)),
      (∀ i, J i ≤ K i) → (∀ g ∈ U, ∀ i, φ g i ∈ K i) →
      (∀ x : (i : Fin r) → H i, (∀ i, x i ∈ K i) → ∃ g ∈ U, φ g = x) →
      (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ J i) →
      U'.relIndex U = ∏ i, (J i).relIndex (K i) := by
  intro G _ r H _ φ U U' K J _ hUK hsurj hU'
  let f : U →* (∀ i, K i) :=
    { toFun := fun g i => ⟨φ g i, hUK g g.2 i⟩
      map_one' := by
        funext i
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        funext i
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg, hx⟩ := hsurj (fun i => (x i : H i)) (fun i => (x i).2)
    refine ⟨⟨g, hg⟩, ?_⟩
    funext i
    apply Subtype.ext
    change φ g i = _
    rw [hx]
  have hc : U'.subgroupOf U =
      (Subgroup.pi Set.univ fun i => (J i).subgroupOf (K i)).comap f := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hU']
    constructor
    · rintro ⟨-, h⟩ i -
      exact Subgroup.mem_subgroupOf.2 (h i)
    · intro h
      exact ⟨g.2, fun i => Subgroup.mem_subgroupOf.1 (h i (Set.mem_univ _))⟩
  rw [Subgroup.relIndex, hc, Subgroup.index_comap_of_surjective _ hf, index_pi_univ_dep]
  rfl

end GlobalTheory
