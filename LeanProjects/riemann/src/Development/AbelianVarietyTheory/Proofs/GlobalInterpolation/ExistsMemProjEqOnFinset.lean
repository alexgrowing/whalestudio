import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory

theorem exists_mem_proj_eq_on_finset {G ι : Type} [Group G] {Gv : ι → Type}
    [∀ v, Group (Gv v)] (π : ∀ v, G →* Gv v) (H : Subgroup G) (Kv : ∀ v, Subgroup (Gv v))
    (hH : ∀ v, ∀ h ∈ Kv v, ∃ g ∈ H, π v g = h ∧ ∀ w, w ≠ v → π w g = 1)
    (h : ∀ v, Gv v) (hh : ∀ v, h v ∈ Kv v) (T : Finset ι) :
    ∃ g ∈ H, (∀ v ∈ T, π v g = h v) ∧ ∀ v, v ∉ T → π v g = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, H.one_mem, by simp, by simp⟩
  | insert a T ha ih =>
    obtain ⟨g, hg, h1, h2⟩ := ih
    obtain ⟨g', hg', h3, h4⟩ := hH a (h a) (hh a)
    refine ⟨g' * g, H.mul_mem hg' hg, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [map_mul, h3, h2 _ ha, mul_one]
      · have hne : v ≠ a := fun e => ha (e ▸ hv)
        rw [map_mul, h4 v hne, h1 v hv, one_mul]
    · intro v hv
      rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, h4 v hv.1, h2 v hv.2, one_mul]

theorem index_pi_univ_dep {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_eq_prod_local :
    ∀ (G ι : Type) [Group G] (Gv : ι → Type) [∀ v, Group (Gv v)] (π : ∀ v, G →* Gv v)
      (H K U : Subgroup G) (Kv Uv : ∀ v, Subgroup (Gv v)) (S : Finset ι),
      (∀ v, ∀ h ∈ Kv v, ∃ g ∈ H, π v g = h ∧ ∀ w, w ≠ v → π w g = 1) →
      (∀ g, g ∈ K ↔ g ∈ H ∧ ∀ v, π v g ∈ Kv v) →
      (∀ g, g ∈ U ↔ g ∈ H ∧ ∀ v, π v g ∈ Uv v) →
      (∀ v, v ∉ S → Kv v ≤ Uv v) →
      U.relIndex K = ∏ v ∈ S, (Uv v).relIndex (Kv v) := by
  intro G ι _ Gv _ π H K U Kv Uv S hH hK hU hS
  classical
  let f : K →* (∀ v : S, Kv v) :=
    { toFun := fun g v => ⟨π v g, ((hK g).1 g.2).2 v⟩
      map_one' := by
        funext v
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        funext v
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    intro x
    let h : ∀ v, Gv v := fun v => if hv : v ∈ S then (x ⟨v, hv⟩ : Gv v) else 1
    have hh : ∀ v, h v ∈ Kv v := by
      intro v
      by_cases hv : v ∈ S
      · simp only [h, dif_pos hv]; exact (x ⟨v, hv⟩).2
      · simp only [h, dif_neg hv]; exact (Kv v).one_mem
    obtain ⟨g, hg, h1, h2⟩ := exists_mem_proj_eq_on_finset π H Kv hH h hh S
    have hgK : g ∈ K := by
      refine (hK g).2 ⟨hg, fun v => ?_⟩
      by_cases hv : v ∈ S
      · rw [h1 v hv]; exact hh v
      · rw [h2 v hv]; exact (Kv v).one_mem
    refine ⟨⟨g, hgK⟩, ?_⟩
    funext v
    apply Subtype.ext
    change π v g = _
    rw [h1 v v.2]
    simp only [h, dif_pos v.2]
  have hc : U.subgroupOf K =
      (Subgroup.pi Set.univ fun v : S => (Uv v).subgroupOf (Kv v)).comap f := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hU]
    constructor
    · rintro ⟨-, h⟩ v -
      exact Subgroup.mem_subgroupOf.2 (h v)
    · intro h
      refine ⟨((hK g).1 g.2).1, fun v => ?_⟩
      by_cases hv : v ∈ S
      · exact Subgroup.mem_subgroupOf.1 (h ⟨v, hv⟩ (Set.mem_univ _))
      · exact hS v hv (((hK g).1 g.2).2 v)
  rw [Subgroup.relIndex, hc, Subgroup.index_comap_of_surjective _ hf, index_pi_univ_dep]
  exact Finset.prod_coe_sort S (fun v => (Uv v).relIndex (Kv v))

end GlobalTheory
