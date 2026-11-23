import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

theorem h2_twist_exists_of_iUnion_open : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    (ε : G →* Oˣ) {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M), Monotone N → (∀ n, IsOpen (N n : Set M)) → (∀ x, ∃ n, x ∈ N n) →
    ∀ z : H2 (twist ε M), ∃ n, ∃ z' : H2 (twist ε (N n)),
      mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype) z' = z := by
  intro O _ _ G _ _ _ ε M _ _ _ _ _ N hmono hopen hcov z
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hK : IsCompact (Set.range f.1) := isCompact_range f.2.1
  have hmono' : Monotone (fun n => (N n : Set M)) := fun a b h => SetLike.coe_subset_coe.mpr (hmono h)
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n => (N n : Set M)) hopen
    (fun x _ => Set.mem_iUnion.mpr (hcov x)) hmono'.directed_le
  let f' : G × G → N n := fun x => ⟨f.1 x, hn ⟨x, rfl⟩⟩
  have hc : Continuous f' := f.2.1.subtype_mk _
  have hcoc : f' ∈ Z2 (twist ε (N n)) := by
    refine ⟨hc, fun g h k => ?_⟩
    apply Subtype.ext
    have e := f.2.2 g h k
    have key : ∀ x : N n, ((twist ε (N n) g x : N n) : M) = twist ε M g (x : M) := fun x => rfl
    simpa [f', key] using e
  refine ⟨n, Submodule.Quotient.mk ⟨f', hcoc⟩, ?_⟩
  rfl

end GlobalTheory
