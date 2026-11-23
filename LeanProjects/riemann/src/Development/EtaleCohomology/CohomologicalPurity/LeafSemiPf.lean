import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem LeafSemi_of : LeafSemi := by
  intro hA9 hG
  intro q _ X Z S p ι _ d e _ _ hq U hU N i
  obtain ⟨gys, rs, hgys⟩ := hG d
  let P : SP d := ⟨X, Z, S, p, ι, e, U, inferInstance, inferInstance, inferInstance, hU⟩
  have hqX : IsUnit (q : Γ(P.X, ⊤)) := by
    simpa using hq.map p.appTop.hom
  have hex := (hgys q P hqX).1
  have hsub : ∀ m j : ℤ, m < 0 → Subsingleton (Ht q (sch.obj Z) m j) :=
    fun m j hm => (hA9 (ZMod q) (tw q j)).1 _ m hm
  obtain ⟨j, rfl⟩ : ∃ j, i = j + d := ⟨i - d, by ring⟩
  constructor
  · intro hN
    refine ⟨?_, ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d := ⟨N - 2 * d, by ring⟩
      have hm : m < 0 := by omega
      have := hsub m j hm
      rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨b, rfl⟩ := ((hex m j).2.2 a).1 ha
      rw [Subsingleton.elim b 0, map_zero]
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d - 1 := ⟨N - 2 * d + 1, by ring⟩
      have hm : m < 0 := by omega
      have := hsub m j hm
      intro u
      exact ((hex m j).1 u).1 (Subsingleton.elim _ _)
  · intro hN
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d := ⟨N - 2 * d, by ring⟩
    have hm : m < 0 := by omega
    have := hsub m j hm
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨b, rfl⟩ := ((hex m j).2.2 a).1 ha
    rw [Subsingleton.elim b 0, map_zero]

end LateralTheory.CohomologicalPurity
