import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKillCut

open LateralTheory.E.E4

def LeafOne : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ m i : ℤ, 0 < m → ∀ x : Ht q (sch.obj C) m i,
  ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ pl q i γ m x = 0

theorem goal_of (hOne : LeafOne) : LateralTheory.E.E4.LeafKill := by
  intro hy q _ Ω _ _ hq C c hc m i hm hfin
  classical
  have key : ∀ s : Finset (Ht q (sch.obj C) m i), ∃ (C' : Scheme.{0}) (γ : C' ⟶ C),
      IsCurve (γ ≫ c) ∧ Surjective γ ∧ ∀ x ∈ s, pl q i γ m x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨C, 𝟙 C, by simpa using hc, inferInstance, by simp⟩
    | insert a s ha IH =>
      obtain ⟨C1, γ1, h1, s1, k1⟩ := IH
      obtain ⟨C2, γ2, h2, s2, k2⟩ := hOne hy q Ω hq (γ1 ≫ c) h1 m i hm (pl q i γ1 m a)
      have := s1
      have := s2
      refine ⟨C2, γ2 ≫ γ1, by simpa [Category.assoc] using h2, inferInstance, ?_⟩
      intro x hx
      rw [pl_comp]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact k2
      · rw [k1 x hx, map_zero]
  have := Fintype.ofFinite (Ht q (sch.obj C) m i)
  obtain ⟨C', γ, h1, h2, h3⟩ := key Finset.univ
  exact ⟨C', γ, h1, h2, AddMonoidHom.ext fun x => by simpa using h3 x (Finset.mem_univ x)⟩

end LateralTheory.E.LeafKillCut

end
