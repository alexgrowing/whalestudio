import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.hom_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (A A' B B' : Glob l L) (a : A.Hom A') (b : B.Hom B') (h : A.Hom B), a.p.ker ≤ (b.p.comp h.p).ker → ∃ h' : A'.Hom B', ∀ x, h'.p (a.p x) = b.p (h.p x) := by
  intro l _ L A A' B B' a b h hk
  have hT1 : T1Space A'.Γ := by
    refine ⟨fun x => ?_⟩
    have h1 : IsPreconnected (closure ({x} : Set A'.Γ)) := isPreconnected_singleton.closure
    have h2 := h1.subsingleton
    have h3 : closure ({x} : Set A'.Γ) = {x} :=
      h2.eq_singleton_of_mem (subset_closure (Set.mem_singleton x))
    exact closure_eq_iff_isClosed.mp h3
  have hT2 : T2Space A'.Γ := inferInstance
  let q : A'.Γ →* B'.Γ := a.p.liftOfRightInverse (Function.surjInv a.surj)
    (Function.rightInverse_surjInv a.surj) ⟨b.p.comp h.p, hk⟩
  have hq : ∀ x, q (a.p x) = b.p (h.p x) := fun x =>
    a.p.liftOfRightInverse_comp_apply _ _ ⟨b.p.comp h.p, hk⟩ x
  have hquot : Topology.IsQuotientMap a.p :=
    a.cont.isClosedMap.isQuotientMap a.cont a.surj
  refine ⟨⟨q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hq⟩
  · rw [hquot.continuous_iff]
    have : (q : A'.Γ → B'.Γ) ∘ a.p = fun x => b.p (h.p x) := funext hq
    rw [this]
    exact b.cont.comp h.cont
  · intro y
    obtain ⟨z, rfl⟩ := b.surj y
    obtain ⟨x, rfl⟩ := h.surj z
    exact ⟨a.p x, hq x⟩
  · intro g
    obtain ⟨x, rfl⟩ := a.surj g
    rw [hq, b.η, h.η, a.η]
  · rw [← a.c, hq, h.c, b.c]
  · intro g
    obtain ⟨x, rfl⟩ := a.surj g
    rw [hq, b.ε, h.ε, a.ε]
  · intro v g
    rw [← a.φ, hq, h.φ, b.φ]
  · intro v g
    rw [← a.φu, hq, h.φu, b.φu]
