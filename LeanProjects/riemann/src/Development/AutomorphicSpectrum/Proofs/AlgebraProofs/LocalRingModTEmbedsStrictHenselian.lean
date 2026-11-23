import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_basis_split_of_exact_of_fg_valuationRing :
    ∀ (V C A W B : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C]
      [IsFractionRing V C] [AddCommGroup A] [Module C A] [Module V A] [IsScalarTower V C A]
      [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [AddCommGroup B]
      [Module C B] [Module V B] [IsScalarTower V C B] (b : A →ₗ[C] W) (al : W →ₗ[C] B),
      Function.Injective b → Function.Exact b al → ∀ (T : Submodule V W), T.FG →
      ∃ (p q : ℕ) (w : Fin p → A) (t : Fin q → W), LinearIndependent C w ∧
        Submodule.span V (Set.range w) = T.comap (b.restrictScalars V) ∧
        LinearIndependent C (fun j => al (t j)) ∧
        Submodule.span V (Set.range fun j => al (t j)) = T.map (al.restrictScalars V) ∧
        LinearIndependent C (Sum.elim (fun i => b (w i)) t) ∧
        Submodule.span V (Set.range (Sum.elim (fun i => b (w i)) t)) = T := by
  intro V C A W B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b al hb hex T hT
  have : IsBezout V := ValuationRing.instIsBezout

  have hfree : ∀ (X : Type) [AddCommGroup X] [Module C X] [Module V X] [IsScalarTower V C X]
      (N : Submodule V X), N.FG → Module.Free V N := by
    intro X _ _ _ _ N hN
    have : Module.Finite V N := Module.Finite.iff_fg.mpr hN
    have : Module.Flat V N := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
      have h2 : ((a : V) • x : N) = 0 := ha
      have h3 : (a : V) • (x : X) = 0 := by
        have h4 := congrArg Subtype.val h2
        simpa using h4
      have h1 : (algebraMap V C (a : V)) • (x : X) = 0 := by
        rw [algebraMap_smul]; exact h3
      have ha0 : algebraMap V C (a : V) ≠ 0 := by
        intro h
        have h5 : (a : V) = 0 := (IsFractionRing.injective V C) (by rw [h, map_zero])
        exact nonZeroDivisors.coe_ne_zero a h5
      have hx0 : (x : X) = 0 := (smul_eq_zero.mp h1).resolve_left ha0
      exact Subtype.ext (by simp [hx0])
    exact Module.free_of_flat_of_isLocalRing

  have hL : ∀ (X : Type) [AddCommGroup X] [Module C X] [Module V X] [IsScalarTower V C X]
      (N : Submodule V X), N.FG → ∃ (n : ℕ) (v : Fin n → X),
        LinearIndependent C v ∧ Submodule.span V (Set.range v) = N := by
    intro X _ _ _ _ N hN
    have := hfree X N hN
    have : Module.Finite V N := Module.Finite.iff_fg.mpr hN
    let e := (Module.Free.chooseBasis V N).reindex
      (Fintype.equivFin (Module.Free.ChooseBasisIndex V N))
    refine ⟨Fintype.card (Module.Free.ChooseBasisIndex V N), fun i => (e i : X), ?_, ?_⟩
    · rw [← LinearIndependent.iff_fractionRing V C]
      exact e.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
    · have hr : Set.range (fun i => (e i : X)) = N.subtype '' Set.range e := by
        rw [← Set.range_comp]; rfl
      rw [hr, Submodule.span_image, e.span_eq, Submodule.map_subtype_top]

  obtain ⟨q, u, hu, hus⟩ := hL B (T.map (al.restrictScalars V)) (hT.map _)
  have hu_mem : ∀ j, u j ∈ T.map (al.restrictScalars V) := by
    intro j
    rw [← hus]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose t ht hta using fun j => Submodule.mem_map.mp (hu_mem j)
  have hta' : ∀ j, al (t j) = u j := fun j => hta j
  have hal : (fun j => al (t j)) = u := funext hta'

  have : Module.Free V (T.map (al.restrictScalars V)) := hfree B _ (hT.map _)
  have : Module.Finite V (T.map (al.restrictScalars V)) := Module.Finite.iff_fg.mpr (hT.map _)
  have : Module.Finite V T := Module.Finite.iff_fg.mpr hT
  have : Module.FinitePresentation V (T.map (al.restrictScalars V)) :=
    Module.finitePresentation_of_projective V _
  have hker : (LinearMap.ker ((al.restrictScalars V).submoduleMap T)).FG :=
    Module.FinitePresentation.fg_ker _ (LinearMap.submoduleMap_surjective _ _)
  have hK : (T.comap (b.restrictScalars V)).FG := by
    apply Submodule.fg_of_fg_map_injective (b.restrictScalars V) hb
    have heq : (T.comap (b.restrictScalars V)).map (b.restrictScalars V)
        = (LinearMap.ker ((al.restrictScalars V).submoduleMap T)).map T.subtype := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨b a, ha⟩, ?_, rfl⟩
        show ((al.restrictScalars V).submoduleMap T) ⟨b a, ha⟩ = 0
        apply Subtype.ext
        show al (b a) = 0
        exact (hex (b a)).mpr ⟨a, rfl⟩
      · rintro ⟨⟨y, hyT⟩, hy0, rfl⟩
        have hy0' : ((al.restrictScalars V).submoduleMap T) ⟨y, hyT⟩ = 0 := hy0
        have hy : al y = 0 := congrArg Subtype.val hy0'
        obtain ⟨a, rfl⟩ := (hex y).mp hy
        exact ⟨a, hyT, rfl⟩
    rw [heq]
    exact hker.map _
  obtain ⟨p, w, hw, hws⟩ := hL A (T.comap (b.restrictScalars V)) hK
  refine ⟨p, q, w, t, hw, hws, ?_, ?_, ?_, ?_⟩
  · rw [hal]; exact hu
  · rw [hal]; exact hus
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have h1 : ∀ i, al (b (w i)) = 0 := fun i => (hex _).mpr ⟨w i, rfl⟩
    have h2 : ∑ j, g (Sum.inr j) • u j = 0 := by
      have h7 := congrArg al hg
      simpa [map_add, map_sum, map_smul, h1, hta'] using h7
    have h3 : ∀ j, g (Sum.inr j) = 0 :=
      Fintype.linearIndependent_iff.mp hu (fun j => g (Sum.inr j)) h2
    have h4 : ∑ i, g (Sum.inl i) • b (w i) = 0 := by
      simpa [h3] using hg
    have h5 : ∑ i, g (Sum.inl i) • w i = 0 := by
      apply hb
      simpa [map_sum, map_smul] using h4
    have h6 := Fintype.linearIndependent_iff.mp hw (fun i => g (Sum.inl i)) h5
    intro i
    cases i with
    | inl i => exact h6 i
    | inr j => exact h3 j
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases i with
      | inl i =>
        have hwi : w i ∈ T.comap (b.restrictScalars V) := by
          rw [← hws]; exact Submodule.subset_span ⟨i, rfl⟩
        exact hwi
      | inr j => exact ht j
    · intro x hx
      have hax : al x ∈ T.map (al.restrictScalars V) := Submodule.mem_map_of_mem hx
      rw [← hus, Submodule.mem_span_range_iff_exists_fun] at hax
      obtain ⟨c, hc⟩ := hax
      have hyal : al (x - ∑ j, c j • t j) = 0 := by
        rw [map_sub, map_sum]
        simp only [LinearMap.map_smul_of_tower, hta']
        rw [hc, sub_self]
      obtain ⟨a, ha⟩ := (hex _).mp hyal
      have haK : a ∈ T.comap (b.restrictScalars V) := by
        show b a ∈ T
        rw [ha]
        exact T.sub_mem hx (T.sum_mem fun j _ => T.smul_mem (c j) (ht j))
      rw [← hws] at haK
      have hx_eq : x = b a + ∑ j, c j • t j := by rw [ha]; abel
      rw [hx_eq, Set.Sum.elim_range, Submodule.span_union]
      apply Submodule.add_mem_sup
      · have hr : Set.range (fun i => b (w i)) = (b.restrictScalars V) '' Set.range w := by
          rw [← Set.range_comp]; rfl
        rw [hr, Submodule.span_image]
        exact Submodule.mem_map_of_mem haK
      · exact Submodule.sum_mem _ fun j _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat
