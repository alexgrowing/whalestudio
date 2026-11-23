import Formalism.FilteredPoleLength.ReducedBasisBounds.BetaSesquilinearity
import Formalism.LogFactorialIndices.LogProductFormula
import Lemmata.MiscLemmasO.Imports

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem exists_smul_mem_of_mem_span_alt (O K V : Type) [CommRing O] [IsDomain O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (M : Submodule O V) (v : V) (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ c : O, c ≠ 0 ∧ c • v ∈ M := by
  first | exact Bl.SecondBlockLemmaP.goal1 .. | (apply Bl.SecondBlockLemmaP.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaP.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaP.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaP.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaP.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M v hv | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M v | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V | exact @Bl.SecondBlockLemmaP.goal1 O K | exact @Bl.SecondBlockLemmaP.goal1 O

theorem exists_adapted_basis_alt (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    (M : Submodule O V) (V' : Submodule K V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (s : Set (Fin (finrank K V))),
      M ≤ Submodule.span O (Set.range b) ∧ (∀ i ∈ s, b i ∈ M ∧ b i ∈ V') ∧
        V' ≤ Submodule.span K (b '' s) := by
  obtain ⟨b0, hb0⟩ := Formalism.LatticeIndexTer.latBasis O K V M hM
  have hli0 : LinearIndependent O b0 :=
    (LinearIndependent.iff_fractionRing O K).mpr b0.linearIndependent
  let bO : Basis (Fin (finrank K V)) O M :=
    (Basis.span hli0).map (LinearEquiv.ofEq _ _ hb0.symm)
  obtain ⟨n, bM, bN, f, a, snf⟩ :=
    Submodule.smithNormalForm bO ((V'.restrictScalars O).comap M.subtype)
  have hliO : LinearIndependent O (fun i => (bM i : V)) :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hliK : LinearIndependent K (fun i => (bM i : V)) :=
    (LinearIndependent.iff_fractionRing O K).mp hliO
  have hspanO : M ≤ Submodule.span O (Set.range (fun i => (bM i : V))) := by
    intro m hm
    have h1 : (⟨m, hm⟩ : M) ∈ Submodule.span O (Set.range bM) := by
      rw [bM.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := M.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  have hspanK : ⊤ ≤ Submodule.span K (Set.range (fun i => (bM i : V))) := by
    rw [← hM.2]
    apply Submodule.span_le.mpr
    intro m hm
    exact Submodule.span_le_restrictScalars O K _ (hspanO hm)
  let b : Basis (Fin (finrank K V)) K V := Basis.mk hliK hspanK
  have hb : ∀ i, b i = (bM i : V) := fun i => by simp [b]
  have hrange : Set.range b = Set.range (fun i => (bM i : V)) := by
    ext x; simp [hb]
  refine ⟨b, Set.range f, ?_, ?_, ?_⟩
  · rw [hrange]; exact hspanO
  · rintro _ ⟨k, rfl⟩
    rw [hb]
    refine ⟨(bM (f k)).2, ?_⟩
    have hmem : ((bN k : M) : V) ∈ V' := (bN k).2
    rw [snf k] at hmem
    have ha : a k ≠ 0 := by
      intro h0
      have : (bN k : M) = 0 := by rw [snf k, h0, zero_smul]
      exact bN.ne_zero k (Subtype.ext this)
    have haK : algebraMap O K (a k) ≠ 0 := by
      simpa using (IsFractionRing.injective O K).ne ha
    have h3 : algebraMap O K (a k) • ((bM (f k) : M) : V) ∈ V' := by
      rw [algebraMap_smul]; simpa using hmem
    exact (V'.smul_mem_iff haK).mp h3
  · intro v hv
    have hv' : v ∈ Submodule.span K (M : Set V) := by rw [hM.2]; trivial
    obtain ⟨c, hc, hcv⟩ := exists_smul_mem_of_mem_span_alt O K V M v hv'
    have hcK : algebraMap O K c ≠ 0 := by
      simpa using (IsFractionRing.injective O K).ne hc
    have hcV : c • v ∈ V' := by
      rw [← algebraMap_smul K c]; exact V'.smul_mem _ hv
    let w : ((V'.restrictScalars O).comap M.subtype : Submodule O M) := ⟨⟨c • v, hcv⟩, hcV⟩
    have hw : w ∈ Submodule.span O (Set.range bN) := by rw [bN.span_eq]; trivial
    have key : ∀ u ∈ Submodule.span O (Set.range bN),
        ((u : M) : V) ∈ Submodule.span K (b '' Set.range f) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rw [snf k]
        have : ((a k • bM (f k) : M) : V) = algebraMap O K (a k) • b (f k) := by
          rw [hb, algebraMap_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f k, ⟨k, rfl⟩, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        have : (((r • x : _) : M) : V) = algebraMap O K r • ((x : M) : V) := by
          rw [algebraMap_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ _ hx
    have h4 : algebraMap O K c • v ∈ Submodule.span K (b '' Set.range f) := by
      rw [algebraMap_smul]; exact key w hw
    exact (Submodule.smul_mem_iff _ hcK).mp h4

theorem inter_baseChange_lattice : SpanImageInf := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj M V' hM
  obtain ⟨b, s, hMb, hs, hV'⟩ := exists_adapted_basis_alt O K V M V' hM
  let b' : Basis (Fin (finrank K V)) K' V₁ := hj.basis b
  have hb' : ∀ i, b' i = j (b i) := fun i => hj.basis_apply b i
  have hjO : ∀ (o : O) (v : V), j (o • v) = algebraMap O O' o • j v := by
    intro o v
    rw [← algebraMap_smul K o v, map_smul, ← algebraMap_smul K' (algebraMap O K o) (j v),
      ← algebraMap_smul K' (algebraMap O O' o) (j v), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hjK : ∀ (k : K) (v : V), j (k • v) = algebraMap K K' k • j v := by
    intro k v
    rw [map_smul, algebraMap_smul]
  have hO : ∀ y ∈ Submodule.span O (Set.range b), j y ∈ Submodule.span O' (Set.range b') := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, hb' i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hjO]; exact Submodule.smul_mem _ _ hy
  have hK : ∀ y ∈ Submodule.span K (b '' s), j y ∈ Submodule.span K' (b' '' s) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, hi, hb' i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hjK]; exact Submodule.smul_mem _ _ hy
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have h1 : x ∈ Submodule.span O' (Set.range b') := by
      refine (Submodule.span_le.mpr ?_) hx1
      rintro _ ⟨m, hm, rfl⟩
      exact hO m (hMb hm)
    have h2 : x ∈ Submodule.span K' (b' '' s) := by
      refine (Submodule.span_le.mpr ?_) hx2
      rintro _ ⟨m, hm, rfl⟩
      exact hK m (hV' hm)
    rw [b'.mem_span_iff_repr_mem O'] at h1
    rw [b'.mem_span_image] at h2
    rw [← b'.sum_repr x]
    refine Submodule.sum_mem _ ?_
    intro i _
    by_cases hi : i ∈ s
    · obtain ⟨c, hc⟩ := h1 i
      rw [← hc, algebraMap_smul, hb']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, hs i hi, rfl⟩)
    · have : b'.repr x i = 0 := by
        by_contra h0
        exact hi (h2 (by simpa using h0))
      rw [this, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, ⟨hm1, hm2⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨m, hm1, rfl⟩, Submodule.subset_span ⟨m, hm2, rfl⟩⟩

end Formalism.LatticeBaseChangeAlt
