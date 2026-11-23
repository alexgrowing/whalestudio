import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RamFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem ine_le_open (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Subgroup (G F Ω)) (hK : IsOpen (K : Set (G F Ω))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      Ine (F := F) A ≤ K := by
  obtain ⟨E, hE, hEK⟩ := (krullTopology_mem_nhds_one_iff F Ω (K : Set (G F Ω))).1 (hK.mem_nhds K.one_mem)
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosure E Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  obtain ⟨T, hT⟩ := (Base.ramFinite F F E Ω).1
  refine ⟨T, fun v hv A hA g hg => hEK ?_⟩
  have h := hT v hv A hA (show g ∈ Base.galOf F F Ω ⊓ Ine (F := F) A from ⟨fun x => g.commutes x, hg⟩)
  exact (IntermediateField.mem_fixingSubgroup_iff E g).2 fun x hx => h ⟨x, hx⟩

theorem UpperTheory.V.GC.levelS :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ), GLink l S K π →
    ∃ (S' : Finset (HeightOneSpectrum (𝓞 F))) (p : GS Ω (S' : Set (HeightOneSpectrum (𝓞 F))) →* Γ), S ⊆ S' ∧ Continuous p ∧ Function.Surjective p ∧ p.comp (toGS Ω _) = π ∧ ∀ A : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (A v) v) →
    p.ker = (Subgroup.normalClosure (⋃ q : {v // v ∈ S' ∧ v ∉ S}, (((Ine (F := F) (A q.1) ⊓ K).map (toGS Ω (S' : Set (HeightOneSpectrum (𝓞 F)))) : Subgroup _) : Set (GS Ω (S' : Set (HeightOneSpectrum (𝓞 F))))))).topologicalClosure := by
  intro F Ω _ _ _ _ _ l _ S K Γ _ _ _ _ _ _ π h
  classical
  obtain ⟨T, hT⟩ := ine_le_open F Ω K h.isOpen
  have hgen : ∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ g ∈ Ine (F := F) B, g ∈ K → π g = 1 := by
    intro v hv B hB g hg hgK
    rw [← MonoidHom.mem_ker, h.ker]
    refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
    simp only [Set.mem_iUnion]
    exact ⟨v, hv, B, hB, hg, hgK⟩
  have hcl : IsClosed (π.ker : Set (G F Ω)) := isClosed_singleton.preimage h.cont
  have hNS : NS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))) ≤ π.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl
    intro g hg
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, B, hB, hg⟩ := hg
    exact hgen v (fun h' => hv (Finset.mem_union_left _ h')) B hB g hg
      (hT v (fun h' => hv (Finset.mem_union_right _ h')) B hB hg)
  have hp : Continuous (QuotientGroup.lift _ π hNS) :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 h.cont
  refine ⟨S ∪ T, QuotientGroup.lift _ π hNS, Finset.subset_union_left, hp, fun y => ?_, rfl, fun A hA => ?_⟩
  · obtain ⟨g, rfl⟩ := h.onto y
    exact ⟨toGS Ω _ g, rfl⟩
  generalize hN : (Subgroup.normalClosure (⋃ q : {v // v ∈ S ∪ T ∧ v ∉ S}, (((Ine (F := F) (A q.1) ⊓ K).map
    (toGS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F)))) : Subgroup _) :
      Set (GS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))))))).topologicalClosure = N
  haveI hNn : N.Normal := by
    rw [← hN]
    exact Subgroup.is_normal_topologicalClosure _
  have hNc : IsClosed (N : Set (GS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))))) := by
    rw [← hN]
    exact Subgroup.isClosed_topologicalClosure _
  apply le_antisymm
  · have key : π.ker ≤ N.comap (toGS Ω _) := by
      rw [h.ker]
      refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
        (hNc.preimage QuotientGroup.continuous_mk)
      intro g hg
      simp only [Set.mem_iUnion] at hg
      obtain ⟨v, hv, B, hB, hg, hgK⟩ := hg
      by_cases hvS : v ∈ S ∪ T
      · obtain ⟨u, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA v) hB
        have hm : u⁻¹ * g * u ∈ N.comap (toGS Ω _) := by
          rw [← hN]
          refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
          exact Set.mem_iUnion.2 ⟨⟨v, hvS, hv⟩,
            Subgroup.mem_map_of_mem _ ⟨GlobalTheory.Cut.ShaBound.conj_mem_Ine' hg, h.normal.conj_mem' g hgK u⟩⟩
        have := (hNn.comap (toGS Ω _)).conj_mem _ hm u
        simpa [mul_assoc] using this
      · have h1 : toGS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))) g = 1 := by
          refine (QuotientGroup.eq_one_iff g).2 ?_
          refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
          simp only [Set.mem_iUnion]
          exact ⟨v, hvS, B, hB, hg⟩
        show toGS Ω _ g ∈ N
        rw [h1]
        exact N.one_mem
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact key hx
  · rw [← hN]
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) (isClosed_singleton.preimage hp)
    intro x hx
    obtain ⟨q, g, hg, rfl⟩ := Set.mem_iUnion.1 hx
    exact hgen q.1 q.2.2 _ (hA q.1) g hg.1 hg.2
