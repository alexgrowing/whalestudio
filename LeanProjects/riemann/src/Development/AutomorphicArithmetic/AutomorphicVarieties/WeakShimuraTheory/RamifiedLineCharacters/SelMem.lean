import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CocConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.selMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S₀ S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), S₀ ⊆ S →
      (∀ v ∈ S, v ∉ S₀ → TrivAt l (ρ.comp (toGS Ω _)) v) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ (m0 : M) (f : Z1 ρ),
        Submodule.Quotient.mk f ∈ gysSel S₀ S ρ Av m0 →
        (fun g => f.1 (toGS Ω _ g)) ∈ Zunr (ρ.comp (toGS Ω _)) S ∧
        (∀ v ∈ S₀, ∀ A, IsPlaceOver A v → ∃ m, ∀ g ∈ Dec (F := F) A, f.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m) ∧
        ∀ v : S, v.1 ∉ S₀ → ∀ g ∈ Ine (F := F) (Av v), f.1 (toGS Ω _ g) ∈ Submodule.span R {m0} := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ _ _ S₀ S ρ hS htriv Av hA m0 f hf
  have hZ : (fun g => f.1 (toGS Ω _ g)) ∈ Z1 (ρ.comp (toGS Ω _) : Representation R (G F Ω) M) :=
    ⟨f.2.1.comp QuotientGroup.continuous_mk, fun a b => by
      have := f.2.2 (toGS Ω _ a) (toGS Ω _ b)
      rw [← map_mul] at this
      exact this⟩
  have hloc := (mem_Sel _ _ _ _ _).1 hf
  refine ⟨⟨hZ, fun v hv A hAv g hg => ?_⟩, fun v hv A hAv => ?_, fun v hv g hg => ?_⟩
  · have h1 : f.1 1 = 0 := by
      have := f.2.2 1 1
      rw [one_mul, map_one] at this
      exact left_eq_add.1 this
    have h2 : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) g = 1 := by
      refine (QuotientGroup.eq_one_iff g).2 ?_
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hv, A, hAv, hg⟩
    show f.1 (toGS Ω _ g) = 0
    rw [h2, h1]
  · have h := hloc ⟨v, hS hv⟩
    rw [show gysL S₀ S ρ Av m0 ⟨v, hS hv⟩ = ⊥ from if_pos hv, Submodule.mem_bot] at h
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h)
    exact (UpperTheory.V.Ws.Gys.cocConj F Ω R M (ρ.comp (toGS Ω _)) _ hZ v (Av ⟨v, hS hv⟩) A (hA ⟨v, hS hv⟩) hAv).1
      ⟨m, fun g hg => hm ⟨g, hg⟩⟩
  · have h := hloc v
    rw [show gysL S₀ S ρ Av m0 v = ramLine (ρ.comp (locFam S Av v)) ((Ine (F := F) (Av v)).subgroupOf (Dec (F := F) (Av v))) m0
      from if_neg hv, mem_ramLine] at h
    obtain ⟨f', h1, h2⟩ := h
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 h2)
    have hd : g ∈ Dec (F := F) (Av v) := Ine_le_Dec _ hg
    have h3 := hm ⟨g, hd⟩
    have h4 : ρ (toGS Ω _ g) = 1 := (htriv v.1 v.2 hv (Av v) (hA v) g hd).1
    have h5 : f'.1 ⟨g, hd⟩ - f.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m := h3
    rw [h4, Module.End.one_apply, sub_self, sub_eq_zero] at h5
    rw [← h5]
    exact h1 ⟨g, hd⟩ hg
