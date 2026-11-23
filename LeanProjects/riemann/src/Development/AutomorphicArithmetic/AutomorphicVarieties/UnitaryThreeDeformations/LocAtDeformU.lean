import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.locAt_deform_u :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f : R), (∀ x ∈ maximalIdeal R, x * f = 0) → f ∈ maximalIdeal R → ∀ (j : ℤ) (v : ι), v ∉ F.Tb →
      ∀ (r r₂ : F.D v →* GG 3 R) (z : F.D v → Gb (ResidueField O) j) (γ : F.D v → Matrix (Fin 3) (Fin 3) R), Red (F.ηv v) (F.Ψv v) r → F.LocAt v r →
      z ∈ F.ZL j v → (∀ g a b, ∃ o : O, residue O o = (z g).val a b ∧ γ g a b = o • f) → IsDeform r γ r₂ → F.LocAt v r₂ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F _ _ R _ _ _ f hf _ j v hv r r₂ z γ _ hr hz hγ hd
  have hvl : v ≠ F.vl := fun h => hv (h ▸ Set.mem_insert _ _)
  refine ⟨fun h => absurd h hvl, fun h => absurd (Set.mem_insert_of_mem _ h) hv, fun _ s hs => ?_⟩
  have h1 : r s = 1 := hr.2.2 hv s hs
  have hz0 : z s = 0 := hz.2.1 hvl s hs
  have hγ0 : γ s = 0 := by
    ext a b
    obtain ⟨o, ho, e⟩ := hγ s a b
    rw [hz0] at ho
    have ho' : o ∈ maximalIdeal O := (residue_eq_zero_iff o).1 ho
    have hm : algebraMap O R o ∈ maximalIdeal R := fun h => ho' (IsLocalHom.map_nonunit o h)
    rw [e, Algebra.smul_def]
    exact hf _ hm
  obtain ⟨e1, e2⟩ := hd s
  rw [h1] at e1
  rw [h1, hγ0, add_zero, one_mul] at e2
  exact SemidirectProduct.ext (Units.ext e2) e1
