import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.DiagEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.WPresEx

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia UpperTheory.V.Pr

private theorem rz_off {O A : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    (F : Frame O G Γ ι) [CommRing A] [Algebra O A] (g : Γ) {a b : Fin 3} (h : wt a b ≠ 0) :
    (F.rz A g).mat a b = 0 := by
  have hab : a ≠ b := by
    rintro rfl
    simp [wt] at h
  simp [Frame.rz, r0, GG.mat, GG.map, tor_val, Matrix.diagonal_apply_ne _ hab]

private theorem eq_of_wt {a b : Fin 3} (h : wt a b = 0) : a = b := by
  simp only [wt, wt1] at h
  apply Fin.ext
  omega

theorem UpperTheory.V.UnitaryThreeInertia.universal_diagonal_of_triangular_points :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.Cl1 → ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    (∀ (A : Type) [CommRing A] [Algebra O A] [IsCD O A], (∀ a ∈ maximalIdeal O, algebraMap O A a = 0) → ∀ r : Γ →* GG 3 A, F.IsPt g₁ r → Upper F.η r ∨ Lower F.η r) →
      Module.Finite O (wpart O u 0) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hOk hCl g₁ hg₁ R _ _ _ u hu htri
  obtain ⟨W, hW, -⟩ := exists_adapted F hOk g₁ hg₁ u hu
  rw [← hW.part 0]
  have key : ∀ {A : Type} [CommRing A] [Algebra O A] (f : R →ₐ[O] A) (g : Γ) (a b : Fin 3),
      f ((u g).mat a b - ((F.rz R) g).mat a b) = ((push f u) g).mat a b - ((F.rz A) g).mat a b := by
    intro A _ _ f g a b
    simp [push, Frame.rz, GG.mat, GG.map]
  refine finCrit O R W ?_ ?_
  · intro i
    obtain ⟨g, a, b, -, -, hz⟩ := hW.var i
    rw [hz]
    have h1 := hu.pt.red g a b
    have h2 : ((F.rz R) g).mat = ((r0 F.η F.Ψ) g).mat.map ⇑(algebraMap O R) := by
      simp [Frame.rz, GG.mat, GG.map]
    rw [h2]
    simpa using h1
  · intro A _ _ _ f hf hA
    letI iLA : IsLocalRing A := inferInstance
    haveI iDA : IsDomain A := inferInstance
    haveI iNA : IsNoetherianRing A := inferInstance
    haveI : IsLocalHom (algebraMap O A) := IsCD.isLocalHom
    haveI := hf
    have hpt : F.IsPt g₁ (push f u) := isPt_push F f g₁ u hu.pt
    have htr := htri A hA (push f u) hpt
    have hdiag : ∀ (g : Γ) (a : Fin 3), ((push f u) g).mat a a = ((F.rz A) g).mat a a :=
      @diag_eq_of_tri O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hOk hCl g₁ hg₁ A _ iDA iLA iNA _ _
        (push f u) hpt htr
    refine ⟨?_, ?_⟩
    · intro i hi
      obtain ⟨g, a, b, -, hw, hz⟩ := hW.var i
      rw [hi] at hw
      obtain rfl := eq_of_wt hw.symm
      rw [hz, key, hdiag, sub_self]
    · rcases htr with hU | hL
      · left
        intro i hi
        obtain ⟨g, a, b, hg, hw, hz⟩ := hW.var i
        rw [hw] at hi
        rw [hz, key, hU g (MonoidHom.mem_ker.mpr hg) a b hi, rz_off (A := A) F g hi.ne, sub_self]
      · right
        intro i hi
        obtain ⟨g, a, b, hg, hw, hz⟩ := hW.var i
        rw [hw] at hi
        rw [hz, key, hL g (MonoidHom.mem_ker.mpr hg) a b hi, rz_off (A := A) F g hi.ne', sub_self]
