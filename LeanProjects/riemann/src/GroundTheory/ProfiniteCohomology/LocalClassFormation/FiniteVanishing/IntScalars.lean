import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits groupCohomology

variable {Γ : Type} [Group Γ]

abbrev uliftIntToIntRep (M : Rep.{0} (ULift.{0} ℤ) Γ) : Rep.{0} ℤ Γ :=
  Rep.of (X := M.V)
    { toFun := fun g => (M.ρ g).toAddMonoidHom.toIntLinearMap
      map_one' := by
        ext x
        simp
      map_mul' := fun g h => by
        ext x
        simp [Module.End.mul_apply] }

theorem inhomogeneousCochains_d_uliftIntToIntRep (M : Rep.{0} (ULift.{0} ℤ) Γ) (i j : ℕ)
    (x : (Fin i → Γ) → M.V) :
    ((inhomogeneousCochains (uliftIntToIntRep M)).d i j).hom x =
      ((inhomogeneousCochains M).d i j).hom x := by
  rcases eq_or_ne (i + 1) j with rfl | h
  · rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def]
    funext g
    have hs : ∀ k : ℕ, ((-1 : ULift.{0} ℤ) ^ k) = (((-1 : ℤ) ^ k : ℤ) : ULift.{0} ℤ) := fun k => by
      simp
    simp only [inhomogeneousCochains.d_hom_apply, hs, Int.cast_smul_eq_zsmul]
    rfl
  · have h' : ¬ (ComplexShape.up ℕ).Rel i j := h
    rw [HomologicalComplex.shape _ _ _ h', HomologicalComplex.shape _ _ _ h']
    rfl

def cochainsScULiftIntIso (M : Rep.{0} (ULift.{0} ℤ) Γ) (n : ℕ) :
    (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.obj ((inhomogeneousCochains M).sc n) ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.obj
        ((inhomogeneousCochains (uliftIntToIntRep M)).sc n) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      ext x
      exact inhomogeneousCochains_d_uliftIntToIntRep M _ _ x)
    (by
      ext x
      exact inhomogeneousCochains_d_uliftIntToIntRep M _ _ x)

def forget₂HomologyIso {S₁ : ShortComplex (ModuleCat.{0} (ULift.{0} ℤ))}
    {S₂ : ShortComplex (ModuleCat.{0} ℤ)}
    (σ : (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.obj S₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).obj S₁ ≅
      (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{0} ℤ) Ab).obj S₂ :=
  ((ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab)).app S₁).symm ≪≫
    (ShortComplex.homologyFunctor Ab).mapIso σ ≪≫
    (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{0} ℤ) Ab)).app S₂

theorem forget₂_homologyMap_comp_forget₂HomologyIso
    {S₁ T₁ : ShortComplex (ModuleCat.{0} (ULift.{0} ℤ))} {S₂ T₂ : ShortComplex (ModuleCat.{0} ℤ)}
    (φ₁ : S₁ ⟶ T₁) (φ₂ : S₂ ⟶ T₂)
    (σS : (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.obj S₂)
    (σT : (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.obj T₁ ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.obj T₂)
    (h : (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.map φ₁ ≫ σT.hom =
      σS.hom ≫ (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.map φ₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).map φ₁ ≫
        (forget₂HomologyIso σT).hom =
      (forget₂HomologyIso σS).hom ≫
        (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{0} ℤ) Ab).map φ₂ := by
  have n1 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab)).inv.naturality φ₁
  have n2 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{0} ℤ) Ab)).hom.naturality φ₂
  have n3 : ((forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex ⋙
        ShortComplex.homologyFunctor Ab).map φ₁ ≫ (ShortComplex.homologyFunctor Ab).map σT.hom =
      (ShortComplex.homologyFunctor Ab).map σS.hom ≫
        ((forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex ⋙ ShortComplex.homologyFunctor Ab).map φ₂ := by
    rw [Functor.comp_map, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp, h]
  simp only [forget₂HomologyIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  slice_lhs 1 2 => rw [n1]
  slice_lhs 2 3 => rw [n3]
  slice_lhs 3 4 => rw [n2]

def groupCohomologyULiftIntIso (M : Rep.{0} (ULift.{0} ℤ) Γ) (n : ℕ) :
    (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).obj (groupCohomology M n) ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).obj (groupCohomology (uliftIntToIntRep M) n) :=
  forget₂HomologyIso (cochainsScULiftIntIso M n)

def groupCohomologyULiftIntAddEquiv (M : Rep.{0} (ULift.{0} ℤ) Γ) (n : ℕ) :
    groupCohomology M n ≃+ groupCohomology (uliftIntToIntRep M) n :=
  (groupCohomologyULiftIntIso M n).addCommGroupIsoToAddEquiv

theorem groupCohomologyULiftIntAddEquiv_map_subtype (M : Rep.{0} (ULift.{0} ℤ) Γ) (S : Subgroup Γ)
    (n : ℕ) (x : groupCohomology M n) :
    groupCohomologyULiftIntAddEquiv (Rep.res S.subtype M) n
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) n).hom x) =
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M))) n).hom
        (groupCohomologyULiftIntAddEquiv M n x) := by
  have key := forget₂_homologyMap_comp_forget₂HomologyIso
    ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (cochainsMap S.subtype (𝟙 (Rep.res S.subtype M))))
    ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (cochainsMap S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M)))))
    (cochainsScULiftIntIso M n) (cochainsScULiftIntIso (Rep.res S.subtype M) n) (by
      ext x <;> rfl)
  exact congrArg (fun f => f.hom x) key

end GroundTheory.ProfCoh
