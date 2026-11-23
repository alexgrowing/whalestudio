import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.IntScalars
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits groupCohomology

section Bridge

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A]

instance isDiscreteRep_uliftIntToIntRep : IsDiscreteRep (uliftIntToIntRep A) :=
  ⟨fun a => isOpen_stabilizer A a⟩

def cochainsULiftIntEquiv (n : ℕ) :
    (cochainsComplex A).X n ≃+ (cochainsComplex (uliftIntToIntRep A)).X n where
  toFun f := mkCochain _ (cochainOf A f) (isLocallyConstant_cochainOf f)
  invFun f := mkCochain A (cochainOf _ f) (isLocallyConstant_cochainOf f)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem cochainOf_cochainsULiftIntEquiv (n : ℕ) (f : (cochainsComplex A).X n) :
    cochainOf (uliftIntToIntRep A) (cochainsULiftIntEquiv A n f) = cochainOf A f :=
  rfl

theorem cochainsULiftIntEquiv_d (i : ℕ) (f : (cochainsComplex A).X i) :
    cochainsULiftIntEquiv A (i + 1) ((cochainsComplex A).d i (i + 1) f) =
      (cochainsComplex (uliftIntToIntRep A)).d i (i + 1) (cochainsULiftIntEquiv A i f) := by
  apply cochainOf_injective
  rw [cochainOf_cochainsULiftIntEquiv, cochainOf_d, cochainOf_d, cochainOf_cochainsULiftIntEquiv]
  have := inhomogeneousCochains_d_uliftIntToIntRep A i (i + 1) (cochainOf A f)
  rw [groupCohomology.inhomogeneousCochains.d_def, groupCohomology.inhomogeneousCochains.d_def] at this
  exact this.symm

end Bridge

section BridgeH

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A]

theorem cochainsULiftIntEquiv_d' (i j : ℕ) (f : (cochainsComplex A).X i) :
    cochainsULiftIntEquiv A j ((cochainsComplex A).d i j f) =
      (cochainsComplex (uliftIntToIntRep A)).d i j (cochainsULiftIntEquiv A i f) := by
  rcases eq_or_ne (i + 1) j with rfl | h
  · exact cochainsULiftIntEquiv_d A i f
  · have h' : ¬ (ComplexShape.up ℕ).Rel i j := h
    rw [HomologicalComplex.shape _ _ _ h', HomologicalComplex.shape _ _ _ h']
    rfl

theorem cochainsULiftIntEquiv_d_eq_zero_iff (i j : ℕ) (f : (cochainsComplex A).X i) :
    (cochainsComplex (uliftIntToIntRep A)).d i j (cochainsULiftIntEquiv A i f) = 0 ↔
      (cochainsComplex A).d i j f = 0 := by
  rw [← cochainsULiftIntEquiv_d', AddEquiv.map_eq_zero_iff]

theorem cochainsULiftIntEquiv_eq_d_iff (i j : ℕ) (f : (cochainsComplex A).X j)
    (z : (cochainsComplex (uliftIntToIntRep A)).X i) :
    (cochainsComplex (uliftIntToIntRep A)).d i j z = cochainsULiftIntEquiv A j f ↔
      (cochainsComplex A).d i j ((cochainsULiftIntEquiv A i).symm z) = f := by
  rw [← (cochainsULiftIntEquiv A j).injective.eq_iff, cochainsULiftIntEquiv_d',
    AddEquiv.apply_symm_apply]

noncomputable def kerULiftIntEquiv (n : ℕ) :
    LinearMap.ker ((cochainsComplex A).sc n).g.hom ≃+
      LinearMap.ker ((cochainsComplex (uliftIntToIntRep A)).sc n).g.hom where
  toFun x := ⟨cochainsULiftIntEquiv A n x.1,
    LinearMap.mem_ker.2 ((cochainsULiftIntEquiv_d_eq_zero_iff A n _ x.1).2 x.2)⟩
  invFun x := ⟨(cochainsULiftIntEquiv A n).symm x.1, LinearMap.mem_ker.2 ((cochainsULiftIntEquiv_d_eq_zero_iff A n _
      ((cochainsULiftIntEquiv A n).symm x.1)).1 x.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem kerULiftIntEquiv_mem_range_iff (n : ℕ) (x : LinearMap.ker ((cochainsComplex A).sc n).g.hom) :
    (∃ z, ((cochainsComplex (uliftIntToIntRep A)).sc n).moduleCatToCycles z = kerULiftIntEquiv A n x) ↔
      ∃ z, ((cochainsComplex A).sc n).moduleCatToCycles z = x := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨(cochainsULiftIntEquiv A _).symm z, Subtype.ext
      ((cochainsULiftIntEquiv_eq_d_iff A _ n x.1 z).1 (congrArg Subtype.val hz))⟩
  · rintro ⟨z, hz⟩
    refine ⟨cochainsULiftIntEquiv A _ z, Subtype.ext ?_⟩
    exact (cochainsULiftIntEquiv_eq_d_iff A _ n x.1 (cochainsULiftIntEquiv A _ z)).2
      (congrArg Subtype.val hz)

noncomputable def homologyDataULiftIntEquiv (n : ℕ) :
    ((cochainsComplex A).sc n).moduleCatLeftHomologyData.H ≃+
      ((cochainsComplex (uliftIntToIntRep A)).sc n).moduleCatLeftHomologyData.H where
  toEquiv := Quotient.congr (kerULiftIntEquiv A n).toEquiv fun a b =>
by
    refine QuotientAddGroup.leftRel_apply.trans (Iff.trans ?_ QuotientAddGroup.leftRel_apply.symm)
    exact (kerULiftIntEquiv_mem_range_iff A n (-a + b)).symm
  map_add' x y := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    rfl

end BridgeH

section BridgeCohomology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A]

noncomputable def cohomologyULiftIntAddEquiv (n : ℕ) :
    cohomology A n ≃+ cohomology (uliftIntToIntRep A) n :=
  ((cochainsComplex A).sc n).moduleCatHomologyIso.toLinearEquiv.toAddEquiv.trans
    ((homologyDataULiftIntEquiv A n).trans
      ((cochainsComplex (uliftIntToIntRep A)).sc n).moduleCatHomologyIso.toLinearEquiv.toAddEquiv.symm)

theorem cohomologyULiftIntAddEquiv_cohomologyπ {n : ℕ} (z : cocycles A n)
    (z' : cocycles (uliftIntToIntRep A) n)
    (h : cochainOf (uliftIntToIntRep A) (cocycleι (uliftIntToIntRep A) n z') =
      cochainOf A (cocycleι A n z)) :
    cohomologyULiftIntAddEquiv A n (cohomologyπ A n z) = cohomologyπ (uliftIntToIntRep A) n z' := by
  set S₁ := (cochainsComplex A).sc n
  set S₂ := (cochainsComplex (uliftIntToIntRep A)).sc n
  have h₁ : S₁.moduleCatHomologyIso.hom (cohomologyπ A n z) =
      S₁.moduleCatLeftHomologyData.π (S₁.moduleCatCyclesIso.hom z) :=
    ShortComplex.π_moduleCatCyclesIso_hom_apply S₁ z
  have h₂ : S₂.moduleCatHomologyIso.hom (cohomologyπ (uliftIntToIntRep A) n z') =
      S₂.moduleCatLeftHomologyData.π (S₂.moduleCatCyclesIso.hom z') :=
    ShortComplex.π_moduleCatCyclesIso_hom_apply S₂ z'
  have hk : kerULiftIntEquiv A n (S₁.moduleCatCyclesIso.hom z) = S₂.moduleCatCyclesIso.hom z' := by
    apply Subtype.ext
    have e₁ := ShortComplex.moduleCatCyclesIso_hom_i_apply S₁ z
    have e₂ := ShortComplex.moduleCatCyclesIso_hom_i_apply S₂ z'
    change cochainsULiftIntEquiv A n (S₁.moduleCatCyclesIso.hom z).1 = (S₂.moduleCatCyclesIso.hom z').1
    apply cochainOf_injective
    change cochainOf A (S₁.moduleCatCyclesIso.hom z).1 = cochainOf (uliftIntToIntRep A) (S₂.moduleCatCyclesIso.hom z').1
    rw [show (S₁.moduleCatCyclesIso.hom z).1 = S₁.iCycles z from e₁,
      show (S₂.moduleCatCyclesIso.hom z').1 = S₂.iCycles z' from e₂]
    exact h.symm
  apply S₂.moduleCatHomologyIso.toLinearEquiv.toAddEquiv.injective
  change S₂.moduleCatHomologyIso.hom (S₂.moduleCatHomologyIso.inv
    (homologyDataULiftIntEquiv A n (S₁.moduleCatHomologyIso.hom (cohomologyπ A n z)))) = _
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply, h₁]
  change S₂.moduleCatLeftHomologyData.π (kerULiftIntEquiv A n (S₁.moduleCatCyclesIso.hom z)) = _
  rw [hk]
  exact h₂.symm

end BridgeCohomology

section BridgeMaps

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A]

noncomputable def cocyclesULiftInt {n : ℕ} (z : cocycles A n) : cocycles (uliftIntToIntRep A) n :=
  (cochainsComplex (uliftIntToIntRep A)).cyclesMk (cochainsULiftIntEquiv A n (cocycleι A n z)) (n + 1)
    (by simp) ((cochainsULiftIntEquiv_d_eq_zero_iff A n (n + 1) _).2
      (congrArg (fun ψ => ψ.hom z) ((cochainsComplex A).iCycles_d n (n + 1))))

@[simp]
theorem cochainOf_cocycleι_cocyclesULiftInt {n : ℕ} (z : cocycles A n) :
    cochainOf (uliftIntToIntRep A) (cocycleι (uliftIntToIntRep A) n (cocyclesULiftInt A z)) =
      cochainOf A (cocycleι A n z) :=
  congrArg (cochainOf (uliftIntToIntRep A)) ((cochainsComplex (uliftIntToIntRep A)).i_cyclesMk _ _ _ _)

theorem cohomologyULiftIntAddEquiv_cohomologyπ' {n : ℕ} (z : cocycles A n) :
    cohomologyULiftIntAddEquiv A n (cohomologyπ A n z) =
      cohomologyπ (uliftIntToIntRep A) n (cocyclesULiftInt A z) :=
  cohomologyULiftIntAddEquiv_cohomologyπ A z _ (cochainOf_cocycleι_cocyclesULiftInt A z)

theorem cohomologyULiftIntAddEquiv_cohomologyMapAlong {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {B : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep B] (φ : H →* G)
    (hφ : Continuous φ) (f : Rep.res φ A ⟶ B)
    (f' : Rep.res φ (uliftIntToIntRep A) ⟶ uliftIntToIntRep B) (hf : ∀ a, f'.hom a = f.hom a)
    (n : ℕ) (x : cohomology A n) :
    cohomologyULiftIntAddEquiv B n (cohomologyMapAlong φ hφ f n x) =
      cohomologyMapAlong φ hφ f' n (cohomologyULiftIntAddEquiv A n x) := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective A n x
  rw [cohomologyπ_cohomologyMapAlong_apply, cohomologyULiftIntAddEquiv_cohomologyπ' A z,
    cohomologyπ_cohomologyMapAlong_apply]
  refine cohomologyULiftIntAddEquiv_cohomologyπ B _ _ ?_
  rw [cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesMapAlong]
  funext v
  rw [cochainOf_cocycleι_cocyclesULiftInt]
  exact hf _

end BridgeMaps

end GroundTheory.ProfCoh
