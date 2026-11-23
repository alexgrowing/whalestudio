import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.ConeDefs
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.Pairing
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section ProdHomology

variable {k : Type u} [CommRing k] (M N : CochainComplex (ModuleCat.{u} k) ℕ)

noncomputable def prodHomologyToProd (n : ℕ) :
    (prodComplex M N).homology n ⟶ ModuleCat.of k (M.homology n × N.homology n) :=
  ModuleCat.ofHom ((HomologicalComplex.homologyMap (prodFst M N) n).hom.prod
    (HomologicalComplex.homologyMap (prodSnd M N) n).hom)

theorem prodHomologyToProd_bijective (n : ℕ) :
    Function.Bijective (prodHomologyToProd M N n).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨c, rfl⟩ :=
      (ModuleCat.epi_iff_surjective ((prodComplex M N).homologyπ n)).1 inferInstance h
    have h1 : ∃ y : M.X ((ComplexShape.up ℕ).prev n), (M.d _ n).hom y =
        (M.iCycles n).hom ((HomologicalComplex.cyclesMap (prodFst M N) n).hom c) := by
      refine (homologyπ_eq_zero_iff _ _).1 ?_
      rw [← homologyMap_homologyπ_apply]
      exact congrArg Prod.fst hh
    have h2 : ∃ y : N.X ((ComplexShape.up ℕ).prev n), (N.d _ n).hom y =
        (N.iCycles n).hom ((HomologicalComplex.cyclesMap (prodSnd M N) n).hom c) := by
      refine (homologyπ_eq_zero_iff _ _).1 ?_
      rw [← homologyMap_homologyπ_apply]
      exact congrArg Prod.snd hh
    obtain ⟨y1, hy1⟩ := h1
    obtain ⟨y2, hy2⟩ := h2
    refine (homologyπ_eq_zero_iff _ c).2 ⟨show (prodComplex M N).X _ from (y1, y2), ?_⟩
    rw [prodComplex_d_hom_apply', hy1, hy2, iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
    rfl
  · rintro ⟨h1, h2⟩
    obtain ⟨c1, hc1⟩ := (ModuleCat.epi_iff_surjective (M.homologyπ n)).1 inferInstance h1
    obtain ⟨c2, hc2⟩ := (ModuleCat.epi_iff_surjective (N.homologyπ n)).1 inferInstance h2
    obtain ⟨c', hc'⟩ := exists_iCycles_eq (K := prodComplex M N)
      (show (prodComplex M N).X n from ((M.iCycles n).hom c1, (N.iCycles n).hom c2)) (by
        rw [CochainComplex.next, prodComplex_d_hom_apply]
        exact Prod.ext (iCycles_d_apply _ n (n + 1) c1) (iCycles_d_apply _ n (n + 1) c2))
    refine ⟨((prodComplex M N).homologyπ n).hom c', Prod.ext ?_ ?_⟩
    · change (HomologicalComplex.homologyMap (prodFst M N) n).hom _ = h1
      rw [homologyMap_homologyπ_apply, ← hc1]
      congr 1
      apply (ModuleCat.mono_iff_injective (M.iCycles n)).1 inferInstance
      rw [iCycles_cyclesMap_apply, hc']
      rfl
    · change (HomologicalComplex.homologyMap (prodSnd M N) n).hom _ = h2
      rw [homologyMap_homologyπ_apply, ← hc2]
      congr 1
      apply (ModuleCat.mono_iff_injective (N.iCycles n)).1 inferInstance
      rw [iCycles_cyclesMap_apply, hc']
      rfl

noncomputable def prodHomologyIso (n : ℕ) :
    (prodComplex M N).homology n ≅ ModuleCat.of k (M.homology n × N.homology n) :=
  (LinearEquiv.ofBijective (prodHomologyToProd M N n).hom
    (prodHomologyToProd_bijective M N n)).toModuleIso

theorem isIso_homologyMap_prodFst {n : ℕ} (hN : IsZero (N.homology n)) :
    IsIso (HomologicalComplex.homologyMap (prodFst M N) n) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hb := prodHomologyToProd_bijective M N n
  constructor
  · intro x y hxy
    refine hb.1 (Prod.ext hxy ?_)
    exact (ModuleCat.subsingleton_of_isZero hN).elim _ _
  · intro m
    obtain ⟨h, hh⟩ := hb.2 (m, 0)
    exact ⟨h, congrArg Prod.fst hh⟩

end ProdHomology

section DegZeroHomology

variable {k : Type u} [CommRing k] (E : ModuleCat.{u} k)

theorem isZero_degZeroComplex_homology_succ (n : ℕ) :
    IsZero ((degZeroComplex E).homology (n + 1)) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (ModuleCat.isZero_of_subsingleton ((degZeroComplex E).X (n + 1)))

noncomputable def degZeroHomologyIso : (degZeroComplex E).homology 0 ≅ E :=
  (degZeroComplex E).isoHomologyπ₀.symm ≪≫
    (degZeroComplex E).iCyclesIso 0 1 (by simp) (degZeroComplex_d E 0 1)

theorem degZeroHomologyIso_hom_homologyπ (c : (degZeroComplex E).cycles 0) :
    (degZeroHomologyIso E).hom.hom (((degZeroComplex E).homologyπ 0).hom c) =
      ((degZeroComplex E).iCycles 0).hom c := by
  change ((degZeroComplex E).iCycles 0).hom
      ((degZeroComplex E).isoHomologyπ₀.inv.hom (((degZeroComplex E).homologyπ 0).hom c)) = _
  rw [hom_apply_hom_apply_of_comp_eq
    (HomologicalComplex.isoHomologyπ_hom_inv_id (degZeroComplex E) _ 0 rfl (by simp)) c]
  rfl

end DegZeroHomology

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w)

section Terms

noncomputable def tateLocalCohomologyIso (n : ℕ) :
    (tateLocalComplex Aᵥ Aᵣ).homology n ≅
      ModuleCat.of k ((∀ v, cohomology (Aᵥ v) n) × (∀ w, cohomology (Aᵣ w) n)) :=
  prodHomologyIso _ _ n ≪≫
    ((localCohomologyIso Aᵥ n).toLinearEquiv.prodCongr (localCohomologyIso Aᵣ n).toLinearEquiv).toModuleIso

omit [∀ w, Fintype (F w)] in
theorem tateLocalCohomologyIso_hom_apply (n : ℕ) (z : (tateLocalComplex Aᵥ Aᵣ).homology n) :
    (tateLocalCohomologyIso Aᵥ Aᵣ n).hom.hom z =
      ((localCohomologyIso Aᵥ n).hom.hom ((HomologicalComplex.homologyMap (prodFst _ _) n).hom z),
        (localCohomologyIso Aᵣ n).hom.hom ((HomologicalComplex.homologyMap (prodSnd _ _) n).hom z)) :=
  rfl

noncomputable def tateGlobalCohomologyIso (n : ℕ) :
    (tateGlobalComplex A Aᵣ).homology (n + 1) ≅ cohomology A (n + 1) :=
  @asIso _ _ _ _ (HomologicalComplex.homologyMap (prodFst _ _) (n + 1))
    (isIso_homologyMap_prodFst (cochainsComplex A) (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w)))
      (isZero_degZeroComplex_homology_succ _ n))

omit [∀ w, TopologicalSpace (F w)] [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)]
  [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateGlobalCohomologyIso_hom (n : ℕ) :
    (tateGlobalCohomologyIso A Aᵣ n).hom =
      HomologicalComplex.homologyMap (prodFst _ _) (n + 1) :=
  rfl

noncomputable def tateGlobalCohomologyZeroIso :
    (tateGlobalComplex A Aᵣ).homology 0 ≅ ModuleCat.of k (cohomology A 0 × ∀ w, Aᵣ w) :=
  prodHomologyIso _ _ 0 ≪≫
    ((LinearEquiv.refl k (cohomology A 0)).prodCongr
      (degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))).toLinearEquiv).toModuleIso

omit [∀ w, TopologicalSpace (F w)] [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)]
  [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateGlobalCohomologyZeroIso_hom_apply (z : (tateGlobalComplex A Aᵣ).homology 0) :
    (tateGlobalCohomologyZeroIso A Aᵣ).hom.hom z =
      ((HomologicalComplex.homologyMap (prodFst _ _) 0).hom z,
        (degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))).hom.hom
          ((HomologicalComplex.homologyMap (prodSnd _ _) 0).hom z)) :=
  rfl

theorem tateCompactRes_prodFst :
    tateCompactRes φ ψ A Aᵥ a Aᵣ ar ≫ prodFst _ _ = prodFst _ _ ≫ localRes φ A Aᵥ a :=
  prodLift_prodFst _ _

theorem tateCompactRes_prodSnd :
    tateCompactRes φ ψ A Aᵥ a Aᵣ ar ≫ prodSnd _ _ =
      prodFst _ _ ≫ localRes ψ A Aᵣ ar + prodSnd _ _ ≫ normCochains Aᵣ :=
  prodLift_prodSnd _ _

noncomputable def tateGlobalToLocal (n : ℕ) :
    cohomology A n ⟶ ModuleCat.of k ((∀ v, cohomology (Aᵥ v) n) × (∀ w, cohomology (Aᵣ w) n)) :=
  ModuleCat.ofHom ((globalToLocal φ A Aᵥ a n).hom.prod (globalToLocal ψ A Aᵣ ar n).hom)

omit [∀ w, Fintype (F w)] in
theorem tateGlobalToLocal_hom_apply (n : ℕ) (x : cohomology A n) :
    (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar n).hom x =
      ((globalToLocal φ A Aᵥ a n).hom x, (globalToLocal ψ A Aᵣ ar n).hom x) :=
  rfl

theorem homologyMap_tateCompactRes_succ (n : ℕ) :
    HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) (n + 1) ≫
        (tateLocalCohomologyIso Aᵥ Aᵣ (n + 1)).hom =
      (tateGlobalCohomologyIso A Aᵣ n).hom ≫ tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1) := by
  have e1 : HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) (n + 1) ≫
      HomologicalComplex.homologyMap (prodFst _ _) (n + 1) ≫ (localCohomologyIso Aᵥ (n + 1)).hom =
      (tateGlobalCohomologyIso A Aᵣ n).hom ≫ globalToLocal φ A Aᵥ a (n + 1) := by
    rw [← HomologicalComplex.homologyMap_comp_assoc, tateCompactRes_prodFst,
      HomologicalComplex.homologyMap_comp_assoc, homologyMap_localRes_localCohomologyIso_hom]
    rfl
  have hz : HomologicalComplex.homologyMap
      (prodSnd (cochainsComplex A) (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w)))) (n + 1) = 0 :=
    (isZero_degZeroComplex_homology_succ _ n).eq_of_tgt _ _
  have e2 : HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) (n + 1) ≫
      HomologicalComplex.homologyMap (prodSnd _ _) (n + 1) ≫ (localCohomologyIso Aᵣ (n + 1)).hom =
      (tateGlobalCohomologyIso A Aᵣ n).hom ≫ globalToLocal ψ A Aᵣ ar (n + 1) := by
    rw [← HomologicalComplex.homologyMap_comp_assoc, tateCompactRes_prodSnd,
      HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp, hz, zero_comp, add_zero, Category.assoc,
      homologyMap_localRes_localCohomologyIso_hom]
    rfl
  refine ModuleCat.hom_ext (LinearMap.ext fun z => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_of_comp_eq e1 z
  · exact hom_apply_hom_apply_of_comp_eq e2 z

end Terms

section Sequence

noncomputable def tateToGlobal (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar n ⟶ cohomology A n :=
  HomologicalComplex.homologyMap
    (mappingCoconeNat.fst (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) ≫ prodFst _ _) n

noncomputable def tateLocalToCompact (n : ℕ) :
    ModuleCat.of k ((∀ v, cohomology (Aᵥ v) n) × (∀ w, cohomology (Aᵣ w) n)) ⟶
      tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 1) :=
  (tateLocalCohomologyIso Aᵥ Aᵣ n).inv ≫
    mappingCoconeNat.homologyδ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) n

theorem tateToGlobal_succ (n : ℕ) :
    tateToGlobal φ ψ A Aᵥ a Aᵣ ar (n + 1) =
      HomologicalComplex.homologyMap (mappingCoconeNat.fst (tateCompactRes φ ψ A Aᵥ a Aᵣ ar))
        (n + 1) ≫ (tateGlobalCohomologyIso A Aᵣ n).hom :=
  HomologicalComplex.homologyMap_comp _ _ _

@[reassoc (attr := simp)]
theorem tateToGlobal_tateGlobalToLocal (n : ℕ) :
    tateToGlobal φ ψ A Aᵥ a Aᵣ ar (n + 1) ≫ tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1) = 0 := by
  refine (congrArg (· ≫ tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1))
    (tateToGlobal_succ φ ψ A Aᵥ a Aᵣ ar n)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (homologyMap_tateCompactRes_succ φ ψ A Aᵥ a Aᵣ ar n).symm).trans ?_
  exact (mappingCoconeNat.homologyMap_fst_homologyMap_assoc _ _ _).trans zero_comp

@[reassoc (attr := simp)]
theorem tateGlobalToLocal_tateLocalToCompact (n : ℕ) :
    tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1) ≫ tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar (n + 1) = 0 := by
  rw [← cancel_epi (tateGlobalCohomologyIso A Aᵣ n).hom, comp_zero, ← Category.assoc,
    ← homologyMap_tateCompactRes_succ]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)).trans
    (mappingCoconeNat.homologyMap_homologyδ _ _))

@[reassoc (attr := simp)]
theorem tateLocalToCompact_tateToGlobal (n : ℕ) :
    tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n ≫ tateToGlobal φ ψ A Aᵥ a Aᵣ ar (n + 1) = 0 := by
  refine (congrArg (tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n ≫ ·)
    (tateToGlobal_succ φ ψ A Aᵥ a Aᵣ ar n)).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (mappingCoconeNat.homologyδ_homologyMap_fst_assoc _ _ _)).trans (by rw [zero_comp, comp_zero]))

theorem tateCompactCohomology_exact_global (n : ℕ) :
    (ShortComplex.mk _ _ (tateToGlobal_tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₃ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) (n + 1))
  exact ShortComplex.isoMk (Iso.refl _) (tateGlobalCohomologyIso A Aᵣ n)
    (tateLocalCohomologyIso Aᵥ Aᵣ (n + 1))
    ((Category.id_comp _).trans (tateToGlobal_succ φ ψ A Aᵥ a Aᵣ ar n))
    (homologyMap_tateCompactRes_succ φ ψ A Aᵥ a Aᵣ ar n).symm

theorem tateCompactCohomology_exact_local (n : ℕ) :
    (ShortComplex.mk _ _ (tateGlobalToLocal_tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₁ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) (n + 1))
  exact ShortComplex.isoMk (tateGlobalCohomologyIso A Aᵣ n) (tateLocalCohomologyIso Aᵥ Aᵣ (n + 1))
    (Iso.refl _) (homologyMap_tateCompactRes_succ φ ψ A Aᵥ a Aᵣ ar n).symm
    ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)

theorem tateCompactCohomology_exact_compact (n : ℕ) :
    (ShortComplex.mk _ _ (tateLocalToCompact_tateToGlobal φ ψ A Aᵥ a Aᵣ ar n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₂ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) n)
  exact ShortComplex.isoMk (tateLocalCohomologyIso Aᵥ Aᵣ n) (Iso.refl _)
    (tateGlobalCohomologyIso A Aᵣ n)
    ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (tateToGlobal_succ φ ψ A Aᵥ a Aᵣ ar n))

end Sequence

section Zero

noncomputable def tateToGlobalZero :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar 0 ⟶ ModuleCat.of k (cohomology A 0 × ∀ w, Aᵣ w) :=
  HomologicalComplex.homologyMap (mappingCoconeNat.fst (tateCompactRes φ ψ A Aᵥ a Aᵣ ar)) 0 ≫
    (tateGlobalCohomologyZeroIso A Aᵣ).hom

noncomputable def tateGlobalZeroToLocal :
    ModuleCat.of k (cohomology A 0 × ∀ w, Aᵣ w) ⟶
      ModuleCat.of k ((∀ v, cohomology (Aᵥ v) 0) × (∀ w, cohomology (Aᵣ w) 0)) :=
  (tateGlobalCohomologyZeroIso A Aᵣ).inv ≫
    HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0 ≫
      (tateLocalCohomologyIso Aᵥ Aᵣ 0).hom

@[reassoc (attr := simp)]
theorem tateToGlobalZero_tateGlobalZeroToLocal :
    tateToGlobalZero φ ψ A Aᵥ a Aᵣ ar ≫ tateGlobalZeroToLocal φ ψ A Aᵥ a Aᵣ ar = 0 := by
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)).trans
    ((mappingCoconeNat.homologyMap_fst_homologyMap_assoc _ 0 _).trans zero_comp))

@[reassoc (attr := simp)]
theorem tateGlobalZeroToLocal_tateLocalToCompact :
    tateGlobalZeroToLocal φ ψ A Aᵥ a Aᵣ ar ≫ tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar 0 = 0 := by
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)).trans
      (mappingCoconeNat.homologyMap_homologyδ _ 0)))).trans comp_zero)

theorem tateCompactCohomology_exact_localZero :
    (ShortComplex.mk _ _ (tateGlobalZeroToLocal_tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₁ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0)
  exact ShortComplex.isoMk (tateGlobalCohomologyZeroIso A Aᵣ) (tateLocalCohomologyIso Aᵥ Aᵣ 0)
    (Iso.refl _) (Iso.hom_inv_id_assoc _ _)
    ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)

section NormClass

variable {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F'] [Fintype F']

noncomputable def normClass (B : Rep.{u} k F') [IsDiscreteRep B] (m : B) : cohomology B 0 :=
  ((cochainsComplex B).homologyπ 0).hom ((cochainsComplex B).cyclesMk
    (zeroCochain B (B.ρ.norm m)) 1 (by simp) (d_zeroCochain_norm B m))

end NormClass

theorem localCohomologyIso_homologyMap_normCochains
    (y : (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).homology 0) :
    (localCohomologyIso Aᵣ 0).hom.hom ((HomologicalComplex.homologyMap (normCochains Aᵣ) 0).hom y) =
      fun w => normClass (Aᵣ w)
        ((show ∀ w, Aᵣ w from (degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))).hom.hom y) w) := by
  obtain ⟨c, rfl⟩ := homologyπ_hom_surjective _ 0 y
  funext w
  rw [degZeroHomologyIso_hom_homologyπ, homologyMap_homologyπ_apply]
  change (HomologicalComplex.homologyMap (piProj _ w) 0).hom
      (((piComplex fun w => cochainsComplex (Aᵣ w)).homologyπ 0).hom
        ((HomologicalComplex.cyclesMap (normCochains Aᵣ) 0).hom c)) = _
  rw [homologyMap_homologyπ_apply]
  unfold normClass
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
  exact ((cochainsComplex (Aᵣ w)).i_cyclesMk _ _ _ _).symm

theorem tateGlobalZeroToLocal_hom_apply (x : cohomology A 0) (e : ∀ w, Aᵣ w) :
    (tateGlobalZeroToLocal φ ψ A Aᵥ a Aᵣ ar).hom (x, e) =
      ((globalToLocal φ A Aᵥ a 0).hom x,
        (globalToLocal ψ A Aᵣ ar 0).hom x + fun w => normClass (Aᵣ w) (e w)) := by
  set z := (tateGlobalCohomologyZeroIso A Aᵣ).inv.hom (x, e) with hz
  have hze : (tateGlobalCohomologyZeroIso A Aᵣ).hom.hom z = (x, e) :=
    hom_apply_hom_apply_of_comp_eq (Iso.inv_hom_id (tateGlobalCohomologyZeroIso A Aᵣ))
      (show ModuleCat.of k (cohomology A 0 × ∀ w, Aᵣ w) from (x, e))
  have hx : (HomologicalComplex.homologyMap (prodFst _ _) 0).hom z = x := congrArg Prod.fst hze
  have he : (degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))).hom.hom
      ((HomologicalComplex.homologyMap (prodSnd _ _) 0).hom z) = e := congrArg Prod.snd hze
  change (tateLocalCohomologyIso Aᵥ Aᵣ 0).hom.hom
    ((HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0).hom z) = _
  rw [tateLocalCohomologyIso_hom_apply]
  refine Prod.ext ?_ ?_
  · have e1 : HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0 ≫
        HomologicalComplex.homologyMap (prodFst _ _) 0 ≫ (localCohomologyIso Aᵥ 0).hom =
        HomologicalComplex.homologyMap (prodFst _ _) 0 ≫ globalToLocal φ A Aᵥ a 0 := by
      rw [← HomologicalComplex.homologyMap_comp_assoc, tateCompactRes_prodFst,
        HomologicalComplex.homologyMap_comp_assoc, homologyMap_localRes_localCohomologyIso_hom]
    rw [← hx]
    exact hom_apply_hom_apply_of_comp_eq e1 z
  · have e2 : HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0 ≫
        HomologicalComplex.homologyMap (prodSnd _ _) 0 =
        HomologicalComplex.homologyMap (prodFst _ _) 0 ≫
            HomologicalComplex.homologyMap (localRes ψ A Aᵣ ar) 0 +
          HomologicalComplex.homologyMap (prodSnd _ _) 0 ≫
            HomologicalComplex.homologyMap (normCochains Aᵣ) 0 := by
      rw [← HomologicalComplex.homologyMap_comp, tateCompactRes_prodSnd,
        HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
        HomologicalComplex.homologyMap_comp]
    change (localCohomologyIso Aᵣ 0).hom.hom
      ((HomologicalComplex.homologyMap (prodSnd _ _) 0).hom
        ((HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0).hom z)) = _
    rw [hom_apply_hom_apply_of_comp_eq e2 z, ModuleCat.hom_add, LinearMap.add_apply, map_add]
    congr 1
    · rw [← hx]
      exact hom_apply_hom_apply_of_comp_eq
        (homologyMap_localRes_localCohomologyIso_hom ψ A Aᵣ ar 0) _
    · rw [← he]
      exact localCohomologyIso_homologyMap_normCochains Aᵣ _

end Zero

end Tate

end GroundTheory.ProfCoh
