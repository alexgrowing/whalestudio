import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDefs
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.EqZeroOfBrauerLocalApplyEqZero
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.Characters
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplit
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global

universe u

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section RootsMap

variable {M N : Type*} [Field M] [Field N] (n : ℕ) [NeZero n]

theorem bijective_restrictRootsOfUnity_of_isPrimitiveRoot (f : M →+* N) {z : M} (hz : IsPrimitiveRoot z n) :
    Function.Bijective (restrictRootsOfUnity f n) := by
  classical
  have hinj : Function.Injective (restrictRootsOfUnity f n) := fun a b h => by
    have e : f ((a : Mˣ) : M) = f ((b : Mˣ) : M) :=
      congrArg (fun x : rootsOfUnity n N => ((x : Nˣ) : N)) h
    exact Subtype.ext (Units.ext (f.injective e))
  refine hinj.bijective_of_nat_card_le ?_
  rw [hz.card_rootsOfUnity]
  exact card_rootsOfUnity N n

end RootsMap

section Inverse

variable {k Γ : Type u} [CommRing k] [Group Γ]

def repInvOfBijective {A B : Rep.{u} k Γ} (f : A ⟶ B) (hf : Function.Bijective f.hom) : B ⟶ A :=
  Rep.ofHom ⟨(LinearEquiv.ofBijective f.hom.toLinearMap hf).symm.toLinearMap, fun g => LinearMap.ext fun b => by
    set e := LinearEquiv.ofBijective f.hom.toLinearMap hf
    apply e.injective
    change e (e.symm (B.ρ g b)) = f.hom (A.ρ g (e.symm b))
    rw [e.apply_symm_apply, Rep.hom_comm_apply]
    change B.ρ g b = B.ρ g (e (e.symm b))
    rw [e.apply_symm_apply]⟩

theorem comp_repInvOfBijective {A B : Rep.{u} k Γ} (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    f ≫ repInvOfBijective f hf = 𝟙 A :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a =>
    (LinearEquiv.ofBijective f.hom.toLinearMap hf).symm_apply_apply a))

theorem repInvOfBijective_comp {A B : Rep.{u} k Γ} (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    repInvOfBijective f hf ≫ f = 𝟙 B :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun b =>
    (LinearEquiv.ofBijective f.hom.toLinearMap hf).apply_symm_apply b))

end Inverse

section CompactMap

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
  {Aᵥ Bᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Bᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {b : ∀ v, Rep.res (φ v).toMonoidHom B ⟶ Bᵥ v}

theorem compactCohomologyMap_congr {g g' : A ⟶ B} {gᵥ gᵥ' : ∀ v, Aᵥ v ⟶ Bᵥ v}
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ b v)
    (hg' : ∀ v, a v ≫ gᵥ' v = (Rep.resFunctor (φ v).toMonoidHom).map g' ≫ b v)
    (h1 : g = g') (h2 : gᵥ = gᵥ') (n : ℕ) :
    compactCohomologyMap φ g gᵥ hg n = compactCohomologyMap φ g' gᵥ' hg' n := by
  subst h1
  subst h2
  rfl

theorem compactCohomologyMap_nsmul_id (m : ℕ)
    (hg : ∀ v, a v ≫ (m • 𝟙 (Aᵥ v)) = (Rep.resFunctor (φ v).toMonoidHom).map (m • 𝟙 A) ≫ a v) (n : ℕ) :
    compactCohomologyMap φ (m • 𝟙 A) (fun v => m • 𝟙 (Aᵥ v)) hg n = m • 𝟙 _ := by
  have h : compactCochainsMap φ (m • 𝟙 A) (fun v => m • 𝟙 (Aᵥ v)) hg = m • 𝟙 _ := by
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochainsComplex A).X n ×
      shiftNegOneX (piComplex fun v => cochainsComplex (Aᵥ v)) n) => ?_)
    have hR : ((m • 𝟙 (compactCochains φ A Aᵥ a) : compactCochains φ A Aᵥ a ⟶ _).f n).hom p = m • p := by
      simp only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, ModuleCat.hom_nsmul, ModuleCat.hom_id]
      rfl
    rw [hR]
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ ?_
    · change ((cochainsMap (m • 𝟙 A)).f n).hom x = m • x
      rw [cochainsMap_nsmul, cochainsMap_id]
      simp [Module.End.mul_apply, Module.End.natCast_apply]
    · cases n with
      | zero => rfl
      | succ n =>
        change ((piMap fun v => cochainsMap (m • 𝟙 (Aᵥ v))).f n).hom y = m • y
        funext v
        change ((cochainsMap (m • 𝟙 (Aᵥ v))).f n).hom (y v) = m • y v
        rw [cochainsMap_nsmul, cochainsMap_id]
        simp [Module.End.mul_apply, Module.End.natCast_apply]
  change HomologicalComplex.homologyMap (compactCochainsMap φ (m • 𝟙 A) (fun v => m • 𝟙 (Aᵥ v)) hg) n = _
  rw [h]
  change (HomologicalComplex.homologyFunctor _ _ n).map (m • 𝟙 _) = _
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

end CompactMap

section ULiftCompare

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] (φ : H →* G) (hφ : Continuous φ) {A B : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep A]
  [IsDiscreteRep B] {Aᵥ : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep Aᵥ] {C : Rep.{0} ℤ H} [IsDiscreteRep C]
  [IsDiscreteRep (uliftIntToIntRep Aᵥ)]

theorem cohomologyMap_uliftInt_cohomologyMapAlong_local (g : A ⟶ B) (f : Rep.res φ A ⟶ Aᵥ)
    (e : uliftIntToIntRep Aᵥ ⟶ C) (f₂ : Rep.res φ (uliftIntToIntRep B) ⟶ C)
    (hf : ∀ a : A, e.hom (f.hom a) = f₂.hom (g.hom a)) (m : ℕ) (x : cohomology A m) :
    (cohomologyMap e m).hom (cohomologyULiftIntAddEquiv Aᵥ m ((cohomologyMapAlong φ hφ f m).hom x)) =
      (cohomologyMapAlong φ hφ f₂ m).hom (cohomologyULiftIntAddEquiv B m ((cohomologyMap g m).hom x)) := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective A m x
  rw [cohomologyMapAlong_cohomologyπ, cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMap_cohomologyπ,
    cohomologyMap_cohomologyπ, cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt,
    cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesMapAlong,
    cochainOf_cocycleι_cocyclesULiftInt, cochainOf_cocycleι_cyclesMap]
  funext h
  exact hf _

end ULiftCompare

section Comparison

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

set_option maxHeartbeats 1600000 in
include hnS in

theorem bijective_gsRootsOmegaMor (v : S) : Function.Bijective (gsRootsOmegaMor S ιs n v).hom := by
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  have hzS : z ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    mem_maxUnramifiedOutside_of_pow_eq_one S (NeZero.ne n) hnS hz.pow_eq_one
  have hzS' : IsPrimitiveRoot (⟨z, hzS⟩ : maxUnramifiedOutside K.1 ℚ̄ S) n :=
    hz.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) Subtype.val_injective
  have hF := bijective_restrictRootsOfUnity_of_isPrimitiveRoot n
    ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom hzS'
  exact Additive.ofMul.bijective.comp (hF.comp Additive.toMul.bijective)

def gsRootsOmegaInv (v : S) :
    galRootsOfUnity ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n ⟶
      Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n) :=
  repInvOfBijective (gsRootsOmegaMor S ιs n v) (bijective_gsRootsOmegaMor S ιs n hnS v)

def gsRootsComparisonInv (m : ℕ) :
    gsRootsCompact S ιs n m ⟶ compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) m :=
  compactCohomologyMap (gsFinFamily S ιs) (a := gsRootsOmegaMor S ιs n) (b := fun _ => 𝟙 _)
    (𝟙 (gsRoots S n)) (gsRootsOmegaInv S ιs n hnS)
    (fun v => Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x =>
      (LinearEquiv.ofBijective (gsRootsOmegaMor S ιs n v).hom.toLinearMap
        (bijective_gsRootsOmegaMor S ιs n hnS v)).symm_apply_apply x))) m

theorem gsRootsComparison_comp_inv (m : ℕ) :
    gsRootsComparison S ιs n m ≫ gsRootsComparisonInv S ιs n hnS m = 𝟙 _ :=
  (compactCohomologyMap_comp (gsFinFamily S ιs) _ _ _ _ _ _ m).symm.trans
    ((compactCohomologyMap_congr (gsFinFamily S ιs) _ _ (Category.comp_id _)
      (funext fun _ => comp_repInvOfBijective _ _) m).trans (compactCohomologyMap_id (gsFinFamily S ιs) m))

theorem gsRootsComparison_inv_comp (m : ℕ) :
    gsRootsComparisonInv S ιs n hnS m ≫ gsRootsComparison S ιs n m = 𝟙 _ :=
  (compactCohomologyMap_comp (gsFinFamily S ιs) _ _ _ _ _ _ m).symm.trans
    ((compactCohomologyMap_congr (gsFinFamily S ιs) _ _ (Category.comp_id _)
      (funext fun _ => repInvOfBijective_comp _ _) m).trans (compactCohomologyMap_id (gsFinFamily S ιs) m))

def gsRootsComparisonIso (m : ℕ) :
    compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) m ≅ gsRootsCompact S ιs n m where
  hom := gsRootsComparison S ιs n m
  inv := gsRootsComparisonInv S ιs n hnS m
  hom_inv_id := gsRootsComparison_comp_inv S ιs n hnS m
  inv_hom_id := gsRootsComparison_inv_comp S ιs n hnS m

include hnS in
theorem bijective_gsRootsComparison (m : ℕ) : Function.Bijective (gsRootsComparison S ιs n m).hom :=
  ConcreteCategory.bijective_of_isIso (gsRootsComparisonIso S ιs n hnS m).hom

end Comparison

section H2Compact

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

def uliftUnitsToUnitsZ (v : S) :
    uliftIntToIntRep (galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) ⟶
      galUnitsZ ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  Rep.ofHom ⟨(AddMonoidHom.id _).toIntLinearMap, fun _ => rfl⟩

instance isDiscreteRep_uliftIntToIntRep_galUnits_local (v : S) :
    IsDiscreteRep (uliftIntToIntRep (galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) :=
  ⟨fun a => isOpen_stabilizer (galUnits.{0, 0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) a⟩

theorem gsLocalRes_sUnitsToUnits_eq (v : S) (z : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
    (gsLocalRes S (ιs v) 2).hom (cohomologyULiftIntAddEquiv _ 2
        ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom z)) =
      (cohomologyMap (uliftUnitsToUnitsZ S v) 2).hom (cohomologyULiftIntAddEquiv _ 2
        ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
          (gsSUnitsLocalMor S ιs v) 2).hom z)) :=
  (cohomologyMap_uliftInt_cohomologyMapAlong_local (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
    (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) (gsSUnitsLocalMor S ιs v) (uliftUnitsToUnitsZ S v)
    (embUnitsMorZ S (ιs v)) (fun _ => rfl) 2 z).symm

variable (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

set_option maxHeartbeats 4000000 in
include hℓ hS in

theorem eq_zero_of_gsUnitsCompact_two (hodd : Odd ℓ ∨ IsTotallyComplex K.1) (y : gsUnitsCompact S ιs 2) (j : ℕ)
    (hy : ℓ ^ j • y = 0) : y = 0 := by
  classical
  have hz : (compactToGlobal (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) _ (gsSUnitsLocalMor S ιs) 2).hom y = 0 := by
    refine eq_zero_of_sUnitsBrauer_eq_zero K S ℓ hℓ hS _ j
      ((map_nsmul _ _ _).symm.trans ((congrArg _ hy).trans (map_zero _))) ?_
    refine eq_zero_of_brauerLocal_apply_eq_zero (gsLocalEmbeddings S ιs) _ fun w => ?_
    rcases w with w | w
    · apply placeInv_injective (K := K) (.inl w)
      refine (placeInv_inl_eq_zero (ℓ ^ j) (hodd.imp (fun h => h.pow) id) w _ ?_).trans (map_zero _).symm
      have e : ℓ ^ j • brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S
          ((compactToGlobal (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) _ (gsSUnitsLocalMor S ιs) 2).hom y)) = 0 := by
        rw [← map_nsmul, ← map_nsmul, ← map_nsmul, hy, map_zero, map_zero, map_zero]
      exact (map_nsmul (DFinsupp.evalAddMonoidHom (β := fun w => localGaloisCohomology K 2 w)
        (Sum.inl w : Place K.1)) (ℓ ^ j) _).symm.trans
        ((congrArg (DFinsupp.evalAddMonoidHom (β := fun w => localGaloisCohomology K 2 w) (Sum.inl w : Place K.1)) e).trans
          (map_zero _))
    · by_cases hw : w ∈ S
      · have h0 : (cohomologyMapAlong (gsFinFamily S ιs ⟨w, hw⟩).toMonoidHom (continuous_toMonoidHom _)
            (gsSUnitsLocalMor S ιs ⟨w, hw⟩) 2).hom
            ((compactToGlobal (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) _ (gsSUnitsLocalMor S ιs) 2).hom y) = 0 :=
          congrFun (ConcreteCategory.congr_hom (compactToGlobal_globalToLocal (gsFinFamily S ιs)
            (galSUnitsMax K.1 ℚ̄ S) _ (gsSUnitsLocalMor S ιs) 2) y) ⟨w, hw⟩
        refine (congrArg (fun x => brauerLocal (gsLocalEmbeddings S ιs) x (.inr w)) (sUnitsBrauer_apply K S _)).trans ?_
        refine (brauerLocal_gsBrauerInfl_inr K S (gsLocalEmbeddings S ιs) w _).trans ?_
        have hfin : (gsLocalEmbeddings S ιs).fin w = ιs ⟨w, hw⟩ := gsLocalEmbeddings_fin S ιs ⟨w, hw⟩
        rw [hfin]
        refine (gsLocalRes_sUnitsToUnits_eq S ιs ⟨w, hw⟩ _).trans ?_
        rw [h0, map_zero, map_zero]
        rfl
      · exact brauerLocal_sUnitsBrauer_inr K S _ _ w hw
  obtain ⟨ξ, hξ⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact_compact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) _ (gsSUnitsLocalMor S ιs) 1) hz
  have : ∀ v : S, Subsingleton (cohomology (galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) 1) :=
    fun v => subsingleton_cohomology_one_galUnits
  rw [← hξ, show ξ = 0 from Subsingleton.elim _ _, map_zero]

end H2Compact

end

end GroundTheory.ProfCoh
