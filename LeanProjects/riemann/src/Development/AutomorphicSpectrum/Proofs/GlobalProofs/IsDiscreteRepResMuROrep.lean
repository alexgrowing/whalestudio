import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.RestrictedRamification.LocalMaps
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Subgroup
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.EqZeroOfBrauerLocalApplyEqZero
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.OpenSubgroups
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.GSCd

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global FiniteSubfield
open GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance 2000] Rep.hV2

theorem continuous_fixingEquiv (K : FiniteSubfield) :
    Continuous (IntermediateField.fixingSubgroupEquiv K.1) := by
  have : FiniteDimensional ℚ K.1 := K.2
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hs⟩ := hs
  have hfin : FiniteDimensional ℚ ↥(E.restrictScalars ℚ) :=
    (Module.Finite.trans (R := ℚ) ↥K.1 ↥E : FiniteDimensional ℚ ↥E)
  have ho : IsOpen (Subtype.val ⁻¹' ((E.restrictScalars ℚ).fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :
      Set ↥K.1.fixingSubgroup) :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (ho.mem_nhds (Subgroup.one_mem _)) fun σ hσ => hs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx

variable (K : FiniteSubfield) (S : Finset (HeightOneSpectrum (𝓞 K.1)))

abbrev Ls : IntermediateField K.1 ℚ̄ :=
  maxUnramifiedOutside K.1 ℚ̄ (S : Set (HeightOneSpectrum (𝓞 K.1)))

abbrev Gs : Type := galUnramifiedOutside K.1 ℚ̄ (S : Set (HeightOneSpectrum (𝓞 K.1)))

def resG : K.1.fixingSubgroup →* Gs K S :=
  (AlgEquiv.restrictNormalHom (Ls K S)).comp (IntermediateField.fixingSubgroupEquiv K.1).toMonoidHom

theorem resG_surjective : Function.Surjective (resG K S) :=
  (AlgEquiv.restrictNormalHom_surjective ℚ̄).comp (IntermediateField.fixingSubgroupEquiv K.1).surjective

theorem continuous_resG : Continuous (resG K S) :=
  (InfiniteGalois.restrictNormalHom_continuous (Ls K S)).comp (continuous_fixingEquiv K)

theorem isQuotientMap_resG : Topology.IsQuotientMap (resG K S) :=
  (continuous_resG K S).isClosedMap.isQuotientMap (continuous_resG K S) (resG_surjective K S)

def liftE : Gs K S →* K.1.fixingSubgroup ⧸ (resG K S).ker :=
  (QuotientGroup.quotientKerEquivOfSurjective (resG K S) (resG_surjective K S)).symm.toMonoidHom

theorem liftE_resG (g : K.1.fixingSubgroup) :
    liftE K S (resG K S g) = QuotientGroup.mk g := by
  apply (QuotientGroup.quotientKerEquivOfSurjective (resG K S) (resG_surjective K S)).injective
  simp [liftE]
  rfl

def descend (M : Rep ℤ K.1.fixingSubgroup) : Rep ℤ (Gs K S) :=
  Rep.res (liftE K S) (M.quotientToInvariants (resG K S).ker)

def descendVal (M : Rep ℤ K.1.fixingSubgroup) : descend K S M →ₗ[ℤ] M :=
  (Representation.invariants (M.ρ.comp (resG K S).ker.subtype)).subtype

theorem descendVal_injective (M : Rep ℤ K.1.fixingSubgroup) :
    Function.Injective (descendVal K S M) :=
  Subtype.val_injective

theorem mem_range_descendVal (M : Rep ℤ K.1.fixingSubgroup) (x : M) :
    x ∈ LinearMap.range (descendVal K S M) ↔ ∀ g ∈ (resG K S).ker, M.ρ g x = x := by
  constructor
  · rintro ⟨y, rfl⟩ g hg
    exact y.2 ⟨g, hg⟩
  · intro h
    exact ⟨⟨x, fun g => h g.1 g.2⟩, rfl⟩

theorem descendVal_ρ (M : Rep ℤ K.1.fixingSubgroup) (g : K.1.fixingSubgroup) (x : descend K S M) :
    descendVal K S M ((descend K S M).ρ (resG K S g) x) = M.ρ g (descendVal K S M x) := by
  have h : (M.ρ.quotientToInvariants (resG K S).ker) (liftE K S (resG K S g)) =
      (M.ρ.quotientToInvariants (resG K S).ker) (QuotientGroup.mk g) :=
    congrArg _ (liftE_resG K S g)
  exact congrArg Subtype.val (DFunLike.congr_fun h x)

instance isDiscreteRep_descend (M : Rep ℤ K.1.fixingSubgroup) [IsDiscreteRep M] :
    IsDiscreteRep (descend K S M) := by
  refine ⟨fun x => ?_⟩
  rw [← (isQuotientMap_resG K S).isOpen_preimage]
  have h : IsOpen ((stabilizer M.ρ (descendVal K S M x) : Subgroup _) : Set K.1.fixingSubgroup) :=
    IsDiscreteRep.isOpen_stabilizer (A := M) (descendVal K S M x)
  refine Subgroup.isOpen_mono (H₂ := (stabilizer (descend K S M).ρ x).comap (resG K S)) ?_ h
  intro g hg
  refine descendVal_injective K S M ?_
  rw [descendVal_ρ]
  exact hg

def descendMap {M M' : Rep ℤ K.1.fixingSubgroup} (f : M ⟶ M') : descend K S M ⟶ descend K S M' :=
  (Rep.resFunctor (liftE K S)).map ((Rep.quotientToInvariantsFunctor ℤ (resG K S).ker).map f)

theorem descendVal_descendMap {M M' : Rep ℤ K.1.fixingSubgroup} (f : M ⟶ M') (x : descend K S M) :
    descendVal K S M' ((descendMap K S f).hom x) = f.hom (descendVal K S M x) :=
  rfl

def preOpen (U : OpenSubgroup (Gs K S)) : OpenSubgroup K.1.fixingSubgroup :=
  U.comap (resG K S) (continuous_resG K S)

abbrev fU (U : OpenSubgroup (Gs K S)) : FiniteSubfield := fieldOf (preOpen K S U)

def absHom (U : OpenSubgroup (Gs K S)) :
    (fU K S U).1.fixingSubgroup →* (U : Subgroup (Gs K S)) :=
  ((resG K S).subgroupComap (U : Subgroup (Gs K S))).comp
    (openEquiv (preOpen K S U)).symm.toMonoidHom

theorem continuous_absHom (U : OpenSubgroup (Gs K S)) : Continuous (absHom K S U) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_resG K S).comp
    (continuous_subtype_val.comp (continuous_openEquiv_symm (preOpen K S U)))

abbrev resK (K : FiniteSubfield) (A : Rep ℤ (ℚ̄ ≃ₐ[ℚ] ℚ̄)) : Rep ℤ K.1.fixingSubgroup :=
  Rep.res K.1.fixingSubgroup.subtype A

def absMor (A : Rep ℤ (ℚ̄ ≃ₐ[ℚ] ℚ̄)) (U : OpenSubgroup (Gs K S)) :
    Rep.res (absHom K S U) (Rep.res (U : Subgroup (Gs K S)).subtype (descend K S (resK K A))) ⟶
      resK (fU K S U) A :=
  Rep.ofHom ⟨descendVal K S (resK K A), fun h => LinearMap.ext fun x => by
    have hρ := descendVal_ρ K S (resK K A) ((openEquiv (preOpen K S U)).symm h).1 x
    have hg : ((((openEquiv (preOpen K S U)).symm h).1 : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) = h.1 := by
      have h1 := coe_openEquiv_apply (preOpen K S U) ((openEquiv (preOpen K S U)).symm h)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1.symm
    change descendVal K S (resK K A) ((descend K S (resK K A)).ρ
      (resG K S ((openEquiv (preOpen K S U)).symm h).1) x) = A.ρ h.1 (descendVal K S (resK K A) x)
    rw [hρ, ← hg]
    rfl⟩

def absInfl (A : Rep ℤ (ℚ̄ ≃ₐ[ℚ] ℚ̄)) [IsDiscreteRep A] (U : OpenSubgroup (Gs K S)) (n : ℕ) :
    cohomology (Rep.res (U : Subgroup (Gs K S)).subtype (descend K S (resK K A))) n ⟶
      cohomology (resK (fU K S U) A) n :=
  cohomologyMapAlong (absHom K S U) (continuous_absHom K S U) (absMor K S A U) n

abbrev UsR : Rep ℤ (Gs K S) := descend K S (unitsLimitRep K)

abbrev JsR : Rep ℤ (Gs K S) := descend K S (limitRep K)

abbrev CsR : Rep ℤ (Gs K S) := descend K S (classLimitRep K)

def sIdeleLimit : Submodule ℤ (limitRep K) :=
  ⨆ p : GLevel K, (sIdelesSubmodule K.1 p.1.1 S).map
    ((levelMor K p.1).hom.toLinearMap)

theorem sIdeleLimit_stable (g : K.1.fixingSubgroup) :
    sIdeleLimit K S ≤ (sIdeleLimit K S).comap ((limitRep K).ρ g) := by
  refine iSup_le fun p => ?_
  intro z hz
  obtain ⟨y, hy, hz⟩ := Submodule.mem_map.1 hz
  have hmem : (ideleRep K.1 p.1.1).ρ (restrictHom (F := K) (E := p.1) g) y ∈
      sIdelesSubmodule K.1 p.1.1 S :=
    Submodule.mem_comap.1 (sIdelesSubmodule_stable K.1 p.1.1 S (restrictHom (F := K) (E := p.1) g) hy)
  have h' : (levelMor K p.1).hom ((ideleRep K.1 p.1.1).ρ (restrictHom (F := K) (E := p.1) g) y) ∈
      sIdeleLimit K S := Submodule.mem_iSup_of_mem p (Submodule.mem_map_of_mem hmem)
  have h : (limitRep K).ρ g z =
      (levelMor K p.1).hom ((ideleRep K.1 p.1.1).ρ (restrictHom (F := K) (E := p.1) g) y) := by
    rw [← hz]
    exact (Rep.hom_comm_apply (levelMor K p.1) g y).symm
  rw [Submodule.mem_comap, h]
  exact h'

def SJ : Submodule ℤ (JsR K S) := (sIdeleLimit K S).comap (descendVal K S (limitRep K))

theorem SJ_stable (σ : Gs K S) : SJ K S ≤ (SJ K S).comap ((JsR K S).ρ σ) := by
  obtain ⟨g, rfl⟩ := resG_surjective K S σ
  intro x hx
  rw [Submodule.mem_comap, SJ, Submodule.mem_comap, descendVal_ρ]
  exact sIdeleLimit_stable K S g hx

abbrev JSrep : Rep ℤ (Gs K S) := (JsR K S).subrepresentation (SJ K S) (SJ_stable K S)

def qMor : JSrep K S ⟶ CsR K S :=
  Rep.subtype (JsR K S) (SJ K S) (SJ_stable K S) ≫ descendMap K S (idelesShortComplexRes K).g

def diagS : UsR K S ⟶ JsR K S := descendMap K S (idelesShortComplexRes K).f

def SO : Submodule ℤ (UsR K S) := (SJ K S).comap (diagS K S).hom.toLinearMap

theorem SO_stable (σ : Gs K S) : SO K S ≤ (SO K S).comap ((UsR K S).ρ σ) := by
  intro x hx
  rw [Submodule.mem_comap, SO, Submodule.mem_comap]
  have h : (diagS K S).hom ((UsR K S).ρ σ x) = (JsR K S).ρ σ ((diagS K S).hom x) :=
    Rep.hom_comm_apply (diagS K S) σ x
  exact h ▸ SJ_stable K S σ hx

abbrev Orep : Rep ℤ (Gs K S) := (UsR K S).subrepresentation (SO K S) (SO_stable K S)

def mMor : Orep K S ⟶ JSrep K S :=
  homToSubrep (JsR K S) (SJ K S) (SJ_stable K S)
    (Rep.subtype (UsR K S) (SO K S) (SO_stable K S) ≫ diagS K S) (fun b => b.2)

instance isDiscreteRep_JSrep : IsDiscreteRep (JSrep K S) := isDiscreteRep_subrepresentation _ _ _

instance isDiscreteRep_Orep : IsDiscreteRep (Orep K S) := isDiscreteRep_subrepresentation _ _ _

instance isDiscreteRep_res_JSrep (U : Subgroup (Gs K S)) :
    IsDiscreteRep (Rep.res U.subtype (JSrep K S)) := isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_CsR (U : Subgroup (Gs K S)) :
    IsDiscreteRep (Rep.res U.subtype (CsR K S)) := isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_JsR (U : Subgroup (Gs K S)) :
    IsDiscreteRep (Rep.res U.subtype (JsR K S)) := isDiscreteRep_res_subtype _ _

def torSub {G : Type} [Group G] (O : Rep ℤ G) (l : ℕ) : Submodule ℤ O :=
  LinearMap.ker ((l : ℤ) • (LinearMap.id : O →ₗ[ℤ] O))

theorem torSub_stable {G : Type} [Group G] (O : Rep ℤ G) (l : ℕ) (g : G) :
    torSub O l ≤ (torSub O l).comap (O.ρ g) := by
  intro x hx
  have hx' : (l : ℤ) • x = 0 := hx
  change (l : ℤ) • O.ρ g x = 0
  rw [← map_zsmul, hx', map_zero]

abbrev MuR {G : Type} [Group G] (O : Rep ℤ G) (l : ℕ) : Rep ℤ G :=
  O.subrepresentation (torSub O l) (torSub_stable O l)

instance isDiscreteRep_MuR {G : Type} [Group G] [TopologicalSpace G] (O : Rep.{0} ℤ G)
    [IsDiscreteRep O] (l : ℕ) : IsDiscreteRep (MuR O l) :=
  isDiscreteRep_subrepresentation _ _ _

instance isDiscreteRep_res_MuR {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (O : Rep.{0} ℤ G) [IsDiscreteRep O] (l : ℕ) (P : Subgroup G) :
    IsDiscreteRep (Rep.res P.subtype (MuR O l)) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_MuR_Orep (l : ℕ) : IsDiscreteRep (MuR (Orep K S) l) :=
  @isDiscreteRep_MuR _ _ _ (Orep K S) (isDiscreteRep_Orep K S) l

instance isDiscreteRep_res_MuR_Orep (l : ℕ) (P : Subgroup (Gs K S)) :
    IsDiscreteRep (Rep.res P.subtype (MuR (Orep K S) l)) :=
  haveI := isDiscreteRep_MuR_Orep K S l
  isDiscreteRep_res_subtype (MuR (Orep K S) l) P

abbrev resMap {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
    {A B : Rep ℤ G} [IsDiscreteRep A] [IsDiscreteRep B] (f : A ⟶ B) (n : ℕ) :
    cohomology (Rep.res U.subtype A) n ⟶ cohomology (Rep.res U.subtype B) n :=
  cohomologyMap ((Rep.resFunctor U.subtype).map f) n

def infJ (U : OpenSubgroup (Gs K S)) (n : ℕ) :
    cohomology (Rep.res (U : Subgroup (Gs K S)).subtype (JSrep K S)) n ⟶
      cohomology (limitRep (fU K S U)) n :=
  resMap (U : Subgroup (Gs K S)) (Rep.subtype (JsR K S) (SJ K S) (SJ_stable K S)) n ≫
    absInfl K S IdeleLimit.rep U n

def infC (U : OpenSubgroup (Gs K S)) (n : ℕ) :
    cohomology (Rep.res (U : Subgroup (Gs K S)).subtype (CsR K S)) n ⟶
      cohomology (classLimitRep (fU K S U)) n :=
  absInfl K S classRep U n

def lamJ (U : OpenSubgroup (Gs K S)) (ι : LocalEmbeddings (fU K S U)) :
    cohomology (Rep.res (U : Subgroup (Gs K S)).subtype (JSrep K S)) 2 →+
      ⨁ v : Place (fU K S U).1, localGaloisCohomology (fU K S U) 2 v :=
  (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).toAddMonoidHom.comp
    (infJ K S U 2).hom.toAddMonoidHom

def GlobalInv : Prop :=
  ∀ (K : FiniteSubfield) (ι : LocalEmbeddings K),
    ∃ inv : cohomology (classLimitRep K) 2 →+ QZ, Function.Injective inv ∧
      ∀ y : cohomology (limitRep K) 2, inv ((idelesToClasses K 2).hom y) =
        sumPlaceInv K (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y)

def KummerDiv (l : ℕ) : Prop := ∀ a : Orep K S, ∃ b : Orep K S, l • b = a

def MuTrivial (l : ℕ) : Prop :=
  Nonempty (ZMod l ≃+ MuR (Orep K S) l) ∧ ∀ (σ : Gs K S) (x : MuR (Orep K S) l),
    (MuR (Orep K S) l).ρ σ x = x

def ClassPrimeTors (l : ℕ) : Prop :=
  ∀ c : CsR K S, ∃ n : ℕ, n.Coprime l ∧ ∃ j : JSrep K S, n • c = (qMor K S).hom j

def LeftExact : Prop :=
  mMor K S ≫ qMor K S = 0 ∧ Function.Injective (mMor K S).hom ∧
    ∀ j : JSrep K S, (qMor K S).hom j = 0 → ∃ o : Orep K S, (mMor K S).hom o = j

def ClassModuleH1Vanishing : Prop :=
  ∀ U : OpenSubgroup (Gs K S),
    Limits.IsZero (cohomology (Rep.res (U : Subgroup (Gs K S)).subtype (CsR K S)) 1)

def IdeleH3Vanishing : Prop :=
  ∀ U : OpenSubgroup (Gs K S),
    Subsingleton (cohomology (Rep.res (U : Subgroup (Gs K S)).subtype (JSrep K S)) 3)

def LamInj : Prop :=
  ∀ (U : OpenSubgroup (Gs K S)) (ι : LocalEmbeddings (fU K S U)), Function.Injective (lamJ K S U ι)

def LamSupport : Prop :=
  ∀ (U : OpenSubgroup (Gs K S)) (ι : LocalEmbeddings (fU K S U))
    (y : cohomology (Rep.res (U : Subgroup (Gs K S)).subtype (JSrep K S)) 2)
    (v : HeightOneSpectrum (𝓞 (fU K S U).1)),
    v ∉ placesAbove (fU K S U).1 (S : Set (HeightOneSpectrum (𝓞 K.1))) →
      lamJ K S U ι y (Sum.inr v) = 0

def LamArch : Prop :=
  ∀ (U : OpenSubgroup (Gs K S)) (ι : LocalEmbeddings (fU K S U))
    (y : cohomology (Rep.res (U : Subgroup (Gs K S)).subtype (JSrep K S)) 2)
    (v : InfinitePlace (fU K S U).1), lamJ K S U ι y (Sum.inl v) = 0

def LamSurj (l : ℕ) : Prop :=
  ∀ (U : OpenSubgroup (Gs K S)) (ι : LocalEmbeddings (fU K S U))
    (b : ⨁ v : Place (fU K S U).1, localGaloisCohomology (fU K S U) 2 v),
    (∀ v : InfinitePlace (fU K S U).1, b (Sum.inl v) = 0) →
    (∀ v : HeightOneSpectrum (𝓞 (fU K S U).1),
      v ∉ placesAbove (fU K S U).1 (S : Set (HeightOneSpectrum (𝓞 K.1))) → b (Sum.inr v) = 0) →
    (∃ a : ℕ, l ^ a • b = 0) → ∃ y, lamJ K S U ι y = b

def InfCInj : Prop :=
  ∀ U : OpenSubgroup (Gs K S), Function.Injective (infC K S U 2).hom

def InfCompat : Prop :=
  ∀ (U : OpenSubgroup (Gs K S))
    (y : cohomology (Rep.res (U : Subgroup (Gs K S)).subtype (JSrep K S)) 2),
    (infC K S U 2).hom ((resMap (U : Subgroup (Gs K S)) (qMor K S) 2).hom y) =
      (idelesToClasses (fU K S U) 2).hom ((infJ K S U 2).hom y)

def PrimarySurj (l : ℕ) : Prop :=
  ∀ (U : OpenSubgroup (Gs K S))
    (c : cohomology (Rep.res (U : Subgroup (Gs K S)).subtype (CsR K S)) 2),
    (∃ a : ℕ, l ^ a • c = 0) → ∃ y, (resMap (U : Subgroup (Gs K S)) (qMor K S) 2).hom y = c

def PrimaryDiv (l : ℕ) : Prop :=
  ∀ (U : OpenSubgroup (Gs K S))
    (y : cohomology (Rep.res (U : Subgroup (Gs K S)).subtype (JSrep K S)) 2),
    (∃ a : ℕ, l ^ a • y = 0) → (resMap (U : Subgroup (Gs K S)) (qMor K S) 2).hom y = 0 →
      ∃ y', (resMap (U : Subgroup (Gs K S)) (qMor K S) 2).hom y' = 0 ∧ l • y' = y

end
end GlobalTheory.CompanionTheory.GSCd
