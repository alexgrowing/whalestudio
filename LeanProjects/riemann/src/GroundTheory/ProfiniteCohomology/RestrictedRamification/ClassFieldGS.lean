import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSUnram
import GroundTheory.GlobalFields.GlobalArtinMap.Kernel
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.LocalField
  Function

noncomputable section

universe u

section Restrict

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem restrictAb_restrictNormalHom (E : IntermediateField F Ω) [Normal F E]
    (h : E ≤ maximalAbelianExtension F Ω) (g : Gal(Ω/F)) :
    restrictAb E h (AlgEquiv.restrictNormalHom (maximalAbelianExtension F Ω) g) =
      AlgEquiv.restrictNormalHom E g := by
  rw [← topologicalAbelianizationEquiv_mk, restrictAb_topologicalAbelianizationEquiv]

end Restrict

theorem zmod_pow_eq_one {n : ℕ} (z : Multiplicative (ZMod n)) : z ^ n = 1 := by
  change Multiplicative.ofAdd (n • Multiplicative.toAdd z) = Multiplicative.ofAdd 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}

section Character

variable (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))

def charAbs : Gal(Ω/K) →* Multiplicative (ZMod n) :=
  χ.toMonoidHom.comp (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S))

theorem charAbs_apply (g : Gal(Ω/K)) :
    charAbs χ g = χ (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) g) :=
  rfl

theorem continuous_charAbs : Continuous (charAbs χ) :=
  χ.continuous.comp (InfiniteGalois.restrictNormalHom_continuous _)

theorem isOpen_ker_charAbs : IsOpen ((charAbs χ).ker : Set Gal(Ω/K)) := by
  rw [MonoidHom.coe_ker]
  exact (isOpen_discrete {1}).preimage (continuous_charAbs χ)

theorem isClosed_ker_charAbs : IsClosed ((charAbs χ).ker : Set Gal(Ω/K)) := by
  rw [MonoidHom.coe_ker]
  exact (isClosed_discrete {1}).preimage (continuous_charAbs χ)

theorem closure_commutator_le_ker_charAbs :
    (commutator Gal(Ω/K)).topologicalClosure ≤ (charAbs χ).ker :=
  Subgroup.topologicalClosure_minimal _ (commutator_le_ker_of_comm _) (isClosed_ker_charAbs χ)

def charAb : (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) →* Multiplicative (ZMod n) :=
  (QuotientGroup.lift _ (charAbs χ) (closure_commutator_le_ker_charAbs χ)).comp
    (topologicalAbelianizationEquiv K Ω).symm.toMulEquiv.toMonoidHom

theorem charAb_restrictNormalHom (g : Gal(Ω/K)) :
    charAb χ (AlgEquiv.restrictNormalHom (maximalAbelianExtension K Ω) g) = charAbs χ g := by
  rw [← topologicalAbelianizationEquiv_mk]
  change QuotientGroup.lift _ (charAbs χ) (closure_commutator_le_ker_charAbs χ)
    ((topologicalAbelianizationEquiv K Ω).symm (topologicalAbelianizationEquiv K Ω _)) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

def charField : IntermediateField K Ω := fixedField (charAbs χ).ker

theorem fixingSubgroup_charField : (charField χ).fixingSubgroup = (charAbs χ).ker :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨(charAbs χ).ker, isClosed_ker_charAbs χ⟩

instance finiteDimensional_charField : FiniteDimensional K (charField χ) :=
  (InfiniteGalois.isOpen_iff_finite _).1 (by rw [fixingSubgroup_charField]; exact isOpen_ker_charAbs χ)

instance isGalois_charField : IsGalois K (charField χ) := IsGalois.of_fixedField_normal_subgroup _

theorem charAbs_eq_one_iff (g : Gal(Ω/K)) :
    charAbs χ g = 1 ↔ AlgEquiv.restrictNormalHom (charField χ) g = 1 := by
  rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
    fixingSubgroup_charField]

instance isAbelianGalois_charField : IsAbelianGalois K (charField χ) := by
  have : IsMulCommutative (charField χ ≃ₐ[K] charField χ) := ⟨⟨fun τ₁ τ₂ ↦ by
    obtain ⟨g₁, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₁
    obtain ⟨g₂, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₂
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← charAbs_eq_one_iff,
      map_mul, map_inv, map_mul, map_mul]
    exact mul_inv_eq_one.2 (mul_comm _ _)⟩⟩
  exact ⟨⟩

theorem charField_le : charField χ ≤ maxUnramifiedOutside K Ω S := by
  intro x hx
  rw [← InfiniteGalois.fixedField_fixingSubgroup (maxUnramifiedOutside K Ω S),
    IntermediateField.mem_fixedField_iff]
  intro g hg
  have h1 : AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) g = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact hg
  have h2 : charAbs χ g = 1 := by rw [charAbs_apply, h1, map_one]
  exact (IntermediateField.mem_fixedField_iff _ _).1 hx g (MonoidHom.mem_ker.2 h2)

theorem isUnramifiedOutside_charField : IsUnramifiedOutside S (charField χ) :=
  (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 (charField_le χ)

theorem charAb_eq_one_of_restrictAb
    {σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω}
    (h : restrictAb (charField χ) (le_maximalAbelianExtension _) σ = 1) : charAb χ σ = 1 := by
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) σ
  rw [restrictAb_restrictNormalHom] at h
  rw [charAb_restrictNormalHom, charAbs_eq_one_iff]
  exact h

theorem sIdeleSubgroupPos_le_ker :
    sIdeleSubgroupPos S ≤ (((charAb χ).comp (artinMap K Ω)).comp (IdeleClassGroup.mk K)).ker := by
  refine sup_le ?_ fun u hu ↦ ?_
  · rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, IdeleClassGroup.mk_diagonal,
      map_one, map_one]
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply]
    apply charAb_eq_one_of_restrictAb
    rw [restrictAb_artinMap, reciprocityMap_mk]
    exact unitsOutsidePos_le_ker_ideleSymbol_of_isUnramifiedOutside S _
      (isUnramifiedOutside_charField χ) hu

def charToSIdelePos : SIdeleClassGroupPos S →* Multiplicative (ZMod n) :=
  QuotientGroup.lift _ (((charAb χ).comp (artinMap K Ω)).comp (IdeleClassGroup.mk K))
    (sIdeleSubgroupPos_le_ker χ)

theorem charToSIdelePos_mk (x : IdeleGroup K) :
    charToSIdelePos χ (SIdeleClassGroupPos.mk S x) = charAb χ (artinMap K Ω (IdeleClassGroup.mk K x)) :=
  rfl

theorem charToSIdelePos_mk_eq (x : IdeleGroup K) (g : Gal(Ω/K))
    (hg : ∀ (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω),
      g y = (artinMap K Ω (IdeleClassGroup.mk K x) ⟨y, hy⟩ : Ω)) :
    charToSIdelePos χ (SIdeleClassGroupPos.mk S x) =
      χ (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) g) := by
  have : AlgEquiv.restrictNormalHom (maximalAbelianExtension K Ω) g =
      artinMap K Ω (IdeleClassGroup.mk K x) :=
    AlgEquiv.ext fun y ↦ Subtype.ext (by rw [AlgEquiv.restrictNormalHom_apply, hg y y.2])
  rw [charToSIdelePos_mk, ← this, charAb_restrictNormalHom]
  rfl

end Character

omit [NumberField K] in

theorem liftNormal_apply_of_mem (σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω)
    (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω) :
    σ.liftNormal Ω y = (σ ⟨y, hy⟩ : Ω) :=
  AlgEquiv.liftNormal_commutes σ Ω ⟨y, hy⟩

variable (K Ω S n) in

def charToSIdelePosHom :
    ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)) →*
      (SIdeleClassGroupPos S →* Multiplicative (ZMod n)) where
  toFun := charToSIdelePos
  map_one' := by
    refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ ?_)
    change charToSIdelePos 1 (SIdeleClassGroupPos.mk S x) = 1
    rw [charToSIdelePos_mk_eq 1 x _ (liftNormal_apply_of_mem _)]
    rfl
  map_mul' χ₁ χ₂ := by
    refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ ?_)
    change charToSIdelePos (χ₁ * χ₂) (SIdeleClassGroupPos.mk S x) =
      charToSIdelePos χ₁ (SIdeleClassGroupPos.mk S x) * charToSIdelePos χ₂ (SIdeleClassGroupPos.mk S x)
    rw [charToSIdelePos_mk_eq _ x _ (liftNormal_apply_of_mem _),
      charToSIdelePos_mk_eq _ x _ (liftNormal_apply_of_mem _),
      charToSIdelePos_mk_eq _ x _ (liftNormal_apply_of_mem _), ContinuousMonoidHom.mul_apply]

variable (S) in

def ofIdeleClassPos : IdeleClassGroup K →* SIdeleClassGroupPos S :=
  QuotientGroup.map _ _ (MonoidHom.id _) le_sup_left

theorem ofIdeleClassPos_mk (x : IdeleGroup K) :
    ofIdeleClassPos S (IdeleClassGroup.mk K x) = SIdeleClassGroupPos.mk S x :=
  rfl

theorem charToSIdelePosHom_injective [IsAlgClosure K Ω] :
    Injective (charToSIdelePosHom K Ω S n) := by
  rw [injective_iff_map_eq_one]
  intro χ hχ
  refine ContinuousMonoidHom.ext fun τ ↦ ?_
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ
  obtain ⟨c, hc⟩ := artinMap_surjective (K := K) (Ω := Ω)
    (AlgEquiv.restrictNormalHom (maximalAbelianExtension K Ω) g)
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  have h := charToSIdelePos_mk_eq (S := S) χ x g fun y hy ↦ by
    rw [hc, AlgEquiv.restrictNormalHom_apply]
  rw [← h]
  exact DFunLike.congr_fun hχ _

theorem charToSIdelePosHom_surjective [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n] :
    Surjective (charToSIdelePosHom K Ω S n) := by
  intro ψ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hn : n ≠ 0 := NeZero.ne n
  set ψC := ψ.comp (ofIdeleClassPos S) with hψC
  have hpow : ∀ c : IdeleClassGroup K, c ^ n ∈ ψC.ker := fun c ↦ by
    rw [MonoidHom.mem_ker, map_pow]
    exact zmod_pow_eq_one _
  have hU : ∀ x ∈ unitsOutsidePos S, IdeleClassGroup.mk K x ∈ ψC.ker := fun x hx ↦ by
    rw [MonoidHom.mem_ker, hψC, MonoidHom.comp_apply, ofIdeleClassPos_mk,
      SIdeleClassGroupPos.mk_eq_one_of_mem S hx, map_one]
  have hNo := isOpen_of_pow_mem_of_unitsOutsidePos hS hn ψC.ker hpow hU
  have := finiteIndex_of_pow_mem_of_unitsOutsidePos hS hn ψC.ker hpow hU
  obtain ⟨E, _, _, hE⟩ :=
    exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex (Ω := Ω) ψC.ker hNo
  have hEu : IsUnramifiedOutside S E := isUnramifiedOutside_of_range_ideleClassNorm hS hn E
    (by rw [hE]; exact hpow) (by rw [hE]; exact hU)
  have hES : E ≤ maxUnramifiedOutside K Ω S :=
    (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).1 hEu
  have hρ : Surjective (reciprocityMap K E) := reciprocityMap_surjective
  have hker : (reciprocityMap K E).ker ≤ ψC.ker := by rw [ker_reciprocityMap, hE]
  let χE : Gal(E/K) →* Multiplicative (ZMod n) :=
    (reciprocityMap K E).liftOfRightInverse (surjInv hρ) (rightInverse_surjInv hρ) ⟨ψC, hker⟩
  have hχE : ∀ c, χE (reciprocityMap K E c) = ψC c := fun c ↦
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c
  let χΩ : Gal(Ω/K) →* Multiplicative (ZMod n) := χE.comp (AlgEquiv.restrictNormalHom E)
  have hχΩc : Continuous χΩ := by
    rw [MonoidHom.coe_comp]
    exact (continuous_of_discreteTopology (f := ⇑χE)).comp (InfiniteGalois.restrictNormalHom_continuous E)
  have hres : RightInverse (fun τ : galUnramifiedOutside K Ω S ↦ τ.liftNormal Ω)
      (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)) := fun τ ↦
    AlgEquiv.restrict_liftNormal (E := Ω) τ
  have hkerS : (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)).ker ≤ χΩ.ker := by
    intro g hg
    rw [IntermediateField.restrictNormalHom_ker] at hg
    have h1 : AlgEquiv.restrictNormalHom E g = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
      exact IntermediateField.fixingSubgroup_antitone hES hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h1, map_one]
  let χS : galUnramifiedOutside K Ω S →* Multiplicative (ZMod n) :=
    (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)).liftOfRightInverse _ hres ⟨χΩ, hkerS⟩
  have hχS : ∀ g, χS (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) g) = χΩ g := fun g ↦
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have hq : Topology.IsQuotientMap
      (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) : Gal(Ω/K) → _) := by
    have : T2Space (galUnramifiedOutside K Ω S) := krullTopology_t2
    have hc := InfiniteGalois.restrictNormalHom_continuous (k := K) (K := Ω)
      (maxUnramifiedOutside K Ω S)
    exact hc.isClosedMap.isQuotientMap hc (AlgEquiv.restrictNormalHom_surjective Ω)
  have hcont : Continuous χS := by
    rw [hq.continuous_iff]
    have : (χS ∘ AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)) = χΩ := funext hχS
    rw [this]
    exact hχΩc
  refine ⟨⟨χS, hcont⟩, QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ ?_)⟩
  set σ := artinMap K Ω (IdeleClassGroup.mk K x)
  change charToSIdelePos _ (SIdeleClassGroupPos.mk S x) = ψ (SIdeleClassGroupPos.mk S x)
  rw [charToSIdelePos_mk_eq _ x (σ.liftNormal Ω) (liftNormal_apply_of_mem σ)]
  change χS _ = _
  rw [hχS]
  have hg' : AlgEquiv.restrictNormalHom (maximalAbelianExtension K Ω) (σ.liftNormal Ω) = σ :=
    AlgEquiv.restrict_liftNormal (E := Ω) σ
  change χE (AlgEquiv.restrictNormalHom E (σ.liftNormal Ω)) = _
  rw [← restrictAb_restrictNormalHom E (le_maximalAbelianExtension E), hg', restrictAb_artinMap, hχE]
  rfl

theorem charToSIdelePosHom_bijective [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n] :
    Bijective (charToSIdelePosHom K Ω S n) :=
  ⟨charToSIdelePosHom_injective, charToSIdelePosHom_surjective hS⟩

variable (Ω) in

def charEquivPos [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n] :
    ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)) ≃*
      (SIdeleClassGroupPos S →* Multiplicative (ZMod n)) :=
  MulEquiv.ofBijective _ (charToSIdelePosHom_bijective hS)

end

end GroundTheory.ProfCoh
