import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary
import GroundTheory.GlobalFields.IdeleGroups.UnitBound

open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

section Completions

open NumberField.InfinitePlace.Completion

def realUnitsHom {w : InfinitePlace K} (hw : w.IsReal) : ℝˣ →ₜ* (w.Completion)ˣ where
  toMonoidHom := Units.map ((ringEquivRealOfIsReal hw).symm : ℝ →+* w.Completion).toMonoidHom
  continuous_toFun := Units.continuous_map (isometryEquivRealOfIsReal hw).symm.continuous

def complexUnitsHom {w : InfinitePlace K} (hw : w.IsComplex) : ℂˣ →ₜ* (w.Completion)ˣ where
  toMonoidHom := Units.map ((ringEquivComplexOfIsComplex hw).symm : ℂ →+* w.Completion).toMonoidHom
  continuous_toFun := Units.continuous_map (isometryEquivComplexOfIsComplex hw).symm.continuous

omit [NumberField K] in
theorem extensionEmbeddingOfIsReal_realUnitsHom {w : InfinitePlace K} (hw : w.IsReal) (x : ℝˣ) :
    extensionEmbeddingOfIsReal hw ((realUnitsHom hw x : (w.Completion)ˣ) : w.Completion) = x := by
  rw [← ringEquivRealOfIsReal_apply]
  exact (ringEquivRealOfIsReal hw).apply_symm_apply _

omit [NumberField K] in

theorem realUnitsHom_surjective {w : InfinitePlace K} (hw : w.IsReal) (a : (w.Completion)ˣ) :
    realUnitsHom hw (Units.map (ringEquivRealOfIsReal hw : w.Completion →+* ℝ).toMonoidHom a) = a :=
  Units.ext ((ringEquivRealOfIsReal hw).symm_apply_apply _)

omit [NumberField K] in

theorem complexUnitsHom_surjective {w : InfinitePlace K} (hw : w.IsComplex) (a : (w.Completion)ˣ) :
    complexUnitsHom hw
      (Units.map (ringEquivComplexOfIsComplex hw : w.Completion →+* ℂ).toMonoidHom a) = a :=
  Units.ext ((ringEquivComplexOfIsComplex hw).symm_apply_apply _)

end Completions

namespace IdeleGroup

def ofInfinite : (InfiniteAdeleRing K)ˣ →* IdeleGroup K :=
  (ContinuousMulEquiv.symm (prodEquiv K)).toMulEquiv.toMonoidHom.comp (MonoidHom.inl _ _)

@[simp]
theorem toInfinite_ofInfinite (x : (InfiniteAdeleRing K)ˣ) : toInfinite K (ofInfinite x) = x := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (x, 1))).1 = x
  rw [ContinuousMulEquiv.apply_symm_apply]

@[simp]
theorem toFinite_ofInfinite (x : (InfiniteAdeleRing K)ˣ) : toFinite K (ofInfinite x) = 1 := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (x, 1))).2 = 1
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem ofFinite_mul_ofInfinite (x : IdeleGroup K) :
    ofFinite (toFinite K x) * ofInfinite (toInfinite K x) = x := by
  apply (prodEquiv K).injective
  refine Prod.ext ?_ ?_
  · change toInfinite K (ofFinite (toFinite K x) * ofInfinite (toInfinite K x)) = toInfinite K x
    rw [map_mul, toInfinite_ofFinite, toInfinite_ofInfinite, one_mul]
  · change toFinite K (ofFinite (toFinite K x) * ofInfinite (toInfinite K x)) = toFinite K x
    rw [map_mul, toFinite_ofFinite, toFinite_ofInfinite, mul_one]

def infiniteComponent (w : InfinitePlace K) : (InfiniteAdeleRing K)ˣ →* (w.Completion)ˣ :=
  Units.map (Pi.evalMonoidHom (fun u : InfinitePlace K ↦ u.Completion) w)

omit [NumberField K] in
@[simp]
theorem coe_infiniteComponent (w : InfinitePlace K) (x : (InfiniteAdeleRing K)ˣ) :
    ((infiniteComponent w x : (w.Completion)ˣ) : w.Completion) = (x : InfiniteAdeleRing K) w :=
  rfl

theorem ofInfinite_map_infiniteAdeleSingle (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ofInfinite (Units.map (infiniteAdeleSingle w) a) = infiniteEmbedding w a :=
  Units.ext rfl

theorem prod_map_infiniteAdeleSingle (x : (InfiniteAdeleRing K)ˣ) :
    ∏ w, Units.map (infiniteAdeleSingle w) (infiniteComponent w x) = x := by
  classical
  apply Units.ext
  rw [Units.coe_prod]
  exact Finset.univ_prod_mulSingle (fun w : InfinitePlace K ↦ (x : InfiniteAdeleRing K) w)

theorem ofInfinite_eq_prod (x : (InfiniteAdeleRing K)ˣ) :
    ofInfinite x = ∏ w, infiniteEmbedding w (infiniteComponent w x) := by
  conv_lhs => rw [← prod_map_infiniteAdeleSingle x]
  rw [map_prod]
  simp only [ofInfinite_map_infiniteAdeleSingle]

variable (K) in

def infinitePositive : Subgroup (InfiniteAdeleRing K)ˣ where
  carrier := {x | ∀ (w : InfinitePlace K) (hw : w.IsReal),
    0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((x : InfiniteAdeleRing K) w)}
  one_mem' w hw := by
    show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (1 : w.Completion)
    rw [map_one]
    exact one_pos
  mul_mem' {a b} ha hb w hw := by
    show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      ((a : InfiniteAdeleRing K) w * (b : InfiniteAdeleRing K) w)
    rw [map_mul]
    exact mul_pos (ha w hw) (hb w hw)
  inv_mem' {a} ha w hw := by
    have h0 : ((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w *
        (a : InfiniteAdeleRing K) w = 1 :=
      congrFun a.inv_mul w
    have h1 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w) *
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((a : InfiniteAdeleRing K) w) = 1 := by
      rw [← map_mul, h0, map_one]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_pos.2 (ha w hw)

omit [NumberField K] in
theorem mem_infinitePositive {x : (InfiniteAdeleRing K)ˣ} :
    x ∈ infinitePositive K ↔ ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((x : InfiniteAdeleRing K) w) :=
  Iff.rfl

variable (K) in

def infiniteSign : (InfiniteAdeleRing K)ˣ →* ({w : InfinitePlace K // w.IsReal} → SignTypeˣ) :=
  MonoidHom.pi fun w ↦ (Units.map (signHom : ℝ →*₀ SignType).toMonoidHom).comp
    ((Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 :
      w.1.Completion →+* ℝ).toMonoidHom).comp (infiniteComponent w.1))

omit [NumberField K] in
theorem infiniteSign_apply_val (x : (InfiniteAdeleRing K)ˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    ((infiniteSign K x w : SignTypeˣ) : SignType) =
      SignType.sign (InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((x : InfiniteAdeleRing K) w.1)) :=
  rfl

omit [NumberField K] in

theorem infinitePositive_eq_ker : infinitePositive K = (infiniteSign K).ker := by
  ext x
  rw [mem_infinitePositive, MonoidHom.mem_ker]
  constructor
  · intro h
    funext w
    apply Units.ext
    rw [infiniteSign_apply_val, Pi.one_apply, Units.val_one, sign_eq_one_iff]
    exact h w.1 w.2
  · intro h w hw
    have h' := congrArg Units.val (congrFun h ⟨w, hw⟩)
    rwa [infiniteSign_apply_val, Pi.one_apply, Units.val_one, sign_eq_one_iff] at h'

instance : (infinitePositive K).FiniteIndex := by
  rw [infinitePositive_eq_ker]
  exact Subgroup.finiteIndex_ker _

variable (K) in

def rayGroup (𝔪 : Ideal (𝓞 K)) : Subgroup (IdeleGroup K) :=
  (diagonal K).range ⊔ (idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite

theorem map_idealLevel_le_standardOpenSubgroup (𝔪 : Ideal (𝓞 K)) :
    (idealLevel 𝔪).map ofFinite ≤ standardOpenSubgroup K := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_standardOpenSubgroup_iff_toFinite_mem, toFinite_ofFinite]
  exact finiteLevel_le_finiteLevel_zero _ hx

theorem map_infinitePositive_le_standardOpenSubgroup :
    (infinitePositive K).map ofInfinite ≤ standardOpenSubgroup K := by
  rintro _ ⟨x, -, rfl⟩
  rw [mem_standardOpenSubgroup_iff_toFinite_mem, toFinite_ofInfinite]
  exact one_mem _

theorem rayGroup_le (𝔪 : Ideal (𝓞 K)) :
    rayGroup K 𝔪 ≤ (diagonal K).range ⊔ standardOpenSubgroup K :=
  sup_le (sup_le le_sup_left ((map_idealLevel_le_standardOpenSubgroup 𝔪).trans le_sup_right))
    (map_infinitePositive_le_standardOpenSubgroup.trans le_sup_right)

theorem finite_quotient_idealLevel {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    Finite (finiteLevel (K := K) 0 ⧸ (idealLevel 𝔪).subgroupOf (finiteLevel 0)) := by
  have hc : IsCompact (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
    convert isCompact_finite_units_integral K using 1
    ext x
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq, mem_finiteLevel]
    refine forall_congr' fun v ↦ ?_
    rw [Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff]
    rfl
  have : CompactSpace (finiteLevel (K := K) 0) := isCompact_iff_compactSpace.1 hc
  have hm : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      v.asIdeal ^ multiplicity v.asIdeal 𝔪 := by
    simpa only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity h𝔪] using
      Ideal.hasFiniteMulSupport h𝔪
  have hs : (support fun v : HeightOneSpectrum (𝓞 K) ↦ multiplicity v.asIdeal 𝔪).Finite := by
    rw [← mulSupport_asIdeal_pow]
    exact hm
  exact Subgroup.quotient_finite_of_isOpen _
    ((isOpen_finiteLevel hs).preimage continuous_subtype_val)

def standardOpenInfiniteHom : standardOpenSubgroup K →* (InfiniteAdeleRing K)ˣ ⧸ infinitePositive K :=
  (QuotientGroup.mk' _).comp ((toInfinite K).comp (standardOpenSubgroup K).subtype)

def standardOpenFiniteHom (𝔪 : Ideal (𝓞 K)) :
    standardOpenSubgroup K →* finiteLevel (K := K) 0 ⧸ (idealLevel 𝔪).subgroupOf (finiteLevel 0) :=
  (QuotientGroup.mk' _).comp (((toFinite K).comp (standardOpenSubgroup K).subtype).codRestrict _
    fun u ↦ (mem_standardOpenSubgroup_iff_toFinite_mem _).1 u.2)

theorem ker_inf_ker_le (𝔪 : Ideal (𝓞 K)) :
    (standardOpenInfiniteHom (K := K)).ker ⊓ (standardOpenFiniteHom 𝔪).ker ≤
      ((idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite).subgroupOf
        (standardOpenSubgroup K) := by
  intro u hu
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hu
  rw [MonoidHom.mem_ker, standardOpenInfiniteHom, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [MonoidHom.mem_ker, standardOpenFiniteHom, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  rw [Subgroup.mem_subgroupOf, ← ofFinite_mul_ofInfinite (u : IdeleGroup K)]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, h2, rfl⟩) (Subgroup.mem_sup_right ⟨_, h1, rfl⟩)

end IdeleGroup

open IdeleGroup

variable (K) in

abbrev RayClassGroup (𝔪 : Ideal (𝓞 K)) : Type _ := IdeleGroup K ⧸ rayGroup K 𝔪

theorem RayClassGroup.finite {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (RayClassGroup K 𝔪) := by
  set R := rayGroup K 𝔪
  set U := standardOpenSubgroup K
  set M := (diagonal K).range ⊔ U

  have hM : M.FiniteIndex := by
    rw [show M = (IdeleGroup.toClassGroup (K := K)).ker from (ker_toClassGroup).symm]
    exact Subgroup.finiteIndex_ker _

  have : Finite ((InfiniteAdeleRing K)ˣ ⧸ infinitePositive K) :=
    Subgroup.finite_quotient_of_finiteIndex
  have : Finite (finiteLevel (K := K) 0 ⧸ (idealLevel 𝔪).subgroupOf (finiteLevel 0)) :=
    finite_quotient_idealLevel h𝔪
  have : Finite (standardOpenInfiniteHom (K := K)).range :=
    Finite.of_injective _ Subtype.val_injective
  have : Finite (standardOpenFiniteHom (K := K) 𝔪).range :=
    Finite.of_injective _ Subtype.val_injective
  have : (standardOpenInfiniteHom (K := K)).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have : (standardOpenFiniteHom (K := K) 𝔪).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have h2 : (((idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite).subgroupOf
      U).FiniteIndex := Subgroup.finiteIndex_of_le (ker_inf_ker_le 𝔪)
  have hWP : (idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite ≤ R :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have h3 : (R.subgroupOf U).FiniteIndex :=
    Subgroup.finiteIndex_of_le fun x hx ↦ Subgroup.mem_subgroupOf.2 (hWP (Subgroup.mem_subgroupOf.1 hx))

  have hUR : U ⊔ R = M :=
    le_antisymm (sup_le le_sup_right (rayGroup_le 𝔪))
      (sup_le ((le_sup_left.trans le_sup_left).trans le_sup_right) le_sup_left)
  have hRM : R.relIndex M ≠ 0 := by
    rw [← hUR, Subgroup.relIndex_sup_right]
    exact h3.index_ne_zero
  have hR : R.index ≠ 0 := by
    rw [← Subgroup.relIndex_mul_index (rayGroup_le 𝔪)]
    exact mul_ne_zero hRM hM.index_ne_zero
  exact Subgroup.index_ne_zero_iff_finite.1 hR

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def realComponent {w : InfinitePlace K} (hw : w.IsReal) : ℝˣ →ₜ* Circle :=
  (χ.infiniteComponent w).comp (realUnitsHom hw)

def complexComponent {w : InfinitePlace K} (hw : w.IsComplex) : ℂˣ →ₜ* Circle :=
  (χ.infiniteComponent w).comp (complexUnitsHom hw)

def realParam {w : InfinitePlace K} (hw : w.IsReal) : Fin 2 × ℝ :=
  (existsUnique_realUnits_circle (χ.realComponent hw)).exists.choose

def complexParam {w : InfinitePlace K} (hw : w.IsComplex) : ℤ × ℝ :=
  (existsUnique_complexUnits_circle (χ.complexComponent hw)).exists.choose

end HeckeCharacter

end

end GroundTheory.Global
