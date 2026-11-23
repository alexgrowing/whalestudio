import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.CongruenceSubgroupLeStandardOpenSubgroup
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SPicDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

def unitsOutside : Subgroup (IdeleGroup K) :=
  (⨅ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∈ S), (finiteProj v).ker) ⊓
    ⨅ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S), (unitsLevel v 0).comap (finiteProj v)

variable {S} in
theorem mem_unitsOutside {x : IdeleGroup K} :
    x ∈ unitsOutside S ↔
      (∀ v ∈ S, finiteProj v x = 1) ∧ ∀ v ∉ S, finiteProj v x ∈ unitsLevel v 0 := by
  simp only [unitsOutside, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker,
    Subgroup.mem_comap]

def unitsOutsidePos : Subgroup (IdeleGroup K) :=
  unitsOutside S ⊓ positiveAt Set.univ

variable {S} in
theorem mem_unitsOutsidePos {x : IdeleGroup K} :
    x ∈ unitsOutsidePos S ↔
      x ∈ unitsOutside S ∧ ∀ w : {w : InfinitePlace K // w.IsReal},
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) := by
  rw [unitsOutsidePos, Subgroup.mem_inf, mem_positiveAt]
  simp

theorem unitsOutsidePos_le : unitsOutsidePos S ≤ unitsOutside S := inf_le_left

def sIdeleSubgroup : Subgroup (IdeleGroup K) :=
  (diagonal K).range ⊔ unitsOutside S

def sIdeleSubgroupPos : Subgroup (IdeleGroup K) :=
  (diagonal K).range ⊔ unitsOutsidePos S

theorem sIdeleSubgroupPos_le : sIdeleSubgroupPos S ≤ sIdeleSubgroup S :=
  sup_le_sup_left (unitsOutsidePos_le S) _

abbrev SIdeleClassGroup : Type _ := IdeleGroup K ⧸ sIdeleSubgroup S

abbrev SIdeleClassGroupPos : Type _ := IdeleGroup K ⧸ sIdeleSubgroupPos S

namespace SIdeleClassGroup

def mk : IdeleGroup K →* SIdeleClassGroup S := QuotientGroup.mk' _

theorem mk_surjective : Function.Surjective (mk S) := QuotientGroup.mk'_surjective _

theorem mk_diagonal (a : Kˣ) : mk S (diagonal K a) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_left ⟨a, rfl⟩)

theorem mk_eq_one_of_mem {x : IdeleGroup K} (hx : x ∈ unitsOutside S) : mk S x = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_right hx)

theorem diagonal_range_le : (diagonal K).range ≤ sIdeleSubgroup S := le_sup_left

def ofIdeleClass : IdeleClassGroup K →* SIdeleClassGroup S :=
  QuotientGroup.map _ _ (MonoidHom.id _) (diagonal_range_le S)

end SIdeleClassGroup

namespace SIdeleClassGroupPos

def mk : IdeleGroup K →* SIdeleClassGroupPos S := QuotientGroup.mk' _

theorem mk_surjective : Function.Surjective (mk S) := QuotientGroup.mk'_surjective _

theorem mk_diagonal (a : Kˣ) : mk S (diagonal K a) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_left ⟨a, rfl⟩)

theorem mk_eq_one_of_mem {x : IdeleGroup K} (hx : x ∈ unitsOutsidePos S) : mk S x = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_right hx)

def toSIdeleClassGroup : SIdeleClassGroupPos S →* SIdeleClassGroup S :=
  QuotientGroup.map _ _ (MonoidHom.id _) (sIdeleSubgroupPos_le S)

theorem toSIdeleClassGroup_surjective : Function.Surjective (toSIdeleClassGroup S) := fun y ↦ by
  obtain ⟨x, rfl⟩ := SIdeleClassGroup.mk_surjective S y
  exact ⟨mk S x, rfl⟩

end SIdeleClassGroupPos

def localUniformizer (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
  Units.mk0 (((v.valuation_exists_uniformizer K).choose : K) : v.adicCompletion K) (by
    intro h
    have h' := congrArg Valued.v h
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      (v.valuation_exists_uniformizer K).choose_spec, map_zero] at h'
    exact WithZero.exp_ne_zero h')

theorem valued_localUniformizer (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((localUniformizer v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := by
  rw [localUniformizer, Units.val_mk0, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    (v.valuation_exists_uniformizer K).choose_spec]

def divisorIdele : sDivisor S →+ Additive (IdeleGroup K) :=
  Finsupp.liftAddHom fun v ↦
    zmultiplesHom _ (Additive.ofMul (finiteEmbedding v.1 (localUniformizer v.1)))

theorem divisorIdele_single (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (k : ℤ) :
    Additive.toMul (divisorIdele S (Finsupp.single v k)) =
      finiteEmbedding v.1 (localUniformizer v.1) ^ k := by
  simp [divisorIdele]

def placesIdele [Finite S] : (∀ w : S, (w.1.adicCompletion K)ˣ) →* IdeleGroup K :=
  letI := Fintype.ofFinite S
  { toFun := fun a ↦ ∏ w : S, finiteEmbedding w.1 (a w)
    map_one' := by simp
    map_mul' := fun a b ↦ by
      simp only [Pi.mul_apply, map_mul]
      exact Finset.prod_mul_distrib }

def sPresentation [Finite S] :
    (∀ w : S, (w.1.adicCompletion K)ˣ) × Multiplicative (sDivisor S) →* SIdeleClassGroup S :=
  (SIdeleClassGroup.mk S).comp
    ((placesIdele S).coprod (AddMonoidHom.toMultiplicativeLeft (divisorIdele S)))

theorem sPresentation_apply [Finite S] (a : ∀ w : S, (w.1.adicCompletion K)ˣ)
    (D : Multiplicative (sDivisor S)) :
    sPresentation S (a, D) =
      SIdeleClassGroup.mk S (placesIdele S a * Additive.toMul (divisorIdele S D.toAdd)) :=
  rfl

end

end GroundTheory.ProfCoh
