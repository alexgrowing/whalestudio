import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.General
import GroundTheory.GlobalFields.GlobalReciprocity.Frobenius
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
import GroundTheory.GlobalFields.ClassFieldConsequences.ConductorLocal
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.GlobalFields.Artin.InflationTower

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField WithZero

noncomputable section

section Circle

variable {G : Type*} [Group G] [Finite G]

theorem norm_coe_apply_eq_one (χ : G →* ℂˣ) (g : G) : ‖((χ g : ℂˣ) : ℂ)‖ = 1 := by
  have h : ((χ g : ℂˣ) : ℂ) ^ Nat.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Nat.card_pos.ne'

def toCircleHom (χ : G →* ℂˣ) : G →* Circle where
  toFun g := ⟨(χ g : ℂ), mem_sphere_zero_iff_norm.2 (norm_coe_apply_eq_one χ g)⟩
  map_one' := Circle.ext (by simp)
  map_mul' x y := Circle.ext (by
    change ((χ (x * y) : ℂˣ) : ℂ) = (χ x : ℂ) * (χ y : ℂ)
    rw [map_mul, Units.val_mul])

@[simp]
theorem coe_toCircleHom (χ : G →* ℂˣ) (g : G) : (toCircleHom χ g : ℂ) = χ g :=
  rfl

theorem toCircleHom_eq_one_iff (χ : G →* ℂˣ) (g : G) : toCircleHom χ g = 1 ↔ χ g = 1 := by
  rw [← Circle.coe_eq_one, coe_toCircleHom, Units.val_eq_one]

end Circle

section CharField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

abbrev charField : IntermediateField K L :=
  fixedField χ.ker

def charBar : (charField χ ≃ₐ[K] charField χ) →* ℂˣ :=
  (QuotientGroup.kerLift χ).comp (IsGalois.normalAutEquivQuotient χ.ker).symm.toMonoidHom

@[simp]
theorem charBar_restrictNormalHom (σ : Gal(L/K)) :
    charBar χ (AlgEquiv.restrictNormalHom (charField χ) σ) = χ σ := by
  rw [charBar, MonoidHom.comp_apply, ← IsGalois.normalAutEquivQuotient_apply]
  simp

theorem charBar_injective : Function.Injective (charBar χ) :=
  (QuotientGroup.kerLift_injective χ).comp (MulEquiv.injective _)

instance isMulCommutative_charField : IsMulCommutative (charField χ ≃ₐ[K] charField χ) :=
  ⟨⟨fun a b ↦ charBar_injective χ (by rw [map_mul, map_mul, mul_comm])⟩⟩

theorem restrictNormalHom_eq_one_iff (σ : Gal(L/K)) :
    AlgEquiv.restrictNormalHom (charField χ) σ = 1 ↔ χ σ = 1 := by
  rw [← charBar_restrictNormalHom, ← (charBar_injective χ).eq_iff, map_one]

end CharField

section Hecke

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

def heckeCharacterOfChar : HeckeCharacter K where
  toMonoidHom := (toCircleHom (charBar χ)).comp (reciprocityMap K (charField χ))
  continuous_toFun :=
    (continuous_of_discreteTopology (f := toCircleHom (charBar χ))).comp continuous_reciprocityMap

theorem heckeCharacterOfChar_apply (c : IdeleClassGroup K) :
    (heckeCharacterOfChar χ c : ℂ) = charBar χ (reciprocityMap K (charField χ) c) :=
  rfl

theorem localComponent_heckeCharacterOfChar (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) :
    (heckeCharacterOfChar χ).localComponent v a =
      toCircleHom (charBar χ) (localSymbol (charField χ) v a) := by
  rw [HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]
  change toCircleHom (charBar χ) (reciprocityMap K (charField χ)
    (IdeleClassGroup.mk K (IdeleGroup.finiteEmbedding v a))) = _
  rw [reciprocityMap_mk, ideleSymbol_finiteEmbedding]

end Hecke

section Places

theorem IsArithFrobAt.eq_of_inertia_eq_bot {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] {Q : Ideal S}
    (hI : Q.inertia G = ⊥) {σ σ' : G} (h : IsArithFrobAt R σ Q) (h' : IsArithFrobAt R σ' Q) :
    σ = σ' := by
  have := h.mul_inv_mem_inertia h'
  rwa [hI, Subgroup.mem_bot, mul_inv_eq_one] at this

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

instance liesOver_under_charField :
    w.asIdeal.LiesOver (w.under (𝓞 (charField χ))).asIdeal :=
  ⟨rfl⟩

instance liesOver_under_charField_base :
    (w.under (𝓞 (charField χ))).asIdeal.LiesOver v.asIdeal :=
  Ideal.LiesOver.tower_bot w.asIdeal _ v.asIdeal

theorem inertia_under_charField_eq_bot_iff :
    (w.under (𝓞 (charField χ))).asIdeal.inertia (charField χ ≃ₐ[K] charField χ) = ⊥ ↔
      ∀ σ ∈ w.asIdeal.inertia Gal(L/K), χ σ = 1 := by
  rw [HeightOneSpectrum.under_asIdeal,
    ← map_inertia_restrictNormalHom (F := charField χ) w.asIdeal,
    Subgroup.map_eq_bot_iff]
  refine ⟨fun h σ hσ ↦ (restrictNormalHom_eq_one_iff χ σ).1 (h hσ),
    fun h σ hσ ↦ (restrictNormalHom_eq_one_iff χ σ).2 (h σ hσ)⟩

include v in

theorem ramificationIdx_under_charField_eq_one_iff :
    (w.under (𝓞 (charField χ))).asIdeal.ramificationIdx (𝓞 K) = 1 ↔
      ∀ σ ∈ w.asIdeal.inertia Gal(L/K), χ σ = 1 := by
  rw [← inertia_under_charField_eq_bot_iff χ w, ← natCard_inertia v (w.under (𝓞 (charField χ))),
    Subgroup.card_eq_one]

theorem units_le_ker_localSymbol_charField_iff :
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        (localSymbol (charField χ) v).ker ↔
      ∀ σ ∈ w.asIdeal.inertia Gal(L/K), χ σ = 1 := by
  rw [← ramificationIdx_under_charField_eq_one_iff χ v w,
    ← localConductorExponent_eq_zero_iff (charField χ) v (w.under (𝓞 (charField χ))),
    ← Nat.le_zero, ← unitsLevel_le_ker_localSymbol_iff, unitsLevel_zero]

theorem ker_localComponent_heckeCharacterOfChar :
    ((heckeCharacterOfChar χ).localComponent v : (v.adicCompletion K)ˣ →* Circle).ker =
      (localSymbol (charField χ) v).ker := by
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change (heckeCharacterOfChar χ).localComponent v a = 1 ↔ _
  rw [localComponent_heckeCharacterOfChar, toCircleHom_eq_one_iff, ← map_one (charBar χ),
    (charBar_injective χ).eq_iff]

theorem units_le_ker_localComponent_iff :
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        ((heckeCharacterOfChar χ).localComponent v : (v.adicCompletion K)ˣ →* Circle).ker ↔
      ∀ σ ∈ w.asIdeal.inertia Gal(L/K), χ σ = 1 := by
  rw [ker_localComponent_heckeCharacterOfChar, units_le_ker_localSymbol_charField_iff χ v w]

theorem not_dvd_conductor_heckeCharacterOfChar_iff :
    ¬ v.asIdeal ∣ (heckeCharacterOfChar χ).conductor ↔
      ∀ σ ∈ w.asIdeal.inertia Gal(L/K), χ σ = 1 := by
  rw [HeckeCharacter.not_dvd_conductor_iff, units_le_ker_localComponent_iff χ v w]

theorem localComponent_uniformizer (hχ : ∀ σ ∈ w.asIdeal.inertia Gal(L/K), χ σ = 1)
    {π : (v.adicCompletion K)ˣ} (hπ : Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ))
    {φ : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal) :
    ((heckeCharacterOfChar χ).localComponent v π : ℂ) = χ φ := by
  obtain ⟨π₀, hord, hval⟩ := exists_ord_eq_one_valued v
  have hv := (not_dvd_conductor_heckeCharacterOfChar_iff χ v w).2 hχ
  rw [(heckeCharacterOfChar χ).localComponent_uniformizer_eq hv hπ hval,
    localComponent_heckeCharacterOfChar, coe_toCircleHom]
  have he := (ramificationIdx_under_charField_eq_one_iff χ v w).2 hχ
  have hI := (inertia_under_charField_eq_bot_iff χ w).2 hχ
  rw [localSymbol_eq_arithFrobAt v (w.under (𝓞 (charField χ))) he hord,
    IsArithFrobAt.eq_of_inertia_eq_bot hI (IsArithFrobAt.arithFrobAt _ _ _)
      (IsArithFrobAt.restrictNormalHom (F := charField χ) hφ), charBar_restrictNormalHom]

end Places

end

end GroundTheory.Global
