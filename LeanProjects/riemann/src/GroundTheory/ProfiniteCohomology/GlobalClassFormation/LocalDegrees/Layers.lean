import Mathlib
import GroundTheory.GlobalFields.CyclotomicCharacters.Degree
import GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicCompositum
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.Cyclotomic FiniteSubfield GroundTheory.LocalField.Abstract

open scoped GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace CyclotomicLayer

def degreeMod (r : ℕ+) : Gal(ℚ̄/ℚ) →* Multiplicative (ZMod r) :=
  (AddMonoidHom.toMultiplicative (ProfiniteInteger.proj r).toAddMonoidHom).comp degree

theorem toAdd_degreeMod (r : ℕ+) (σ : Gal(ℚ̄/ℚ)) :
    Multiplicative.toAdd (degreeMod r σ) = ProfiniteInteger.proj r (Multiplicative.toAdd (degree σ)) :=
  rfl

theorem mem_ker_degreeMod (r : ℕ+) (σ : Gal(ℚ̄/ℚ)) :
    σ ∈ (degreeMod r).ker ↔ ProfiniteInteger.proj r (Multiplicative.toAdd (degree σ)) = 0 := by
  rw [MonoidHom.mem_ker, ← toAdd_degreeMod, toAdd_eq_zero]

theorem isOpen_ker_degreeMod (r : ℕ+) : IsOpen ((degreeMod r).ker : Set Gal(ℚ̄/ℚ)) := by
  have h : ((degreeMod r).ker : Set Gal(ℚ̄/ℚ)) =
      (fun σ => ProfiniteInteger.proj r (Multiplicative.toAdd (degree σ))) ⁻¹' {0} := by
    ext σ
    exact mem_ker_degreeMod r σ
  rw [h]
  exact (isOpen_discrete _).preimage
    ((ProfiniteInteger.continuous_proj r).comp (continuous_toAdd.comp continuous_degree))

theorem isClosed_ker_degreeMod (r : ℕ+) : IsClosed ((degreeMod r).ker : Set Gal(ℚ̄/ℚ)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_ker_degreeMod r)

def zhatLayerField (r : ℕ+) : IntermediateField ℚ ℚ̄ :=
  fixedField (degreeMod r).ker

theorem fixingSubgroup_zhatLayerField (r : ℕ+) :
    (zhatLayerField r).fixingSubgroup = (degreeMod r).ker :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨(degreeMod r).ker, isClosed_ker_degreeMod r⟩

theorem finiteDimensional_zhatLayerField (r : ℕ+) : FiniteDimensional ℚ (zhatLayerField r) := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  refine (InfiniteGalois.isOpen_iff_finite _).1 ?_
  change IsOpen ((zhatLayerField r).fixingSubgroup : Set Gal(ℚ̄/ℚ))
  rw [fixingSubgroup_zhatLayerField]
  exact isOpen_ker_degreeMod r

def zhatLayer (r : ℕ+) : FiniteSubfield :=
  ⟨zhatLayerField r, finiteDimensional_zhatLayerField r⟩

theorem zhatLayer_coe (r : ℕ+) : (zhatLayer r).1 = zhatLayerField r :=
  rfl

instance isGalois_zhatLayer (r : ℕ+) : IsGalois ℚ (zhatLayer r).1 := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  refine (InfiniteGalois.normal_iff_isGalois _).1 ?_
  change (zhatLayerField r).fixingSubgroup.Normal
  rw [fixingSubgroup_zhatLayerField]
  infer_instance

theorem zhatLayerField_le_zhatField (r : ℕ+) : zhatLayerField r ≤ zhatField := by
  intro x hx
  rw [zhatLayerField, mem_fixedField_iff] at hx
  rw [zhatField, mem_fixedField_iff]
  intro f hf
  refine hx f ?_
  rw [mem_ker_degreeMod, MonoidHom.mem_ker.1 hf, toAdd_one, map_zero]

variable (K : FiniteSubfield) (r : ℕ+)

abbrev cyclotomicLayer : FiniteSubfield :=
  CyclotomicSymbol.compositum K (zhatLayer r)

instance isGalois_cyclotomicLayer : IsGalois K.1 (cyclotomicLayer K r).1 :=
  CyclotomicSymbol.isGalois_compositum K (zhatLayer r)

theorem cyclotomicLayer_le : (cyclotomicLayer K r).1 ≤ K.1 ⊔ zhatField :=
  sup_le_sup_left (zhatLayerField_le_zhatField r) K.1

theorem mem_fixingSubgroup_cyclotomicLayer_iff (g : K.1.fixingSubgroup) :
    (g : Gal(ℚ̄/ℚ)) ∈ (cyclotomicLayer K r).1.fixingSubgroup ↔ degreeMod r g = 1 := by
  rw [CyclotomicSymbol.fixingSubgroup_compositum, Subgroup.mem_inf, zhatLayer_coe,
    fixingSubgroup_zhatLayerField, MonoidHom.mem_ker]
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

def degreeModK : K.1.fixingSubgroup →* Multiplicative (ZMod r) :=
  (degreeMod r).comp K.1.fixingSubgroup.subtype

theorem ker_restrictHom_cyclotomicLayer :
    (restrictHom (F := K) (E := cyclotomicLayer K r)).ker = (degreeModK K r).ker := by
  ext g
  rw [ker_restrictHom, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  exact mem_fixingSubgroup_cyclotomicLayer_iff K r g

def layerDegree : Gal((cyclotomicLayer K r).1/K.1) →* Multiplicative (ZMod r) :=
  (QuotientGroup.lift _ (degreeModK K r) (ker_restrictHom_cyclotomicLayer K r).le).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (restrictHom_surjective (F := K) (E := cyclotomicLayer K r))).symm.toMonoidHom

theorem layerDegree_restrictHom (g : K.1.fixingSubgroup) :
    layerDegree K r (restrictHom (E := cyclotomicLayer K r) g) = degreeMod r g := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _
      (restrictHom_surjective (F := K) (E := cyclotomicLayer K r))).symm
        (restrictHom (E := cyclotomicLayer K r) g) = (g : _ ⧸ _) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [layerDegree, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk]
  rfl

theorem layerDegree_injective : Function.Injective (layerDegree K r) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  obtain ⟨g, rfl⟩ := restrictHom_surjective (F := K) (E := cyclotomicLayer K r) σ
  rw [layerDegree_restrictHom] at hσ
  rw [← MonoidHom.mem_ker, ker_restrictHom_cyclotomicLayer, MonoidHom.mem_ker]
  exact hσ

instance isCyclic_cyclotomicLayer : IsCyclic Gal((cyclotomicLayer K r).1/K.1) :=
  isCyclic_of_injective (layerDegree K r) (layerDegree_injective K r)

end CyclotomicLayer

end

end GroundTheory.ProfCoh
