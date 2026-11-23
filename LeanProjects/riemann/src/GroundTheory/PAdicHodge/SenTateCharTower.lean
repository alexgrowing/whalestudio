import Mathlib
import GroundTheory.LocalFields.ConductorMatch
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import GroundTheory.PAdicHodge.FieldOfNormsRam
import GroundTheory.PAdicHodge.SenTateCharUnits
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open CyclNorms GroundTheory.LocalField ValuativeRel

variable {p : ℕ} [hp : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

instance isAlgClosure_padicAlgCl : IsAlgClosure K (PadicAlgCl p) :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K⟩

variable {K} (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ)

def charTowerGal (k : ℕ) : Subgroup Gal(PadicAlgCl p/K) := (unitsOneAdd p k).comap η

theorem mem_charTowerGal {k : ℕ} {σ : Gal(PadicAlgCl p/K)} : σ ∈ charTowerGal η k ↔ η σ ∈ unitsOneAdd p k :=
  Iff.rfl

instance charTowerGal_normal (k : ℕ) : (charTowerGal η k).Normal :=
  Subgroup.Normal.comap (Subgroup.normal_of_isMulCommutative _) η

theorem charTowerGal_antitone : Antitone (charTowerGal η) := fun _ _ h =>
  Subgroup.comap_mono (unitsOneAdd_antitone h)

variable {η}

theorem isOpen_charTowerGal (hη : Continuous η) (k : ℕ) : IsOpen (charTowerGal η k : Set Gal(PadicAlgCl p/K)) :=
  (isOpen_unitsOneAdd k).preimage hη

theorem isClosed_charTowerGal (hη : Continuous η) (k : ℕ) :
    IsClosed (charTowerGal η k : Set Gal(PadicAlgCl p/K)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_charTowerGal hη k)

variable (η)

def charTower (k : ℕ) : IntermediateField K (PadicAlgCl p) :=
  _root_.IntermediateField.fixedField (charTowerGal η k)

theorem charTower_mono : Monotone (charTower η) := fun _ _ h =>
  _root_.IntermediateField.fixedField_antitone (charTowerGal_antitone η h)

variable {η}

theorem fixingSubgroup_charTower (hη : Continuous η) (k : ℕ) :
    (charTower η k).fixingSubgroup = charTowerGal η k :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨charTowerGal η k, isClosed_charTowerGal hη k⟩

theorem finiteDimensional_charTower (hη : Continuous η) (k : ℕ) : FiniteDimensional K (charTower η k) := by
  have h := isOpen_charTowerGal hη k
  rw [← fixingSubgroup_charTower hη k] at h
  exact (InfiniteGalois.isOpen_iff_finite _).1 h

theorem isGalois_charTower (hη : Continuous η) (k : ℕ) : IsGalois K (charTower η k) := by
  rw [← InfiniteGalois.normal_iff_isGalois, fixingSubgroup_charTower hη]
  infer_instance

theorem restrictNormalHom_charTower_eq_one_iff (hη : Continuous η) (k : ℕ)
    [Normal K (charTower η k)] (σ : Gal(PadicAlgCl p/K)) :
    AlgEquiv.restrictNormalHom (charTower η k) σ = 1 ↔ η σ ∈ unitsOneAdd p k := by
  rw [← MonoidHom.mem_ker, (charTower η k).restrictNormalHom_ker, fixingSubgroup_charTower hη]
  rfl

theorem isAbelianGalois_charTower (hη : Continuous η) (k : ℕ) : IsAbelianGalois K (charTower η k) := by
  have := isGalois_charTower hη k
  refine { toIsGalois := inferInstance, toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩ }
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := charTower η k)
    (E := PadicAlgCl p) a
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := charTower η k)
    (E := PadicAlgCl p) b
  rw [← map_mul, ← map_mul, ← div_eq_one, ← map_div]
  rw [restrictNormalHom_charTower_eq_one_iff hη, map_div, map_mul, map_mul, mul_comm (η σ), div_self']
  exact one_mem _

theorem map_mem_charTower (hη : Continuous η) {k : ℕ} (σ : Gal(PadicAlgCl p/K)) {y : PadicAlgCl p}
    (hy : y ∈ charTower η k) : σ y ∈ charTower η k := by
  have := isGalois_charTower hη k
  have h : σ y = ((σ.restrictNormal (charTower η k) ⟨y, hy⟩ : charTower η k) : PadicAlgCl p) :=
    (AlgEquiv.restrictNormal_commutes σ (charTower η k) ⟨y, hy⟩).symm
  rw [h]
  exact SetLike.coe_mem _

section CFT

variable (K) [FiniteDimensional ℚ_[p] K]

def artinGal (n : ℕ) : Subgroup Gal(PadicAlgCl p/K) :=
  ((unitFiltrationUnits K n).map (localArtinMap K (PadicAlgCl p))).comap
    (AlgEquiv.restrictNormalHom (maximalAbelianExtension K (PadicAlgCl p)))

variable (η) in

def artinImage (n : ℕ) : Subgroup ℤ_[p]ˣ := (artinGal K n).map η

variable {K}

theorem artinGal_antitone : Antitone (artinGal K) := fun _ _ h =>
  Subgroup.comap_mono (Subgroup.map_mono (unitFiltrationUnits_antitone h))

variable (η) in
theorem artinImage_antitone : Antitone (artinImage K η) := fun _ _ h =>
  Subgroup.map_mono (artinGal_antitone h)

omit [FiniteDimensional ℚ_[p] K] in

theorem restrictAb_restrictNormalHom (E : IntermediateField K (PadicAlgCl p)) [Normal K E]
    (h : E ≤ maximalAbelianExtension K (PadicAlgCl p)) (ρ : Gal(PadicAlgCl p/K)) :
    restrictAb E h (AlgEquiv.restrictNormalHom (maximalAbelianExtension K (PadicAlgCl p)) ρ) =
      AlgEquiv.restrictNormalHom E ρ := by
  ext x
  rw [restrictAb_apply, AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]

omit [FiniteDimensional ℚ_[p] K] in

theorem eq_one_of_mem_fixingSubgroup_maximalAbelianExtension (hη : Continuous η)
    {ρ : Gal(PadicAlgCl p/K)}
    (hρ : ρ ∈ (maximalAbelianExtension K (PadicAlgCl p)).fixingSubgroup) : η ρ = 1 := by
  rw [fixingSubgroup_maximalAbelianExtension] at hρ
  have hker : (commutator Gal(PadicAlgCl p/K)).topologicalClosure ≤ η.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker η) ?_
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hη
  exact hker hρ

theorem restrictNormalHom_mem_upperRamificationGroup_iff (hη : Continuous η) (k n : ℕ)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)]
    (σ : Gal(PadicAlgCl p/K)) :
    AlgEquiv.restrictNormalHom (charTower η k) σ ∈ upperRamificationGroup K (charTower η k) n ↔
      η σ ∈ artinImage K η n ⊔ unitsOneAdd p k := by
  set M := charTower η k
  set Lab := maximalAbelianExtension K (PadicAlgCl p)
  have hM := le_maximalAbelianExtension M
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap M n, Subgroup.mem_sup]
  constructor
  · rintro ⟨u, hu, huσ⟩
    obtain ⟨ρ, hρ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := Lab)
      (E := PadicAlgCl p) (localArtinMap K (PadicAlgCl p) u)
    have hρA : ρ ∈ artinGal K n := ⟨u, hu, hρ.symm⟩
    refine ⟨η ρ, ⟨ρ, hρA, rfl⟩, η (ρ⁻¹ * σ), ?_, by rw [map_mul, map_inv, mul_inv_cancel_left]⟩
    have h1 : AlgEquiv.restrictNormalHom M (ρ⁻¹ * σ) = 1 := by
      rw [map_mul, map_inv, ← huσ, MonoidHom.comp_apply, ← hρ, restrictAb_restrictNormalHom,
        inv_mul_cancel]
    exact (restrictNormalHom_charTower_eq_one_iff hη k _).1 h1
  · rintro ⟨a, ⟨ρ, hρA, rfl⟩, b, hb, hab⟩
    obtain ⟨u, hu, hu'⟩ := hρA
    refine ⟨u, hu, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom M (ρ⁻¹ * σ) = 1 := by
      refine (restrictNormalHom_charTower_eq_one_iff hη k _).2 ?_
      rw [map_mul, map_inv, ← hab, inv_mul_cancel_left]
      exact hb
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [MonoidHom.comp_apply, hu', restrictAb_restrictNormalHom, h1]

theorem artinImage_add_eq_map_pow (hη : Continuous η) {n e : ℕ}
    (h : (unitFiltrationUnits K n).map (powMonoidHom p) = unitFiltrationUnits K (n + e)) :
    artinImage K η (n + e) = (artinImage K η n).map (powMonoidHom p) := by
  set Lab := maximalAbelianExtension K (PadicAlgCl p)
  ext a
  constructor
  · rintro ⟨ρ, ⟨u, hu, hu'⟩, rfl⟩
    rw [← h] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    obtain ⟨ρw, hρw⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := Lab)
      (E := PadicAlgCl p) (localArtinMap K (PadicAlgCl p) w)
    refine ⟨η ρw, ⟨ρw, ⟨w, hw, hρw.symm⟩, rfl⟩, ?_⟩
    have hfix : ρ⁻¹ * ρw ^ p ∈ Lab.fixingSubgroup := by
      rw [← Lab.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, map_pow, hρw, ← hu',
        powMonoidHom_apply, map_pow, inv_mul_cancel]
    have h1 := eq_one_of_mem_fixingSubgroup_maximalAbelianExtension hη hfix
    rw [map_mul, map_inv, inv_mul_eq_one, map_pow] at h1
    rw [powMonoidHom_apply, h1]
  · rintro ⟨b, ⟨ρ, ⟨w, hw, hw'⟩, rfl⟩, rfl⟩
    refine ⟨ρ ^ p, ⟨w ^ p, ?_, ?_⟩, ?_⟩
    · rw [← h]; exact ⟨w, hw, rfl⟩
    · rw [map_pow, map_pow, hw']
    · rw [map_pow, powMonoidHom_apply]

theorem artinImage_le_of_conductor_le (hη : Continuous η) [FiniteDimensional K (charTower η 2)]
    [IsAbelianGalois K (charTower η 2)] {n : ℕ} (hn : conductor (charTower η 2) ≤ n) :
    artinImage K η n ≤ unitsOneAdd p 2 := by
  rintro _ ⟨ρ, hρ, rfl⟩
  have h1 := (restrictNormalHom_mem_upperRamificationGroup_iff hη 2 n ρ).2
    (Subgroup.mem_sup_left ⟨ρ, hρ, rfl⟩)
  rw [(upperRamificationGroup_natCast_eq_bot_iff (charTower η 2) n).2 hn, Subgroup.mem_bot] at h1
  exact (restrictNormalHom_charTower_eq_one_iff hη 2 ρ).1 h1

end CFT

end SenTateChar

end GroundTheory.PAdicHodge
