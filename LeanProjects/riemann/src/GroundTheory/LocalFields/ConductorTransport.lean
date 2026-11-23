import Mathlib
import GroundTheory.LocalFields.UpperNumbering
import GroundTheory.LocalFields.LubinTateTowerMaps
import GroundTheory.LocalFields.SeparableClosure

noncomputable section

open ValuativeRel IsDiscreteValuationRing

namespace GroundTheory.LocalField

section Transport

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L₁ : Type*} [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
  [Algebra K L₁] [ValuativeExtension K L₁] [FiniteDimensional K L₁]
  {L₂ : Type*} [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
  [Algebra K L₂] [ValuativeExtension K L₂] [FiniteDimensional K L₂]

def integerAlgEquivOfAlgEquiv (e : L₁ ≃ₐ[K] L₂) : 𝒪[L₁] ≃ₐ[𝒪[K]] 𝒪[L₂] :=
  AlgEquiv.ofAlgHom (integerAlgHom e.toAlgHom) (integerAlgHom e.symm.toAlgHom)
    (by ext; simp) (by ext; simp)

@[simp]
theorem coe_integerAlgEquivOfAlgEquiv_apply (e : L₁ ≃ₐ[K] L₂) (x : 𝒪[L₁]) :
    (integerAlgEquivOfAlgEquiv e x : L₂) = e x :=
  rfl

omit [IsNonarchimedeanLocalField K] in

theorem addVal_ringEquiv {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (φ : R ≃+* S) (x : R) :
    addVal S (φ x) = addVal R x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have hϖ' : Irreducible (φ ϖ) := (MulEquiv.irreducible_iff (f := (φ : R ≃* S))).mpr hϖ
  rw [map_mul, map_pow, addVal_def' u hϖ n]
  exact addVal_def' (Units.map (φ : R →* S) u) hϖ' n

theorem lowerIndex_autCongr (e : L₁ ≃ₐ[K] L₂) (σ : L₁ ≃ₐ[K] L₁) :
    lowerIndex K L₂ (e.autCongr σ) = lowerIndex K L₁ σ := by
  set φ := integerAlgEquivOfAlgEquiv e
  rw [lowerIndex, lowerIndex, ← φ.toEquiv.iInf_comp]
  refine iInf_congr fun x => ?_
  have h : integerAlgEquiv K L₂ (e.autCongr σ) (φ x) - φ x = φ (integerAlgEquiv K L₁ σ x - x) := by
    apply Subtype.ext
    simp [φ, AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [h]
  exact addVal_ringEquiv (φ : 𝒪[L₁] ≃+* 𝒪[L₂]) _

theorem map_lowerRamificationGroup_autCongr (e : L₁ ≃ₐ[K] L₂) (i : ℤ) :
    (lowerRamificationGroup K L₁ i).map (e.autCongr : (L₁ ≃ₐ[K] L₁) →* (L₂ ≃ₐ[K] L₂)) =
      lowerRamificationGroup K L₂ i := by
  ext τ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [mem_lowerRamificationGroup_iff_lowerIndex] at hσ ⊢
    show _ ≤ lowerIndex K L₂ (e.autCongr σ)
    rw [lowerIndex_autCongr]
    exact hσ
  · intro hτ
    refine ⟨e.autCongr.symm τ, ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [mem_lowerRamificationGroup_iff_lowerIndex] at hτ ⊢
    rw [← lowerIndex_autCongr e, MulEquiv.apply_symm_apply]
    exact hτ

theorem map_lowerRamificationGroupReal_autCongr (e : L₁ ≃ₐ[K] L₂) (t : ℝ) :
    (lowerRamificationGroupReal K L₁ t).map (e.autCongr : (L₁ ≃ₐ[K] L₁) →* (L₂ ≃ₐ[K] L₂)) =
      lowerRamificationGroupReal K L₂ t :=
  map_lowerRamificationGroup_autCongr e _

theorem herbrandPhi_eq_of_algEquiv (e : L₁ ≃ₐ[K] L₂) (u : ℝ) :
    herbrandPhi K L₂ u = herbrandPhi K L₁ u := by
  rcases le_or_gt (-1) u with hu | hu
  · rw [herbrandPhi_eq_sum_lowerIndex hu, herbrandPhi_eq_sum_lowerIndex hu]
    have hcard : Nat.card (lowerRamificationGroup K L₂ 0) = Nat.card (lowerRamificationGroup K L₁ 0) := by
      rw [← map_lowerRamificationGroup_autCongr e 0]
      exact Subgroup.card_map_of_injective e.autCongr.injective
    rw [hcard, ← Fintype.sum_equiv e.autCongr.toEquiv
      (fun σ => enatMin (lowerIndex K L₁ σ) (u + 1))
      (fun τ => enatMin (lowerIndex K L₂ τ) (u + 1))
      (fun σ => by
        show _ = enatMin (lowerIndex K L₂ (e.autCongr σ)) (u + 1)
        rw [lowerIndex_autCongr])]
  · rw [herbrandPhi_of_nonpos (by linarith), herbrandPhi_of_nonpos (by linarith)]

theorem herbrandPsi_eq_of_algEquiv (e : L₁ ≃ₐ[K] L₂) (v : ℝ) :
    herbrandPsi K L₂ v = herbrandPsi K L₁ v := by
  rw [herbrandPsi_eq_iff, herbrandPhi_eq_of_algEquiv e, herbrandPhi_herbrandPsi]

theorem map_upperRamificationGroup_autCongr (e : L₁ ≃ₐ[K] L₂) (v : ℝ) :
    (upperRamificationGroup K L₁ v).map (e.autCongr : (L₁ ≃ₐ[K] L₁) →* (L₂ ≃ₐ[K] L₂)) =
      upperRamificationGroup K L₂ v := by
  rw [upperRamificationGroup, upperRamificationGroup, herbrandPsi_eq_of_algEquiv e,
    map_lowerRamificationGroupReal_autCongr]

theorem upperRamificationGroup_eq_bot_of_ramificationIndex_eq_one [IsGalois K L₁]
    (he : ramificationIndex K L₁ = 1) {v : ℝ} (hv : -1 < v) : upperRamificationGroup K L₁ v = ⊥ := by
  have h0 : lowerRamificationGroup K L₁ 0 = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [card_lowerRamificationGroup_zero, he])
  rw [eq_bot_iff, ← h0, upperRamificationGroup, lowerRamificationGroupReal]
  apply lowerRamificationGroup_antitone
  have h1 : -1 < herbrandPsi K L₁ v := by
    rw [← herbrandPsi_of_nonpos (K := K) (L := L₁) (show (-1 : ℝ) ≤ 0 by norm_num)]
    exact herbrandPsi_strictMono hv
  exact Int.le_ceil_iff.mpr (by push_cast; linarith)

end Transport

section Restrict

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  {L M : IntermediateField K Ω} [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L]
  [IsGalois K M]

theorem map_upperRamificationGroup_restrictAut (h : L ≤ M) (v : ℝ) :
    (upperRamificationGroup K M v).map (restrictAut h) = upperRamificationGroup K L v := by
  set R := IntermediateField.restrict h
  let e : L ≃ₐ[K] R := IntermediateField.restrictAlgEquiv h
  have : IsGalois K R := IsGalois.of_algEquiv e
  have hH := map_upperRamificationGroup (K := K) (L := M) R v
  have hT := map_upperRamificationGroup_autCongr e.symm v
  have key : ∀ y : R, ((e.symm y : L) : Ω) = ((y : M) : Ω) := fun y => by
    conv_rhs => rw [← e.apply_symm_apply y]
    rfl
  have hcomp : (e.symm.autCongr : (R ≃ₐ[K] R) →* (L ≃ₐ[K] L)).comp
      (AlgEquiv.restrictNormalHom R) = restrictAut h := by
    ext σ x
    rw [restrictAut_apply]
    show ((e.symm ((σ.restrictNormal R) (e x)) : L) : Ω) = _
    rw [key]
    have h1 := AlgEquiv.restrictNormal_commutes σ R (e x)
    have h2 : (algebraMap R M (σ.restrictNormal R (e x)) : M) = ((σ.restrictNormal R (e x) : R) : M) :=
      rfl
    rw [← h2, h1]
    rfl
  rw [← hT, ← hH, Subgroup.map_map, hcomp]

end Restrict

end GroundTheory.LocalField
