import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem idx_GK {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (Om l)) :
    K.fixingSubgroup.index = finrank ℚ_[l] K :=
  (IntermediateField.finrank_eq_fixingSubgroup_index (Om l) K).symm

private theorem sup_Iq {l : ℕ} [Fact l.Prime] (K : FinExt l) :
    GK K ⊔ Iq l = (K0 K).fixingSubgroup := by
  haveI := K.2
  have ho : IsOpen ((GK K ⊔ Iq l : Subgroup (GQ l)) : Set (GQ l)) :=
    Subgroup.isOpen_mono le_sup_left (IntermediateField.fixingSubgroup_isOpen K.1)
  have hc := Subgroup.isClosed_of_isOpen _ ho
  have h1 := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ_[l]) (K := Om l) ⟨GK K ⊔ Iq l, hc⟩
  have h2 : IntermediateField.fixedField (GK K ⊔ Iq l) = K0 K := by
    apply le_antisymm
    · refine le_inf ?_ ?_
      · rw [← InfiniteGalois.fixedField_fixingSubgroup K.1]
        exact IntermediateField.fixedField_le le_sup_left
      · rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l)]
        exact IntermediateField.fixedField_le le_sup_right
    · rw [IntermediateField.le_iff_le]
      exact sup_le (IntermediateField.fixingSubgroup_le inf_le_left)
        (IntermediateField.fixingSubgroup_le inf_le_right)
  rw [← h2]
  exact h1.symm

theorem UpperTheory.V.Loc.isCrIff :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (ρ : Representation A ↥(GK K) V), (IsCr (GK K).subtype ρ ↔ Crys K ρ) ∧ (IsDr (GK K).subtype ρ ↔ DeRham K ρ) := by
  intro l _ K A _ _ V _ _ _ _ ρ
  have hC : Dcr (GK K).subtype (resCoef ℚ_[l] ρ) = Dcris ((PP l).PD K) (resCoef ℚ_[l] ρ) := by
    unfold Dcr Dcris
    refine iInf_congr fun g => ?_
    have : actC (GK K).subtype (resCoef ℚ_[l] ρ) g = actVB ((PP l).PD K) (resCoef ℚ_[l] ρ) g := by
      unfold actC actVB
      congr 1
      ext b
      exact ((PP l).PD_actB K g b).symm
    rw [this]
  have hD : Ddr (GK K).subtype (resCoef ℚ_[l] ρ) = DdR ((PP l).PD K) (resCoef ℚ_[l] ρ) := by
    unfold Ddr DdR
    refine iInf_congr fun g => ?_
    have : actD (GK K).subtype (resCoef ℚ_[l] ρ) g = actVdR ((PP l).PD K) (resCoef ℚ_[l] ρ) g := by
      unfold actD actVdR
      congr 1
      ext b
      exact ((PP l).PD_actdR K g b).symm
    rw [this]
  constructor
  · unfold IsCr Crys IsCrys
    rw [hC, Subgroup.range_subtype, sup_Iq, idx_GK]
  · unfold IsDr DeRham IsDR
    rw [hD, Subgroup.range_subtype, show (GK K).index = finrank ℚ_[l] K.1 from idx_GK K.1]
