import Mathlib
import GroundTheory.LocalFields.ConductorTransport
import GroundTheory.LocalFields.SeparableClosure
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel IntermediateField

section AbsUpper

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

def absUpper (u : ℝ) : Subgroup Gal(Ω/K) where
  carrier := {σ | ∀ M : FiniteGaloisIntermediateField K Ω,
    AlgEquiv.restrictNormalHom (M : IntermediateField K Ω) σ ∈
      upperRamificationGroup K (M : IntermediateField K Ω) u}
  one_mem' M := by rw [map_one]; exact one_mem _
  mul_mem' hσ hτ M := by rw [map_mul]; exact mul_mem (hσ M) (hτ M)
  inv_mem' hσ M := by rw [map_inv]; exact inv_mem (hσ M)

variable {K Ω}

variable (K Ω) in

theorem absUpper_antitone : Antitone (absUpper K Ω) :=
  fun _ _ h _ hσ M ↦ upperRamificationGroup_antitone K _ h (hσ M)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

theorem restrictAut_restrictNormalHom {M M' : IntermediateField K Ω} [Normal K M] [Normal K M']
    (h : M ≤ M') (σ : Gal(Ω/K)) :
    restrictAut h (AlgEquiv.restrictNormalHom M' σ) = AlgEquiv.restrictNormalHom M σ := by
  ext x
  rw [restrictAut_apply, AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]

theorem restrictNormalHom_mem_of_le {M M' : FiniteGaloisIntermediateField K Ω}
    (h : (M : IntermediateField K Ω) ≤ M') {u : ℝ} {σ : Gal(Ω/K)}
    (hσ : AlgEquiv.restrictNormalHom (M' : IntermediateField K Ω) σ ∈
      upperRamificationGroup K (M' : IntermediateField K Ω) u) :
    AlgEquiv.restrictNormalHom (M : IntermediateField K Ω) σ ∈
      upperRamificationGroup K (M : IntermediateField K Ω) u := by
  rw [← map_upperRamificationGroup_restrictAut h u, ← restrictAut_restrictNormalHom h]
  exact Subgroup.mem_map_of_mem _ hσ

variable [IsGalois K Ω]

theorem map_absUpper (M : FiniteGaloisIntermediateField K Ω) (u : ℝ) :
    (absUpper K Ω u).map (AlgEquiv.restrictNormalHom (M : IntermediateField K Ω)) =
      upperRamificationGroup K (M : IntermediateField K Ω) u := by
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact hσ M
  intro τ hτ

  let t : FiniteGaloisIntermediateField K Ω → Set Gal(Ω/K) := fun M' ↦
    {σ | AlgEquiv.restrictNormalHom (M : IntermediateField K Ω) σ = τ ∧
      AlgEquiv.restrictNormalHom (M' : IntermediateField K Ω) σ ∈
        upperRamificationGroup K (M' : IntermediateField K Ω) u}
  have hmono : ∀ {M₁ M₂ : FiniteGaloisIntermediateField K Ω}, M₁ ≤ M₂ → t M₂ ⊆ t M₁ :=
    fun h σ hσ ↦ ⟨hσ.1, restrictNormalHom_mem_of_le h hσ.2⟩
  have hdir : Directed (· ⊇ ·) t := fun M₁ M₂ ↦
    ⟨M₁ ⊔ M₂, hmono le_sup_left, hmono le_sup_right⟩
  have hne : ∀ M', (t M').Nonempty := by
    intro M'
    let M'' := M ⊔ M'
    have hMM : (M : IntermediateField K Ω) ≤ M'' := (le_sup_left : M ≤ M'')
    rw [← map_upperRamificationGroup_restrictAut hMM u] at hτ
    obtain ⟨ρ, hρ, rfl⟩ := hτ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
      (K₁ := (M'' : IntermediateField K Ω)) Ω ρ
    refine ⟨σ, (restrictAut_restrictNormalHom hMM σ).symm, ?_⟩
    exact restrictNormalHom_mem_of_le (le_sup_right : M' ≤ M'') hρ
  have hcl : ∀ M', IsClosed (t M') := by
    intro M'
    have h1 : IsClosed {σ : Gal(Ω/K) | AlgEquiv.restrictNormalHom (M : IntermediateField K Ω) σ = τ} :=
      isClosed_eq (InfiniteGalois.restrictNormalHom_continuous _) continuous_const
    have h2 : IsClosed {σ : Gal(Ω/K) | AlgEquiv.restrictNormalHom (M' : IntermediateField K Ω) σ ∈
        upperRamificationGroup K (M' : IntermediateField K Ω) u} :=
      (Set.toFinite _).isClosed.preimage (InfiniteGalois.restrictNormalHom_continuous _)
    exact h1.inter h2
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
    (fun M' ↦ (hcl M').isCompact) hcl
  rw [Set.mem_iInter] at hσ
  exact ⟨σ, fun M' ↦ (hσ M').2, (hσ M).1⟩

instance absUpper_normal (u : ℝ) : (absUpper K Ω u).Normal where
  conj_mem n hn g M := by
    have : (upperRamificationGroup K (M : IntermediateField K Ω) u).Normal := by
      unfold upperRamificationGroup lowerRamificationGroupReal; infer_instance
    rw [map_mul, map_mul, map_inv]
    exact this.conj_mem _ (hn M) _

end AbsUpper

section APF

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  (L : IntermediateField K Ω)

def upperSupFixing (u : ℝ) : Subgroup Gal(Ω/K) :=
  absUpper K Ω u ⊔ L.fixingSubgroup

def IsAPF : Prop :=
  ∀ u : ℝ, IsOpen (upperSupFixing K Ω L u : Set Gal(Ω/K))

def apfIndex (u : ℝ) : ℕ :=
  (upperSupFixing K Ω L u).relIndex (absUpper K Ω 0)

def apfPsi (u : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..u, (apfIndex K Ω L w : ℝ)

def IsStrictlyAPF : Prop :=
  IsAPF K Ω L ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ u in Filter.atTop, c * apfIndex K Ω L u ≤ apfPsi K Ω L u

def upperField (u : ℝ) : IntermediateField K Ω :=
  fixedField (upperSupFixing K Ω L u)

variable {K Ω L}

theorem fixingSubgroup_le_upperSupFixing (u : ℝ) : L.fixingSubgroup ≤ upperSupFixing K Ω L u :=
  le_sup_right

theorem absUpper_le_upperSupFixing (u : ℝ) : absUpper K Ω u ≤ upperSupFixing K Ω L u :=
  le_sup_left

theorem upperSupFixing_antitone : Antitone (upperSupFixing K Ω L) :=
  fun _ _ h ↦ sup_le_sup_right (absUpper_antitone K Ω h) _

variable [IsGalois K Ω]

theorem finiteIndex_of_isOpen (H : Subgroup Gal(Ω/K)) (h : IsOpen (H : Set Gal(Ω/K))) :
    H.FiniteIndex := by
  have := Subgroup.quotient_finite_of_isOpen H h
  exact Subgroup.finiteIndex_of_finite_quotient

theorem relIndex_ne_zero_of_isOpen {H : Subgroup Gal(Ω/K)} (h : IsOpen (H : Set Gal(Ω/K)))
    (H' : Subgroup Gal(Ω/K)) : H.relIndex H' ≠ 0 := by
  have := finiteIndex_of_isOpen H h
  have : H.IsFiniteRelIndex ⊤ := Subgroup.isFiniteRelIndex_top_iff.mpr this
  exact mt (Subgroup.relIndex_eq_zero_of_le_right le_top) (Subgroup.relIndex_ne_zero (K := ⊤))

theorem upperField_le (u : ℝ) : upperField K Ω L u ≤ L := by
  conv_rhs => rw [← InfiniteGalois.fixedField_fixingSubgroup L]
  exact (IntermediateField.fixedField_antitone (fixingSubgroup_le_upperSupFixing u))

theorem upperField_mono : Monotone (upperField K Ω L) :=
  fun _ _ h ↦ IntermediateField.fixedField_antitone (upperSupFixing_antitone h)

theorem isClosed_upperSupFixing (hL : IsAPF K Ω L) (u : ℝ) :
    IsClosed (upperSupFixing K Ω L u : Set Gal(Ω/K)) :=
  Subgroup.isClosed_of_isOpen _ (hL u)

theorem fixingSubgroup_upperField (hL : IsAPF K Ω L) (u : ℝ) :
    (upperField K Ω L u).fixingSubgroup = upperSupFixing K Ω L u :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨upperSupFixing K Ω L u, isClosed_upperSupFixing hL u⟩

theorem finiteDimensional_upperField (hL : IsAPF K Ω L) (u : ℝ) :
    FiniteDimensional K (upperField K Ω L u) := by
  rw [← InfiniteGalois.isOpen_iff_finite]
  have := fixingSubgroup_upperField hL u
  exact this ▸ hL u

theorem apfIndex_mono (hL : IsAPF K Ω L) : Monotone (apfIndex K Ω L) := by
  intro u u' h
  exact Subgroup.relIndex_le_of_le_left (upperSupFixing_antitone h)
    (relIndex_ne_zero_of_isOpen (hL u') _)

theorem apfIndex_pos (hL : IsAPF K Ω L) (u : ℝ) : 0 < apfIndex K Ω L u := by
  exact Nat.pos_of_ne_zero (relIndex_ne_zero_of_isOpen (hL u) _)

theorem intervalIntegrable_apfIndex (hL : IsAPF K Ω L) (a b : ℝ) :
    IntervalIntegrable (fun w ↦ (apfIndex K Ω L w : ℝ)) MeasureTheory.volume a b :=
  (Monotone.intervalIntegrable (fun _ _ h ↦ by exact_mod_cast apfIndex_mono hL h))

end APF

end GroundTheory.PAdicHodge
