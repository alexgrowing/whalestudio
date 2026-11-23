import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.IntOfSm
import GroundTheory.AutomorphicForms.GLnLocal

noncomputable section

open Matrix Topology

namespace PositivityTheory.RgUd.T.Nil.BasePf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem isOpen_ball' (γ : (ValueGroupWithZero k)ˣ) : IsOpen {x : k | valuation k x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨γ, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact lt_of_le_of_lt h (max_lt hy hx)

theorem isOpen_cball1 : IsOpen {x : k | valuation k x ≤ 1} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨1, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_one] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact le_trans h (max_le hy.le hx)

theorem isOpen_sm (γ : (ValueGroupWithZero k)ˣ) : IsOpen {A : Matrix (Fin n) (Fin n) k | sm γ A} := by
  have : {A : Matrix (Fin n) (Fin n) k | sm γ A} = ⋂ i, ⋂ j, (fun A : Matrix (Fin n) (Fin n) k => A i j) ⁻¹'
      ({x | valuation k x < γ} ∩ {x | valuation k x < ((1 : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)}) := by
    ext A
    simp [sm]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    ((isOpen_ball' γ).inter (isOpen_ball' 1)).preimage (continuous_id.matrix_elem i j)

theorem nhds_one_ball {U : Set (Matrix (Fin n) (Fin n) k)} (hU : U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k)) :
    ∃ γ : (ValueGroupWithZero k)ˣ, ∀ A : Matrix (Fin n) (Fin n) k,
      (∀ i j, valuation k ((A - 1) i j) < γ) → A ∈ U := by
  let B : (ValueGroupWithZero k)ˣ → Set (Matrix (Fin n) (Fin n) k) :=
    fun γ => {A | ∀ i j, valuation k ((A - 1) i j) < γ}
  have hdir : Directed (· ≥ ·) (fun γ => Filter.principal (B γ)) := by
    intro a b
    refine ⟨min a b, ?_, ?_⟩
    · simp only [ge_iff_le, Filter.principal_mono]
      intro A hA i j
      exact lt_of_lt_of_le (hA i j) (by exact_mod_cast min_le_left a b)
    · simp only [ge_iff_le, Filter.principal_mono]
      intro A hA i j
      exact lt_of_lt_of_le (hA i j) (by exact_mod_cast min_le_right a b)
  have ht : Filter.Tendsto (fun A : Matrix (Fin n) (Fin n) k => A)
      (⨅ γ, Filter.principal (B γ)) (𝓝 (1 : Matrix (Fin n) (Fin n) k)) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [(IsValuativeTopology.hasBasis_nhds ((1 : Matrix (Fin n) (Fin n) k) i j)).tendsto_right_iff]
    intro δ _
    rw [Filter.eventually_iff]
    refine Filter.mem_iInf_of_mem δ ?_
    rw [Filter.mem_principal]
    intro A hA
    simpa [Matrix.sub_apply] using hA i j
  obtain ⟨γ, hγ⟩ := (Filter.mem_iInf_of_directed hdir _).mp (ht hU)
  exact ⟨γ, fun A hA => Filter.mem_principal.mp hγ hA⟩

theorem cont_inv_one : ContinuousAt (fun A : Matrix (Fin n) (Fin n) k => A⁻¹) 1 := by
  apply continuousAt_matrix_inv
  rw [det_one, Ring.inverse_eq_inv']
  exact continuousAt_inv₀ one_ne_zero

theorem isClosed_Wt (e : Matrix (Fin n) (Fin n) k) : IsClosed {w : Fin n → k | e *ᵥ w = w} :=
  isClosed_eq (continuous_const.matrix_mulVec continuous_id) continuous_id

theorem isCompact_L (e : Matrix (Fin n) (Fin n) k) :
    IsCompact {w : Wt e | ∀ i, valuation k (w.1 i) ≤ 1} := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n => {x : k | valuation k x ≤ 1}) :=
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have heq : {w : Wt e | ∀ i, valuation k (w.1 i) ≤ 1} =
      (Subtype.val : Wt e → (Fin n → k)) ⁻¹' (Set.pi Set.univ fun _ : Fin n => {x : k | valuation k x ≤ 1}) := by
    ext w
    simp
  rw [heq]
  exact (isClosed_Wt e).isClosedEmbedding_subtypeVal.isCompact_preimage hK

theorem isOpen_L (e : Matrix (Fin n) (Fin n) k) :
    IsOpen {w : Wt e | ∀ i, valuation k (w.1 i) ≤ 1} := by
  have hO : IsOpen (Set.pi Set.univ fun _ : Fin n => {x : k | valuation k x ≤ 1}) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball1
  have := hO.preimage (continuous_subtype_val : Continuous (Subtype.val : Wt e → (Fin n → k)))
  convert this using 1
  ext w
  simp

end PositivityTheory.RgUd.T.Nil.BasePf
