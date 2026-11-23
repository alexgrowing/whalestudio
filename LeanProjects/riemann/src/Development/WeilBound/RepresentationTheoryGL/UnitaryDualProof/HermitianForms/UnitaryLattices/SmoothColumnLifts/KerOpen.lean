import Mathlib

namespace PositivityTheory.RgUd.Form.U.Lift2.KerOpen

open Filter Topology

theorem isOpen_ker {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (φ : AddChar k Circle) (hφ : Continuous φ) :
    IsOpen {x : k | φ x = 1} := by

  let K : AddSubgroup k :=
    { carrier := {x | φ x = 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [AddChar.map_add_eq_mul, ha, hb, one_mul]
      zero_mem' := AddChar.map_zero_eq_one φ
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [AddChar.map_neg_eq_inv, ha, inv_one] }

  have h1 : (1 : Circle) ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  have hU : φ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : k) := by
    apply hφ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact (Circle.isOpen_centeredArc _).mem_nhds h1

  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hU
  let B : AddSubgroup k := (ValuativeRel.valuation k).ltAddSubgroup (Units.mk0 γ hγ)
  have hB : (B : Set k) = {x | ValuativeRel.valuation k x < γ} := rfl

  have hBK : (B : Set k) ⊆ K := by
    intro x hx
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    rw [← AddChar.map_nsmul_eq_pow]
    apply hsub
    rw [← hB]
    exact B.nsmul_mem hx n
  have hBn : (B : Set k) ∈ 𝓝 (0 : k) := by
    rw [hB]
    exact (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ
  exact AddSubgroup.isOpen_of_mem_nhds K (Filter.mem_of_superset hBn hBK)

end PositivityTheory.RgUd.Form.U.Lift2.KerOpen
