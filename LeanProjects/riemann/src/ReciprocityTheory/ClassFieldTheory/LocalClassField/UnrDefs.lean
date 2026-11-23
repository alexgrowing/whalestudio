import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

variable (p : ℕ) [Fact p.Prime]

noncomputable abbrev Obar : ValuationSubring (PadicAlgCl p) := (PadicAlgCl.valued p).v.valuationSubring

abbrev kbar : Type := IsLocalRing.ResidueField (Obar p)

variable {p} in
theorem mem_Obar_iff {x : PadicAlgCl p} : x ∈ Obar p ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe]
  rfl

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

noncomputable def resK : Subfield (kbar p) where
  toSubring := (K.toSubring.comap (Obar p).subtype).map (IsLocalRing.residue (Obar p))
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    by_cases h0 : IsLocalRing.residue (Obar p) a = 0
    · rw [h0, inv_zero]; exact Subring.zero_mem _
    · have h0 := (IsLocalRing.residue_ne_zero_iff_isUnit a).1 h0
      obtain ⟨u, rfl⟩ := h0
      refine ⟨((u⁻¹ : (Obar p)ˣ) : Obar p), ?_, ?_⟩
      · have h1 : (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) = ((u : Obar p) : PadicAlgCl p)⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          have h2 : ((((u⁻¹ : (Obar p)ˣ) : Obar p) * (u : Obar p) : Obar p) : PadicAlgCl p) = 1 := by
            rw [u.inv_mul]; rfl
          exact h2
        change (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) ∈ K
        rw [h1]
        exact K.inv_mem ha
      · apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, u.inv_mul, map_one]

noncomputable def qK : ℕ := Nat.card (resK p K)

noncomputable def Kn (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1}

def IsFrobOn (n : ℕ) (φ : GK p K) : Prop :=
  ∀ x ∈ Kn p K n, ‖x‖ ≤ 1 → ‖φ x - x ^ qK p K‖ < 1

end ReciprocityTheory.DiscreteGroups.LocalClassField
