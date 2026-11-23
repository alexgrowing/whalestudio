import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.CentralMult

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem finite_range_inter (C : Set (GA E N)) (hC : IsCompact C) :
    (C ∩ ((ratGL E N).range : Set (GA E N))).Finite := by
  have hd : DiscreteTopology ((ratGL E N).range) := GlobalTheory.MirTower.discrete_of_le_range le_rfl
  have hcl : IsClosed (((ratGL E N).range : Subgroup (GA E N)) : Set (GA E N)) :=
    Subgroup.isClosed_of_discrete
  have hK : IsCompact (C ∩ ((ratGL E N).range : Set (GA E N))) := hC.inter_right hcl
  have hds : DiscreteTopology ↥(C ∩ ((ratGL E N).range : Set (GA E N))) :=
    DiscreteTopology.of_subset hd Set.inter_subset_right
  exact hK.finite ⟨hds⟩

theorem mul_inv_eq_of_central {G : Type} [Group G] {z x a b q r : G} (hz : ∀ g, z * g = g * z)
    (ha : a * x = z * q) (hb : b * x = z * r) : a * b⁻¹ = q * r⁻¹ := by
  have h1 : a = z * q * x⁻¹ := eq_mul_inv_of_mul_eq ha
  have h2 : b = z * r * x⁻¹ := eq_mul_inv_of_mul_eq hb
  have h3 : z * q * x⁻¹ * (z * r * x⁻¹)⁻¹ = z * (q * r⁻¹) * z⁻¹ := by group
  rw [h1, h2, h3, hz, mul_inv_cancel_right]

theorem multC : PositivityTheory.Rg.BcB.E.E3.MultC := by
  intro E _ _ _ N Q hQ
  have hC : IsCompact (Q * Q⁻¹) := hQ.mul hQ.inv
  have hF := finite_range_inter (Q * Q⁻¹) hC
  refine ⟨hF.toFinset.card, fun z hz x => ?_⟩
  rw [← hF.encard_eq_coe_toFinset_card]
  rcases Set.eq_empty_or_nonempty
    {γ : (ratGL E N).range | (γ : GA E N) * x ∈ (fun q => z * q) '' Q} with h0 | ⟨γ₀, q₀, hq₀, e₀⟩
  · rw [h0]
    simp
  · refine Set.encard_le_encard_of_injOn (f := fun γ : (ratGL E N).range => (γ : GA E N) * (γ₀ : GA E N)⁻¹) ?_ ?_
    · rintro γ ⟨q, hq, e⟩
      refine ⟨?_, mul_mem γ.2 (inv_mem γ₀.2)⟩
      have e' : (γ : GA E N) * (γ₀ : GA E N)⁻¹ = q * q₀⁻¹ := mul_inv_eq_of_central hz e.symm e₀.symm
      change (γ : GA E N) * (γ₀ : GA E N)⁻¹ ∈ Q * Q⁻¹
      rw [e']
      exact Set.mul_mem_mul hq (Set.inv_mem_inv.2 hq₀)
    · intro γ _ γ' _ h
      exact Subtype.ext (mul_right_cancel h)

end GlobalTheory.CompanionTheory.CentralMult

end
