import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal Pointwise

variable (G : Type*) [Group G]

theorem UnfoldOrbit.bijective_mul_out_inv {Γ Γ₀ : Subgroup G} (hle : Γ₀ ≤ Γ) :
    Function.Bijective (fun p : (Γ ⧸ Γ₀.subgroupOf Γ) × Γ₀ =>
      (⟨(p.2 : G) * ((Quotient.out p.1 : Γ) : G)⁻¹,
        Γ.mul_mem (hle p.2.2) (Γ.inv_mem (Quotient.out p.1).2)⟩ : Γ)) := by
  constructor
  · rintro ⟨q, h⟩ ⟨q', h'⟩ heq
    simp only [Subtype.mk.injEq] at heq
    have hmem : (Quotient.out q' : Γ)⁻¹ * Quotient.out q ∈ Γ₀.subgroupOf Γ := by
      rw [Subgroup.mem_subgroupOf]
      have key : (((Quotient.out q' : Γ)⁻¹ * Quotient.out q : Γ) : G) = (h' : G)⁻¹ * h := by
        rw [show (h' : G)⁻¹ * h = (h' : G)⁻¹ * ((h : G) * ((Quotient.out q : Γ) : G)⁻¹) *
          ((Quotient.out q : Γ) : G) by group, heq]
        push_cast
        group
      rw [key]
      exact Γ₀.mul_mem (Γ₀.inv_mem h'.2) h.2
    have hq : q' = q := by
      rw [← QuotientGroup.out_eq' q', ← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 hmem
    subst hq
    have hh : h = h' := Subtype.ext (mul_right_cancel heq)
    rw [hh]
  · intro γ
    have hmem := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk γ⁻¹ :
      Γ ⧸ Γ₀.subgroupOf Γ)).symm
    rw [Subgroup.mem_subgroupOf] at hmem
    refine ⟨⟨QuotientGroup.mk γ⁻¹, ⟨_, hmem⟩⟩, ?_⟩
    apply Subtype.ext
    simp

theorem UnfoldOrbit.proof [MeasurableSpace G] [MeasurableMul G] : UnfoldOrbit.Statement G := by
  intro μ _ Γ Γ₀ _ hle FD FD₀ hFD hFD₀ φ hφ hinv
  have : Countable Γ₀ := (Subgroup.inclusion_injective hle).countable
  have : Countable (Γ ⧸ Γ₀.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  rw [lintegral_tsum (f := fun (q : Γ ⧸ Γ₀.subgroupOf Γ) g => φ (((Quotient.out q : Γ) : G)⁻¹ * g))
      fun q => (hφ.comp (measurable_const_mul _)).aemeasurable,
    hFD.setLIntegral_eq_tsum φ FD₀,
    ← (Equiv.ofBijective _ (UnfoldOrbit.bijective_mul_out_inv G hle)).tsum_eq,
    ENNReal.tsum_prod']
  refine tsum_congr fun q => ?_
  have h1 : ∫⁻ g in FD, φ (((Quotient.out q : Γ) : G)⁻¹ * g) ∂μ =
      ∫⁻ x in ((Quotient.out q : Γ) : G)⁻¹ • FD, φ x ∂μ := by
    rw [← Set.image_smul]
    exact (measurePreserving_mul_left μ _).setLIntegral_comp_emb (measurableEmbedding_mulLeft _) φ FD
  rw [h1, hFD₀.setLIntegral_eq_tsum' φ]
  refine tsum_congr fun h => ?_
  have hset : h • ((Quotient.out q : Γ) : G)⁻¹ • FD ∩ FD₀ =
      FD₀ ∩ (Equiv.ofBijective _ (UnfoldOrbit.bijective_mul_out_inv G hle) (q, h)) • FD := by
    rw [Set.inter_comm]
    congr 1
    show (h : G) • ((Quotient.out q : Γ) : G)⁻¹ • FD = ((h : G) * ((Quotient.out q : Γ) : G)⁻¹) • FD
    rw [smul_smul]
  rw [hset]
  exact lintegral_congr fun x => hinv _ (h⁻¹).2 x

end GroundTheory.Heights₂.Heights.FiniteCovolume
