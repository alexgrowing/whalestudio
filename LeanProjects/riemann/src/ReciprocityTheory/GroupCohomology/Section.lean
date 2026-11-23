import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.SectionA

namespace ReciprocityTheory.Coh

open Function

universe u

theorem groupSection_holds : GroupSectionStatement.{u} := by
  intro G _ _ _ _ _ _ U hU
  obtain ⟨t, ht, htU, hc⟩ := ContinuousSections.core U hU
  let r0 : G → U := fun g => ⟨g * (t g)⁻¹, by simpa using U.inv_mem (htU g)⟩
  have hr0 : Continuous r0 := (continuous_id.mul ht.inv).subtype_mk _
  refine ⟨fun g => r0 g * (r0 1)⁻¹, hr0.mul continuous_const, mul_inv_cancel _, ?_⟩
  intro x g
  have h : t (x * g) = t g := hc _ _ (by rw [mul_inv_cancel_right]; exact x.2)
  apply Subtype.ext
  simp only [r0, Subgroup.coe_mul, Subgroup.coe_inv, h, mul_assoc]

theorem section_holds : SectionStatement.{u} := by
  intro B C _ _ _ _ _ _ p hp hsurj hcase
  rcases hcase with hd | ⟨hcB, hT2, hTD, hT2C⟩
  · exact ⟨surjInv hsurj, continuous_of_discreteTopology, surjInv_eq hsurj⟩
  · have : CompactSpace (Multiplicative B) := hcB
    have : T2Space (Multiplicative B) := hT2
    have : TotallyDisconnectedSpace (Multiplicative B) := hTD
    let U : Subgroup (Multiplicative B) :=
      { carrier := {x | p x.toAdd = 0}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, toAdd_mul, map_add] at ha hb ⊢; rw [ha, hb, add_zero]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_ofPred_eq, toAdd_inv, map_neg] at ha ⊢; rw [ha, neg_zero] }
    have hU : IsClosed (U : Set (Multiplicative B)) :=
      isClosed_singleton.preimage (hp.comp continuous_toAdd)
    obtain ⟨t, ht, htU, hc⟩ := ContinuousSections.core U hU
    let f : B → B := fun b => Multiplicative.toAdd (t (Multiplicative.ofAdd b))
    have hf : Continuous f := continuous_toAdd.comp (ht.comp continuous_ofAdd)
    have hpf : ∀ b, p (f b) = p b := by
      intro b
      have h := htU (Multiplicative.ofAdd b)
      change p (Multiplicative.toAdd (t (Multiplicative.ofAdd b) * (Multiplicative.ofAdd b)⁻¹)) = 0 at h
      rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, map_add, map_neg, add_neg_eq_zero] at h
      exact h
    have hfc : ∀ b b', p b = p b' → f b = f b' := by
      intro b b' hbb
      refine congrArg Multiplicative.toAdd (hc _ _ ?_)
      change p (Multiplicative.toAdd (Multiplicative.ofAdd b * (Multiplicative.ofAdd b')⁻¹)) = 0
      rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, map_add, map_neg, hbb, add_neg_cancel]
    refine ⟨fun c => f (surjInv hsurj c), continuous_iff_isClosed.2 fun F hF => ?_,
      fun c => by rw [hpf, surjInv_eq hsurj]⟩
    have e : (fun c => f (surjInv hsurj c)) ⁻¹' F = p '' (f ⁻¹' F) := by
      ext c
      constructor
      · intro hc'
        exact ⟨surjInv hsurj c, hc', surjInv_eq hsurj c⟩
      · rintro ⟨b, hb, rfl⟩
        show f (surjInv hsurj (p b)) ∈ F
        rw [hfc _ b (surjInv_eq hsurj _)]; exact hb
    rw [e]
    exact hp.isClosedMap _ (hF.preimage hf)

end ReciprocityTheory.Coh
