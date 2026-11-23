import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements

set_option autoImplicit false

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.UpperArith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem tr_one_mem (M : TwoLevels E r U C) (c : C) : M.tr 1 c ∈ (M.comp c).Γ := by
  have h := M.tr_mul 1 1 c
  simp only [mul_one, one_smul, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] at h
  simpa using (M.comp c).Γ.inv_mem h

def upperSub (M : TwoLevels E r U C) (c : C) : Subgroup (GL (Fin r) E) where
  carrier := M.upper c
  one_mem' := ⟨1, one_smul U c, (M.tr 1 c)⁻¹, (M.comp c).Γ.inv_mem (tr_one_mem M c), by simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, γ, hγ, rfl⟩ ⟨v, hv, δ, hδ, rfl⟩
    have hc := (M.tr_conj u c δ).1 hδ
    rw [hu] at hc
    have hm := M.tr_mul u v c
    rw [hv, mul_smul, hv, hu] at hm
    refine ⟨u * v, by rw [mul_smul, hv, hu], γ * (M.tr u c * δ * (M.tr u c)⁻¹) *
      (M.tr (u * v) c * (M.tr u c * M.tr v c)⁻¹)⁻¹, ?_, ?_⟩
    · exact (M.comp c).Γ.mul_mem ((M.comp c).Γ.mul_mem hγ hc) ((M.comp c).Γ.inv_mem hm)
    · group
  inv_mem' := by
    rintro _ ⟨u, hu, γ, hγ, rfl⟩
    have hu' : u⁻¹ • c = c := by rw [inv_smul_eq_iff, hu]
    have hm := M.tr_mul u⁻¹ u c
    rw [hu, inv_mul_cancel, one_smul] at hm
    have h1 := tr_one_mem M c
    have hε : M.tr u⁻¹ c * M.tr u c ∈ (M.comp c).Γ := by
      have := (M.comp c).Γ.mul_mem ((M.comp c).Γ.inv_mem hm) h1
      simpa [mul_inv_rev, mul_assoc] using this
    have hc : (M.tr u c)⁻¹ * γ⁻¹ * M.tr u c ∈ (M.comp c).Γ := by
      rw [M.tr_conj u c, hu]
      simpa [mul_assoc] using (M.comp c).Γ.inv_mem hγ
    refine ⟨u⁻¹, hu', (M.tr u c)⁻¹ * γ⁻¹ * M.tr u c * (M.tr u⁻¹ c * M.tr u c)⁻¹,
      (M.comp c).Γ.mul_mem hc ((M.comp c).Γ.inv_mem hε), ?_⟩
    group

theorem prime_and_mem_of_primesOver {g : ℕ} {P : Ideal (𝓞 E)}
    (hP : P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E)) : P.IsPrime ∧ (g : 𝓞 E) ∈ P := by
  obtain ⟨hp, hl⟩ := hP
  refine ⟨hp, ?_⟩
  have hg : (g : ℤ) ∈ P.under ℤ := by
    rw [← hl.over]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_comap] at hg
  simpa using hg

theorem upper_subgroup (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (c : C) (g : ℕ) (hU : M.UnipotentOver g) :
    ∃ Γo : Subgroup (GL (Fin r) E), (∀ γ ∈ Γo, IsUStab (M.comp c).Gm (M.comp c).L' γ) ∧
      (∀ γ ∈ Γo, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g γ) ∧
      ∀ u : U, u • c = c → M.tr u c ∈ Γo := by
  refine ⟨upperSub M c, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, δ, hδ, rfl⟩
    have hs := (M.comp c).Γ_stab δ hδ
    refine ⟨fun v w => ?_, fun v => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs.1, M.comp_Gm, M.tr_herm]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, M.tr_L' u c v, hu]
      exact M.Γ_L' c δ hδ _
  · intro γ hγ P hP
    obtain ⟨hp, hg⟩ := prime_and_mem_of_primesOver hP
    exact ⟨r, fun v hv => hU c γ hγ P hp hg v hv⟩
  · intro u hu
    exact ⟨u, hu, 1, (M.comp c).Γ.one_mem, (one_mul _).symm⟩

end GlobalTheory.UpperArith
