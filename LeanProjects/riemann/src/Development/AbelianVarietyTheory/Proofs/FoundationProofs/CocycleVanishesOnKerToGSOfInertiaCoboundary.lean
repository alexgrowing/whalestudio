import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem cocycle_zero_on_ker_toGS : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (Y : G ℚ Ω → Fin 2 → Qbar l), Nf e S A W → Y ∈ Z1 (Loc.colRep W) → (∀ q : Pl, q ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, Y s = mat W s *ᵥ x - x) → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Y a = 0 := by
  intro l _ Ω _ _ _ e S A W Y hN hY hc a ha
  have hcoc : ∀ g h, Y (g * h) = Y g + mat W g *ᵥ Y h := fun g h => ((mem_Z1_iff_cocycle _ _).1 hY).2 g h
  have hcont : Continuous Y := ((mem_Z1_iff_cocycle _ _).1 hY).1
  have h1 : Y 1 = 0 := by
    have := hcoc 1 1
    simpa [mat] using this
  let H : Subgroup (G ℚ Ω) :=
    { carrier := {g | Y g = 0 ∧ W g = 1}
      one_mem' := ⟨h1, map_one W⟩
      mul_mem' := fun {g h} hg hh => ⟨by rw [hcoc, hg.1, hh.1]; simp, by rw [map_mul, hg.2, hh.2, one_mul]⟩
      inv_mem' := fun {g} hg => by
        refine ⟨?_, by rw [map_inv, hg.2, inv_one]⟩
        have := hcoc g g⁻¹
        rw [mul_inv_cancel, h1, hg.1] at this
        simpa [mat, hg.2] using this.symm }
  have hH : ∀ g, g ∈ H ↔ Y g = 0 ∧ W g = 1 := fun g => Iff.rfl
  haveI : H.Normal := ⟨fun g hg h => by
    rw [hH] at hg ⊢
    refine ⟨?_, by rw [map_mul, map_mul, hg.2, mul_one, ← map_mul, mul_inv_cancel, map_one]⟩
    have e1 : Y (g * h⁻¹) = Y h⁻¹ := by
      rw [hcoc, hg.1]; simp [mat, hg.2]
    rw [mul_assoc, hcoc, e1, ← hcoc, mul_inv_cancel, h1]⟩
  have hcl : IsClosed (H : Set (G ℚ Ω)) :=
    (isClosed_singleton.preimage hcont).inter (isClosed_singleton.preimage hN.cont)
  have hle : Subgroup.normalClosure
      (⋃ v ∈ (S : Set Pl)ᶜ, ⋃ B ∈ {B : ValuationSubring Ω | IsPlaceOver B v}, Inertia (F := ℚ) B) ≤ H := by
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    have hv' : v ∉ S := by simpa using hv
    have hτ' : τ ∈ Ine (F := ℚ) B := hτ
    have hW : W τ = 1 := hN.unr v hv' B hB hτ'
    obtain ⟨x, hx⟩ := hc v hv' B hB
    refine (hH τ).2 ⟨?_, hW⟩
    rw [hx τ hτ']
    simp [mat, hW]
  have ha' : a ∈ NS Ω (S : Set Pl) := by
    rwa [toGS, QuotientGroup.ker_mk'] at ha
  exact ((hH a).1 (Subgroup.topologicalClosure_minimal _ hle hcl ha')).1

end GlobalTheory.Ord2.GwCount
