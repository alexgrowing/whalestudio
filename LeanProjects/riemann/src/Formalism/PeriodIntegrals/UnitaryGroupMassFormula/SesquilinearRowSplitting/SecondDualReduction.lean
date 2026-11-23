import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStepOf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem mem_dual_iff' (Λ : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ ↔ ∀ y ∈ Λ, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_one]

theorem pair_int {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x y : S.V}
    (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x := by
  have hx' : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    rw [show Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ from hU]
    exact hx
  exact (mem_dual_iff' S Λ x).mp hx' y hy

end Gen

theorem first_dual_reduction : DualEStep := by
  intro E _ _ _ S r T aa F0 Λ hC b x hx
  obtain ⟨_, hU, _, _, hX, hne, hst, _⟩ := hC
  rw [FractionalIdeal.mem_inv_iff (hne b)]
  intro t ht
  have h1 : star t • F0.e b ∈ Formalism.L2.SG.Saturated.latSpan aa F0.e :=
    Submodule.subset_span ⟨b, star t, hst b t ht, rfl⟩
  have h2 : star t • F0.e b ∈ XLam Λ (⟨F0, F0.z⟩ : LFlag S r T) := hX ▸ h1
  have hmem : star t • F0.e b ∈ Λ := (Submodule.mem_inf.1 h2).1
  obtain ⟨o, ho⟩ := pair_int S hU hx hmem
  rw [FractionalIdeal.mem_one_iff]
  refine ⟨o, ?_⟩
  rw [ho, LinearMap.map_smulₛₗ₂, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]

theorem second_dual_reduction : DualFStep := by
  intro E _ _ _ S r T aa F0 Λ hC f hF b y hy
  obtain ⟨_, hU, _, _, _, hne, hst, _⟩ := hC
  have hU' := hU
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hU'
  rw [← hU', mem_dual_iff']
  intro l hl
  have h1 : S.hT (f b) l ∈ aa b := hF.2.2 b l hl
  have h2 := (FractionalIdeal.mem_inv_iff (hne b)).1 hy _ (hst b _ h1)
  rw [FractionalIdeal.mem_one_iff] at h2
  obtain ⟨o, ho⟩ := h2
  refine ⟨o, ?_⟩
  rw [ho, map_smul, smul_eq_mul, ← LinearMap.isSymm_def.1 S.herm (f b) l, starRingEnd_apply]

theorem assembly_reduction : AsmStep := by
  intro E _ _ _ S r T aa F0 Λ hC f hF hiso
  have hE := first_dual_reduction E S r T aa F0 Λ hC
  have hFd := second_dual_reduction E S r T aa F0 Λ hC f hF
  obtain ⟨_, _, hz, _, hX, _, _, _⟩ := hC
  have herm : ∀ x y, star (S.hT x y) = S.hT y x := fun x y => by
    rw [← starRingEnd_apply]
    exact LinearMap.isSymm_def.1 S.herm x y
  have hfe : ∀ c a, S.hT (f c) (F0.e a) = if a = c then 1 else 0 := fun c a => by
    rw [← herm, hF.1 a c]
    by_cases h : a = c <;> simp [h]
  have hXle : Formalism.L2.SG.Saturated.latSpan aa F0.e ≤ Λ := by
    intro x hx
    have h2 : x ∈ XLam Λ (⟨F0, F0.z⟩ : LFlag S r T) := hX ▸ hx
    exact (Submodule.mem_inf.1 h2).1
  have hYle : Formalism.L2.SG.Saturated.latSpan (fun a => (aa a)⁻¹) f ≤ Λ := by
    rw [Formalism.L2.SG.Saturated.latSpan, Submodule.span_le]
    rintro _ ⟨a, y, hy, rfl⟩
    exact hFd a y hy
  let L : Submodule (𝓞 E) S.V :=
    Λ ⊓ ⨅ a, (LinearMap.ker ((S.hT (F0.e a)).restrictScalars (𝓞 E)) ⊓
      LinearMap.ker ((S.hT (f a)).restrictScalars (𝓞 E)))
  have hmemL : ∀ x, x ∈ L ↔ x ∈ Λ ∧ ∀ a, S.hT (F0.e a) x = 0 ∧ S.hT (f a) x = 0 := fun x => by
    simp [L, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  refine ⟨f, L, hiso, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [hF.1 a b]
  · intro x hx a
    exact ((hmemL x).1 hx).2 a
  · exact (hmemL _).2 ⟨hz, fun a => ⟨F0.z_orth a, hF.2.1 a⟩⟩
  · apply le_antisymm
    · intro l hl
      have hPmem : (∑ a, S.hT (f a) l • F0.e a) ∈ Formalism.L2.SG.Saturated.latSpan aa F0.e :=
        Submodule.sum_mem _ (fun a _ => Submodule.subset_span ⟨a, _, hF.2.2 a l hl, rfl⟩)
      have hQmem : (∑ b, S.hT (F0.e b) l • f b) ∈ Formalism.L2.SG.Saturated.latSpan (fun a => (aa a)⁻¹) f :=
        Submodule.sum_mem _ (fun b _ => Submodule.subset_span ⟨b, _, hE b l hl, rfl⟩)
      have hμ : l - (∑ a, S.hT (f a) l • F0.e a) - (∑ b, S.hT (F0.e b) l • f b) ∈ L := by
        rw [hmemL]
        refine ⟨Λ.sub_mem (Λ.sub_mem hl (hXle hPmem)) (hYle hQmem), fun c => ⟨?_, ?_⟩⟩
        · simp [map_sum, F0.e_iso, hF.1, Finset.sum_ite_eq]
        · simp [map_sum, hfe, hiso, Finset.sum_ite_eq']
      have hsplit : l = (∑ a, S.hT (f a) l • F0.e a) +
          (l - (∑ a, S.hT (f a) l • F0.e a) - (∑ b, S.hT (F0.e b) l • f b)) +
          (∑ b, S.hT (F0.e b) l • f b) := by abel
      rw [hsplit]
      exact Submodule.add_mem_sup (Submodule.add_mem_sup hPmem hμ) hQmem
    · exact sup_le (sup_le hXle (fun x hx => ((hmemL x).1 hx).1)) hYle

end PI.SRW
