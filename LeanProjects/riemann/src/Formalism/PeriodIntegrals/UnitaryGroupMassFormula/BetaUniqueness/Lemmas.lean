import Mathlib
import Formalism.PeriodIntegrals.BetaLUniq
import Lemmata.GeneralBFactThirdRest.Imports

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaLUniq

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem finrank_orth_add (U : Submodule E S.V) :
    finrank E (orth S U) + finrank E U = finrank E S.V := by
  set d := finrank E U
  let b := Module.finBasis E U
  let f : Fin d → Module.Dual E S.V := fun i => S.hT (b i : S.V)
  have hli : LinearIndependent E f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : S.hT (∑ j, star (g j) • (b j : S.V)) = 0 := by
      rw [map_sum]
      simp only [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star]
      exact hg
    have h1 : ∑ j, star (g j) • (b j : S.V) = 0 :=
      S.nondeg.1 _ (fun y => by rw [h0]; rfl)
    have hli' : LinearIndependent E (fun j => (b j : S.V)) :=
      b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    have := (Fintype.linearIndependent_iff.mp hli') (fun j => star (g j)) h1 i
    simpa using this
  let Φ : Submodule E (Module.Dual E S.V) := Submodule.span E (Set.range f)
  have hΦ : finrank E Φ = d := by
    rw [finrank_span_eq_card hli]; simp [d]
  have hco : Φ.dualCoannihilator = orth S U := by
    ext v
    rw [Submodule.mem_dualCoannihilator, mem_orth]
    constructor
    · intro h x hx
      have hx' := b.sum_repr ⟨x, hx⟩
      have : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : S.V) := by
        have h2 := congrArg Subtype.val hx'
        rw [Submodule.coe_sum] at h2
        simp only [Submodule.coe_smul] at h2
        exact h2.symm
      rw [this, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
      have := h (f i) (Submodule.subset_span ⟨i, rfl⟩)
      simp only [f] at this
      rw [this, smul_zero]
    · intro h φ hφ
      induction hφ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact h _ (b i).2
      | zero => rfl
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ
  rw [hco, hΦ] at this
  omega

theorem exists_smul_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (x : S.V) :
    ∃ a : 𝓞 E, a ≠ 0 ∧ a • x ∈ Λ := by
  first | exact Bl.general_b_fact_third''''.goal1 .. | (apply Bl.general_b_fact_third''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_third''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_third''''.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_third''''.goal1 E ‹_› ‹_› ‹_› S Λ hΛ x | exact @Bl.general_b_fact_third''''.goal1 E ‹_› ‹_› ‹_› S Λ hΛ | exact @Bl.general_b_fact_third''''.goal1 E ‹_› ‹_› ‹_› S Λ | exact @Bl.general_b_fact_third''''.goal1 E ‹_› ‹_› ‹_› S | exact @Bl.general_b_fact_third''''.goal1 E ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third''''.goal1 E ‹_› ‹_› | exact @Bl.general_b_fact_third''''.goal1 E ‹_› | exact @Bl.general_b_fact_third''''.goal1 E

theorem span_inf_toO (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (U : Submodule E S.V) :
    Submodule.span E ((Λ ⊓ toO S U : Submodule (𝓞 E) S.V) : Set S.V) = U := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro x hx
    obtain ⟨a, ha, hax⟩ := exists_smul_mem S Λ hΛ x
    have hmem : a • x ∈ (Λ ⊓ toO S U : Submodule (𝓞 E) S.V) :=
      ⟨hax, by simpa [toO] using U.smul_mem (a : E) hx⟩
    have hx' : x = ((a : E)⁻¹) • (a • x) := by
      rw [← algebraMap_smul E a x, smul_smul]
      have : (a : E) ≠ 0 := by simpa using ha
      simp [this]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem Xsp_le_UUE (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) {r : ℕ} {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') : Xsp F ≤ UUE Λ F F' := by
  rw [← span_inf_toO S Λ hΛ (Xsp F)]
  apply Submodule.span_mono
  intro x hx
  simp only [UU]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hx))

theorem Xsp_le_UUE' (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) {r : ℕ} {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') : Xsp F' ≤ UUE Λ F F' := by
  rw [← span_inf_toO S Λ hΛ (Xsp F')]
  apply Submodule.span_mono
  intro x hx
  simp only [UU]
  exact Submodule.mem_sup_left (Submodule.mem_sup_right hx)

end PI.UnitaryGroupMassFormula.BetaLUniq
