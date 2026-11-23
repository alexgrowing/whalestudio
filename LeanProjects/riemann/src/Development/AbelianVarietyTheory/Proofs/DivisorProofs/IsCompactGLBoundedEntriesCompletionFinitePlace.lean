import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace GlobalTheory.BoundedGL

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem isCompact_le (c : WithZero (Multiplicative ℤ)) :
    IsCompact {x : w.adicCompletion E | Valued.v x ≤ c} := by
  by_cases hc : c = 0
  · have e : {x : w.adicCompletion E | Valued.v x ≤ c} = {0} := by
      ext x
      simp [hc]
    rw [e]
    exact isCompact_singleton
  · obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
    set u : w.adicCompletion E := ((π ^ (-WithZero.log c) : E) : w.adicCompletion E) with hu
    have hvu : Valued.v u = c := by
      rw [hu, valuedAdicCompletion_eq_valuation', map_zpow₀, hπ, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log hc]
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, map_zero] at hvu
      exact hc hvu.symm
    have hO : IsCompact {x : w.adicCompletion E | Valued.v x ≤ 1} := by
      have := PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers w
      convert this using 1
      ext x
      simp [mem_adicCompletionIntegers]
    have e : {x : w.adicCompletion E | Valued.v x ≤ c} = (fun y => u * y) '' {x | Valued.v x ≤ 1} := by
      ext x
      constructor
      · intro hx
        refine ⟨u⁻¹ * x, ?_, by simp [hu0]⟩
        show Valued.v (u⁻¹ * x) ≤ 1
        rw [map_mul, map_inv₀, hvu]
        exact inv_mul_le_one_of_le₀ hx zero_le'
      · rintro ⟨y, hy, rfl⟩
        show Valued.v (u * y) ≤ c
        rw [map_mul, hvu]
        exact mul_le_of_le_one_right' hy
    rw [e]
    exact hO.image (continuous_mul_left u)

theorem isCompact_bounded : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
  intro E _ _ w n c
  set K := w.adicCompletion E
  set S : Set (Matrix (Fin n) (Fin n) K) := {A | ∀ i j, Valued.v (A i j) ≤ c} with hS
  have hK : IsCompact S := by
    have h : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => {x : K | Valued.v x ≤ c}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_le w c
    have e : S = (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => {x : K | Valued.v x ≤ c}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) K)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [hS, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
  exact ⟨fun hg => ⟨fun i j => (hg i j).1, fun i j => (hg i j).2⟩, fun hg i j => ⟨hg.1 i j, hg.2 i j⟩⟩

end GlobalTheory.BoundedGL
