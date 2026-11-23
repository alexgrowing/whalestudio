import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AdjointMemCapSpSubA
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerStepLoweringUnitaryComplement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapZeroOfContraction
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

open Matrix in

theorem _root_.GlobalTheory.WigSh.exists_wigMap_chain_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : _root_.Formalism.FourierDecayAlt.Q.Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), _root_.Formalism.QuantumDeterminants.inWb (n + 1) r z → 0 < _root_.Formalism.QuantumDeterminants.Tz (n + 1) r z → _root_.Formalism.FourierDecayAlt.Q.IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → _root_.Formalism.FourierDecayAlt.Q.IsFrameOf (n + 1) r [z] B → (∀ j, j > l → L j < L l - (n₀ : ℤ)) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : _root_.Formalism.FourierDecayAlt.Q.Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), _root_.Formalism.FourierDecayAlt.Q.IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - (n₀ : ℝ))) ∧ _root_.GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ _root_.Formalism.FourierDecayAlt.Qr.CapSp (_root_.Formalism.FourierDecayAlt.Qr.subA (_root_.Formalism.FourierDecayAlt.Qr.EB π B)) (_root_.Formalism.FourierDecayAlt.Qr.shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, _root_.GlobalTheory.WigSh.wM (Function.update L l (L l - (j : ℤ))) M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l n₀
  induction n₀ with
  | zero =>
    intro hz hT hType hL hrel hB hgap
    refine ⟨V, inferInstance, inferInstance, inferInstance, π, fun _ => ContinuousLinearMap.id ℂ V,
      ?_, ?_, ?_⟩
    · simpa using hType
    · exact _root_.GlobalTheory.WigSh.wigMap_zero_of_contraction V V (n + 1) r z π π
        (ContinuousLinearMap.id ℂ V) (fun v => le_rfl) (fun h _ v => rfl)
    · intro M v _
      simp only [Finset.prod_range_zero, Complex.ofReal_one, one_smul,
        ContinuousLinearMap.id_apply]
      refine ext_inner_left ℂ fun w => ?_
      rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.id_apply]
  | succ m ih =>
    intro hz hT hType hL hrel hB hgap
    have hm : (0 : ℤ) ≤ m := Nat.cast_nonneg m
    have hgap' : ∀ j, j > l → L j < L l - (m : ℤ) := fun j hj => by
      have := hgap j hj
      push_cast at this
      linarith
    obtain ⟨V₁, i₁, i₂, i₃, π₁, A₁, hType₁, hA₁, hprod₁⟩ := ih hz hT hType hL hrel hB hgap'
    set L₁ := Function.update L l (L l - m) with hL₁def
    set u₁ := Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - m) with hu₁def
    have hL₁ : StrictAnti L₁ := by
      intro a b hab
      by_cases ha : a = l
      · subst ha
        have hb : b ≠ a := ne_of_gt hab
        rw [hL₁def, Function.update_self, Function.update_of_ne hb]
        have := hgap b hab
        push_cast at this
        linarith
      · by_cases hb : b = l
        · subst hb
          rw [hL₁def, Function.update_self, Function.update_of_ne ha]
          have := hL hab
          linarith
        · rw [hL₁def, Function.update_of_ne ha, Function.update_of_ne hb]
          exact hL hab
    have hne₁ : ∀ j : Fin (n + 1), L₁ j ≠ L₁ l - 1 := by
      intro j
      by_cases hj : j = l
      · subst hj
        omega
      · rw [hL₁def, Function.update_self, Function.update_of_ne hj]
        rcases lt_or_gt_of_ne hj with h | h
        · have := hL h
          omega
        · have := hgap j h
          push_cast at this
          omega
    have hrel₁ : ∀ j : Fin (n + 1),
        (u₁ ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L₁ j : ℂ) := by
      intro j
      by_cases hj : j = l
      · subst hj
        rw [hu₁def, hL₁def, Function.update_self, Function.update_self]
        have := hrel j
        push_cast at this ⊢
        linear_combination this
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [hu₁def, hL₁def, Function.update_of_ne hj, Function.update_of_ne hj']
        exact hrel j
    obtain ⟨V₂, j₁, j₂, j₃, π₂, A₂, hType₂, hA₂, hprod₂⟩ :=
      _root_.GlobalTheory.WignerStepLower.wigner_step_lowering V₁ n r z π₁ u₁ β L₁ B l hz hT hType₁ hL₁ hrel₁ hB hne₁
    refine ⟨V₂, j₁, j₂, j₃, π₂, fun ω => (A₁ ω).comp (A₂ ω), ?_,
      _root_.GlobalTheory.WigSh.wigMap_comp V V₁ V₂ (n + 1) r z π π₁ π₂ m 1 A₁ A₂ hA₁ hA₂, ?_⟩
    · have key : Function.update u₁ ((l : ℕ) + 1) (u₁ ((l : ℕ) + 1) - 1) =
          Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - ((m + 1 : ℕ) : ℝ)) := by
        rw [hu₁def, Function.update_idem, Function.update_self]
        congr 1
        push_cast
        ring
      rw [← key]
      exact hType₂
    · intro M v hv
      have hadj := _root_.GlobalTheory.adjoint_mem_CapSp_subA V V₁ n r z π π₁ B
        (A₁ (B (Fin.last n))) (_root_.Formalism.FourierDecayAlt.Qr.shf β M) ⟨hType.2.1, hType.2.2.1⟩ ⟨hType₁.2.1, hType₁.2.2.1⟩
        hType.2.2.2.1 hType₁.2.2.2.1 hB
        (fun h hh hfix => by
          have := hA₁.2.1 h hh (B (Fin.last n))
          rwa [hfix] at this) v hv
      simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
      rw [hprod₂ M _ hadj, map_smul, hprod₁ M v hv, Finset.prod_range_succ, Complex.ofReal_mul,
        mul_comm, mul_smul]

end GlobalTheory.WigSh
