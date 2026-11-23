import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionEqSumKFiniteModuleStatement
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem raisingSpan_eq_span_words : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ S : Submodule ℂ H, S ≤ D → raisingSpan ε σ S = (Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}).map D.subtype := by
  intro n ε H _ _ σ D E hK S hSD
  set Y : Set D := {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
    ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hY
  have hcmp := GlobalTheory.T.complexifiedDerivedAction_eq_sum_kFiniteModule n ε H σ D E hK

  have hstab : ∀ a b, ε a = true → ε b = false → ∀ y ∈ Submodule.span ℂ Y, E a b y ∈ Submodule.span ℂ Y := by
    intro a b ha hb y hy
    have hle : Submodule.span ℂ Y ≤ (Submodule.span ℂ Y).comap (E a b) := by
      rw [Submodule.span_le]
      rintro z ⟨l, hl, x, hx, rfl⟩
      apply Submodule.subset_span
      refine ⟨(a, b) :: l, ?_, x, hx, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨ha, hb⟩
        · exact hl p hp
      · simp [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact hle hy
  apply le_antisymm
  · rw [raisingSpan, Submodule.span_le]
    rintro w ⟨l, hl, v, hv, rfl⟩
    have key : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ l, Z ∈ pPlus ε) →
        ∃ y ∈ Submodule.span ℂ Y, (y : H) = l.foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) v := by
      intro l
      induction l with
      | nil =>
        intro _
        refine ⟨⟨v, hSD hv⟩, Submodule.subset_span ⟨[], by simp, ⟨v, hSD hv⟩, hv, by simp⟩, rfl⟩
      | cons Z l ih =>
        intro hl
        obtain ⟨y, hy, hyv⟩ := ih (fun Z' hZ' => hl Z' (List.mem_cons_of_mem _ hZ'))
        have hZ := hl Z List.mem_cons_self
        refine ⟨∑ a, ∑ b, Z a b • E a b y, ?_, ?_⟩
        · refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
          by_cases h : ε a = true ∧ ε b = false
          · exact Submodule.smul_mem _ _ (hstab a b h.1 h.2 y hy)
          · rw [hZ a b h, zero_smul]
            exact Submodule.zero_mem _
        · rw [List.foldr_cons, ← hyv, hcmp Z y]
    obtain ⟨y, hy, hyv⟩ := key l hl
    exact ⟨y, hy, hyv⟩
  · rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨y, ⟨l, hl, x, hx, rfl⟩, rfl⟩
    have key : ∀ l : List (Fin n × Fin n),
        (((l.map fun p : Fin n × Fin n => E p.1 p.2).prod x : D) : H) =
          (l.map fun p : Fin n × Fin n => Matrix.single p.1 p.2 (1 : ℂ)).foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) (x : H) := by
      intro l
      induction l with
      | nil => simp
      | cons p l ih =>
        rw [List.map_cons, List.map_cons, List.foldr_cons, ← ih, hcmp, List.prod_cons, Module.End.mul_apply]
        congr 1
        rw [Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]
        · simp
        · intro b _ hb; simp [Matrix.single_apply, Ne.symm hb]
        · simp
        · intro a _ ha
          refine Finset.sum_eq_zero fun b _ => ?_
          simp [Matrix.single_apply, Ne.symm ha]
        · simp
    refine Submodule.subset_span ⟨l.map fun p : Fin n × Fin n => Matrix.single p.1 p.2 (1 : ℂ), ?_, (x : H), hx, key l⟩
    intro Z hZ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hZ
    exact single_mem_pPlus (hl p hp).1 (hl p hp).2 1

end GlobalTheory.HolDS
