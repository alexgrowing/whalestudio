import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRaisingWordMemSpanHigherWordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeightWordApplyWeightVectorStatement
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HdStep

theorem proj_comm {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} (hU : KUnit ε E) (L : Submodule ℂ V) [L.HasOrthogonalProjection]
    (hL : KStab ε E L) (a b : Fin n) (hab : ε a = ε b) (y : V) :
    L.starProjection (E a b y) = E a b (L.starProjection y) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hL a b hab _ (L.starProjection_apply_mem y)
  · intro z hz
    rw [← map_sub, hU a b hab]
    exact Submodule.starProjection_inner_eq_zero y _ (hL b a hab.symm z hz)

theorem main : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → KUnit ε E → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → ∀ Λ : Fin n → ℝ, (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = Λ) → ∀ (μ : Fin n → ℝ) (w : V), KHighest ε E μ w → ∀ (s t : Bool) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t) → ∀ x ∈ L, ⟪x, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 → ∃ l' : List (Fin n × Fin n), l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ μ + (l'.map fun p : Fin n × Fin n => root p.1 p.2).sum = Λ := by
  intro n ε V _ _ E hG hU L hfd hL Λ hΛ μ w hw s t l hl x hx hxl
  haveI : FiniteDimensional ℂ L := hfd
  let word : List (Fin n × Fin n) → V := fun l => (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w
  let ht : List (Fin n × Fin n) → ℤ := fun l => (l.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum
  let S : Set (List (Fin n × Fin n)) :=
    {l' | l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ L.starProjection (word l') ≠ 0}
  have hSfin : S.Finite := (List.finite_length_eq (Fin n × Fin n) l.length).subset (fun l' h => h.1)
  have hlS : l ∈ S := by
    refine ⟨rfl, hl, fun h0 => hxl ?_⟩
    have hPx : L.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    rw [← hPx, Submodule.inner_starProjection_left_eq_right]
    change ⟪x, L.starProjection (word l)⟫_ℂ = 0
    rw [h0, inner_zero_right]
  obtain ⟨l', hl'S, hmax⟩ := Set.exists_max_image S ht hSfin ⟨l, hlS⟩
  refine ⟨l', hl'S.1, hl'S.2.1, ?_⟩
  set u := L.starProjection (word l') with hu
  have huL : u ∈ L := L.starProjection_apply_mem _
  have hwt := GlobalTheory.T.isWeight_word_apply_weightVector n V E hG μ w hw.1 l'
  refine hΛ _ u huL hl'S.2.2 ⟨?_, ?_⟩
  · intro a
    rw [hu, ← proj_comm hU L hL a a rfl, hwt a, map_smul]
  · intro c d hcd hcd'
    rw [hu, ← proj_comm hU L hL c d hcd']
    have hspan := GlobalTheory.T.compactRaising_word_mem_span_higherWords n ε V E hG w c d hcd hcd' (hw.2 c d hcd hcd') s t l' hl'S.2.1
    have hle : Submodule.span ℂ {y : V | ∃ l'' : List (Fin n × Fin n), l''.length = l'.length ∧
        (∀ p ∈ l'', ε p.1 = s ∧ ε p.2 = t) ∧
        (l'.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum <
          (l''.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum ∧
        y = (l''.map fun p : Fin n × Fin n => E p.1 p.2).prod w} ≤
        LinearMap.ker (L.starProjection : V →ₗ[ℂ] V) := by
      rw [Submodule.span_le]
      rintro y ⟨l'', hlen, htyp, hlt, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      by_contra hne
      have hS'' : l'' ∈ S := ⟨hlen.trans hl'S.1, htyp, hne⟩
      exact absurd (hmax l'' hS'') (not_le.mpr hlt)
    exact LinearMap.mem_ker.mp (hle hspan)

end GlobalTheory.HdStep
