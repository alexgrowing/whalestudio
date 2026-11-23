import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory

theorem exists_separating_extension_of_rel : ∀ {α β L : Type} [Infinite L] (S : Finset (α → L)) (r : β → α) (Rel : (α → L) → (β → L) → Prop), Function.Injective r → (∀ e ∈ S, ∀ e' ∈ S, ∀ f f', Rel e f → Rel e' f' → (e ∘ r = e' ∘ r ↔ f = f')) → ∃ tr : (α → L) → α → L, (∀ e ∈ S, ∀ f, Rel e f → ∀ k, f k = tr e (r k)) ∧ ∀ e ∈ S, ∀ e' ∈ S, (∃ k, e (r k) ≠ e' (r k)) → ∃ k, tr e (r k) ≠ tr e' (r k) := by
  intro α β L _ S r Rel hr H
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · exact ⟨id, fun _ _ _ _ k => isEmptyElim k, fun _ _ _ _ h => h⟩
  have hF : (⋃ e ∈ (S : Set (α → L)), {f | Rel e f}).Finite := by
    refine Set.Finite.biUnion S.finite_toSet fun e he => Set.Subsingleton.finite ?_
    intro f hf f' hf'
    exact (H e he e he f f' hf hf').1 rfl
  have hinf := hF.infinite_compl
  have hT : ((fun e : α → L => e ∘ r) '' (S : Set (α → L))).Countable :=
    (S.finite_toSet.image _).countable
  obtain ⟨n, hn⟩ := Set.countable_iff_exists_injOn.1 hT
  let j : (β → L) → (β → L) := fun c => (hinf.natEmbedding _ (n c)).1
  have hj : ∀ c, ∀ e ∈ S, ¬ Rel e (j c) := by
    intro c e he h
    exact (hinf.natEmbedding _ (n c)).2 (Set.mem_biUnion (Finset.mem_coe.2 he) h)
  have hji : ∀ e ∈ S, ∀ e' ∈ S, j (e ∘ r) = j (e' ∘ r) → e ∘ r = e' ∘ r := by
    intro e he e' he' h
    exact hn ⟨e, he, rfl⟩ ⟨e', he', rfl⟩ ((hinf.natEmbedding _).injective (Subtype.ext h))
  let g : (β → L) → (β → L) := fun c =>
    if h : ∃ f, ∃ e ∈ S, e ∘ r = c ∧ Rel e f then h.choose else j c
  have hg : ∀ c, (∃ e ∈ S, e ∘ r = c ∧ Rel e (g c)) ∨ g c = j c := by
    intro c
    by_cases h : ∃ f, ∃ e ∈ S, e ∘ r = c ∧ Rel e f
    · left
      have : g c = h.choose := dif_pos h
      rw [this]
      exact h.choose_spec
    · exact Or.inr (dif_neg h)
  refine ⟨fun e => Function.extend r (g (e ∘ r)) e, ?_, ?_⟩
  · intro e he f hf k
    have h : ∃ f, ∃ e' ∈ S, e' ∘ r = e ∘ r ∧ Rel e' f := ⟨f, e, he, rfl, hf⟩
    have h1 : g (e ∘ r) = h.choose := dif_pos h
    obtain ⟨e', he', h2, h3⟩ := h.choose_spec
    have h4 := (H e' he' e he _ _ h3 hf).1 h2
    show f k = Function.extend r (g (e ∘ r)) e (r k)
    rw [hr.extend_apply, h1, h4]
  · rintro e he e' he' ⟨k, hk⟩
    by_contra hc
    have hge : g (e ∘ r) = g (e' ∘ r) := by
      funext i
      by_contra hi
      refine hc ⟨i, ?_⟩
      show Function.extend r (g (e ∘ r)) e (r i) ≠ Function.extend r (g (e' ∘ r)) e' (r i)
      rwa [hr.extend_apply, hr.extend_apply]
    apply hk
    suffices h : e ∘ r = e' ∘ r from congrFun h k
    rcases hg (e ∘ r) with ⟨a, ha, h1, h2⟩ | h1 <;> rcases hg (e' ∘ r) with ⟨b, hb, h3, h4⟩ | h3
    · rw [← h1, ← h3]
      exact (H a ha b hb _ _ h2 h4).2 hge
    · exact absurd (by rw [← h3, ← hge]; exact h2) (hj (e' ∘ r) a ha)
    · exact absurd (by rw [← h1, hge]; exact h4) (hj (e ∘ r) b hb)
    · exact hji e he e' he' (by rw [← h1, ← h3, hge])

end GlobalTheory
