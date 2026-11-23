import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.Cell

theorem exists_block_equiv_of_cells {X α β : Type} {m : α → Type} (e : (Σ i, m i) ≃ X) (b : X → β)
    (c : α → β → ℕ) (E : ∀ i j, {x : X // (e.symm x).1 = i ∧ b x = j} ≃ Fin (c i j)) :
    ∃ f : ∀ i, (Σ j, Fin (c i j)) ≃ m i,
      ∀ i j t, e ⟨i, f i ⟨j, t⟩⟩ = ((E i j).symm t).1 := by
  have hι : ∀ i, Function.Bijective
      (fun y : m i => (⟨e ⟨i, y⟩, by simp⟩ : {x : X // (e.symm x).1 = i})) := by
    intro i
    constructor
    · intro a a' h
      have h1 : e ⟨i, a⟩ = e ⟨i, a'⟩ := congrArg Subtype.val h
      exact sigma_mk_injective (e.injective h1)
    · rintro ⟨x, hx⟩
      obtain ⟨⟨k, y⟩, rfl⟩ := e.surjective x
      simp only [Equiv.symm_apply_apply] at hx
      subst hx
      exact ⟨y, rfl⟩
  have hF : ∀ i, Function.Bijective
      (fun p : Σ j, Fin (c i j) =>
        (⟨((E i p.1).symm p.2).1, ((E i p.1).symm p.2).2.1⟩ : {x : X // (e.symm x).1 = i})) := by
    intro i
    constructor
    · rintro ⟨j, t⟩ ⟨j', t'⟩ h
      have h1 : ((E i j).symm t).1 = ((E i j').symm t').1 := congrArg Subtype.val h
      have hj : j = j' := by
        calc j = b ((E i j).symm t).1 := ((E i j).symm t).2.2.symm
          _ = b ((E i j').symm t').1 := by rw [h1]
          _ = j' := ((E i j').symm t').2.2
      subst hj
      have ht : t = t' := (E i j).symm.injective (Subtype.ext h1)
      subst ht
      rfl
    · rintro ⟨x, hx⟩
      refine ⟨⟨b x, E i (b x) ⟨x, hx, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      simp
  refine ⟨fun i => (Equiv.ofBijective _ (hF i)).trans (Equiv.ofBijective _ (hι i)).symm, ?_⟩
  intro i j t
  have key := (Equiv.ofBijective _ (hι i)).apply_symm_apply (Equiv.ofBijective _ (hF i) ⟨j, t⟩)
  exact congrArg Subtype.val key

theorem cell_row_column_partitions :
    ∀ {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} {m' : β' → Type} (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), ∃ (f : ∀ i, (Σ j, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m i) (g : ∀ j, (Σ i, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m' j), ∀ i j (t : Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩ := by
  intro α β' _ _ _ _ N m m' e e' w
  let E : ∀ i j, {x : Fin N // (e.symm x).1 = i ∧ blk e' (w.symm x) = j} ≃
      Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) :=
    fun i j => (Equiv.subtypeEquivRight (fun x => by
      rw [Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩)).trans
      (Finset.equivFin _)
  let E' : ∀ j i, {x : Fin N // ((e'.trans w).symm x).1 = j ∧ blk e x = i} ≃
      Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) :=
    fun j i => (Equiv.subtypeEquivRight (fun x => by
      rw [Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h.2, h.1⟩, fun h => ⟨h.2.2, h.2.1⟩⟩)).trans
      (Finset.equivFin _)
  obtain ⟨f, hf⟩ := exists_block_equiv_of_cells e (fun x => blk e' (w.symm x))
    (fun i j => (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) E
  obtain ⟨g, hg⟩ := exists_block_equiv_of_cells (e'.trans w) (fun x => blk e x)
    (fun j i => (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) E'
  refine ⟨f, g, ?_⟩
  intro i j t
  rw [hf i j t]
  exact hg j i t

end GlobalTheory.CompanionTheory.Cell
