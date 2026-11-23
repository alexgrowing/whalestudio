import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.IntCocycle

theorem stdLat_free (g : ℕ) : Module.Free ℤ (stdLat g) := by
  have hli : LinearIndependent ℤ (Pi.basisFun ℝ (Fin g ⊕ Fin g)) :=
    (Pi.basisFun ℝ (Fin g ⊕ Fin g)).linearIndependent.restrict_scalars' ℤ
  exact Module.Free.of_basis (Module.Basis.span hli)

variable {M : Type} [AddCommGroup M]

@[ext] structure Ext (c : M → M → ℤ) where

  fst : ℤ

  snd : M

variable {c : M → M → ℤ}

instance : Add (Ext c) := ⟨fun x y => ⟨x.fst + y.fst + c x.snd y.snd, x.snd + y.snd⟩⟩
instance : Zero (Ext c) := ⟨⟨-c 0 0, 0⟩⟩
instance : Neg (Ext c) := ⟨fun x => ⟨-c 0 0 - x.fst - c (-x.snd) x.snd, -x.snd⟩⟩

@[simp] lemma add_fst (x y : Ext c) : (x + y).fst = x.fst + y.fst + c x.snd y.snd := rfl
@[simp] lemma add_snd (x y : Ext c) : (x + y).snd = x.snd + y.snd := rfl
@[simp] lemma zero_fst : (0 : Ext c).fst = -c 0 0 := rfl
@[simp] lemma zero_snd : (0 : Ext c).snd = 0 := rfl
@[simp] lemma neg_fst (x : Ext c) : (-x).fst = -c 0 0 - x.fst - c (-x.snd) x.snd := rfl
@[simp] lemma neg_snd (x : Ext c) : (-x).snd = -x.snd := rfl

def Ext.addCommGroup (hs : ∀ l l' : M, c l l' = c l' l)
    (hc : ∀ l l' l'' : M, c l l' + c (l + l') l'' = c l (l' + l'') + c l' l'') :
    AddCommGroup (Ext c) :=
  have h0 : ∀ m : M, c 0 m = c 0 0 := by
    intro m
    have := hc 0 0 m
    simp only [zero_add] at this
    linarith
  { AddGroup.ofLeftAxioms
      (fun x y z => by
        ext
        · simp only [add_fst, add_snd]
          have := hc x.snd y.snd z.snd
          linarith
        · simp [add_assoc])
      (fun x => by
        ext
        · simp [h0]
        · simp)
      (fun x => by
        ext
        · simp only [add_fst, neg_fst, neg_snd, zero_fst]
          ring
        · simp) with
    add_comm := fun x y => by
      ext
      · simp only [add_fst]
        rw [hs]
        ring
      · simp [add_comm] }

end GlobalTheory.IntCocycle

open GlobalTheory.IntCocycle in

theorem GlobalTheory.symm_int_cocycle_stdLat_coboundary :
    ∀ {g : ℕ} (c : Fl g → Fl g → ℤ), (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, c l l' = c l' l) →
      (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ l'' ∈ stdLat g,
        c l l' + c (l + l') l'' = c l (l' + l'') + c l' l'') →
      ∃ a : Fl g → ℤ, ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, c l l' = a (l + l') - a l - a l' := by
  intro g c hs hc
  classical
  let L := stdLat g
  let c' : L → L → ℤ := fun x y => c x y
  letI : AddCommGroup (Ext c') :=
    Ext.addCommGroup (fun x y => hs x x.2 y y.2)
      (fun x y z => by simpa [c'] using hc x x.2 y y.2 z z.2)
  haveI : Module.Free ℤ L := stdLat_free g
  let pr : Ext c' →+ L :=
    { toFun := Ext.snd
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hpr : Function.Surjective pr := fun l => ⟨⟨0, l⟩, rfl⟩
  obtain ⟨s, hs'⟩ := Module.projective_lifting_property pr.toIntLinearMap LinearMap.id hpr
  have hsnd : ∀ l : L, (s l).snd = l := fun l => LinearMap.congr_fun hs' l
  refine ⟨fun x => if h : x ∈ L then (s ⟨x, h⟩).fst else 0, ?_⟩
  intro l hl l' hl'
  have hll : l + l' ∈ L := L.add_mem hl hl'
  show c l l' = (if h : l + l' ∈ L then (s ⟨l + l', h⟩).fst else 0) - (if h : l ∈ L then (s ⟨l, h⟩).fst else 0) - (if h : l' ∈ L then (s ⟨l', h⟩).fst else 0)
  rw [dif_pos hll, dif_pos hl, dif_pos hl']
  have hadd := congrArg Ext.fst (s.map_add ⟨l, hl⟩ ⟨l', hl'⟩)
  have e : (⟨l, hl⟩ + ⟨l', hl'⟩ : L) = ⟨l + l', hll⟩ := rfl
  rw [e] at hadd
  rw [hadd]
  show c l l' = (s ⟨l, hl⟩).fst + (s ⟨l', hl'⟩).fst + c (s ⟨l, hl⟩).snd.1 (s ⟨l', hl'⟩).snd.1
    - (s ⟨l, hl⟩).fst - (s ⟨l', hl'⟩).fst
  rw [hsnd, hsnd]
  ring
