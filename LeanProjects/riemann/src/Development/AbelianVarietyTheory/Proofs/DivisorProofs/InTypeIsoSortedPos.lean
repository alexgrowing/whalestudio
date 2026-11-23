import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Formalism.LocalToGlobal.Columns.HeckeInertComm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

noncomputable section

namespace GlobalTheory.InertTypeIso

open Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : Ideal (𝓞 E))

def consEquiv (a : ℕ) (s : List ℕ) :
    inType P (a :: s) ≃ₗ[𝓞 E] (𝓞 E ⧸ P ^ a) × inType P s where
  toFun x := (x 0, fun i => x i.succ)
  invFun p := Fin.cons (α := fun i : Fin (s.length + 1) => 𝓞 E ⧸ P ^ (a :: s).get i) p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv p := by
    rcases p with ⟨u, v⟩
    rfl

def zeroEquiv (s : List ℕ) : inType P (0 :: s) ≃ₗ[𝓞 E] inType P s :=
  haveI : Subsingleton (𝓞 E ⧸ P ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr ((pow_zero P).trans Ideal.one_eq_top)
  (consEquiv P 0 s).trans
    { toFun := Prod.snd
      invFun := fun x => (0, x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ => rfl }

theorem iso_of_perm {s t : List ℕ} (h : s.Perm t) :
    Nonempty (inType P s ≃ₗ[𝓞 E] inType P t) := by
  induction h with
  | nil => exact ⟨LinearEquiv.refl _ _⟩
  | cons a _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨(consEquiv P a _).trans (((LinearEquiv.refl _ _).prodCongr e).trans (consEquiv P a _).symm)⟩
  | swap a b l =>
    exact ⟨(consEquiv P b _).trans <|
      ((LinearEquiv.refl _ _).prodCongr (consEquiv P a l)).trans <|
      (LinearEquiv.prodAssoc _ _ _ _).symm.trans <|
      ((LinearEquiv.prodComm _ _ _).prodCongr (LinearEquiv.refl _ _)).trans <|
      (LinearEquiv.prodAssoc _ _ _ _).trans <|
      ((LinearEquiv.refl _ _).prodCongr (consEquiv P b l).symm).trans (consEquiv P a _).symm⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨e1.trans e2⟩

theorem iso_filter_pos (s : List ℕ) :
    Nonempty (inType P s ≃ₗ[𝓞 E] inType P (s.filter (fun a => 0 < a))) := by
  induction s with
  | nil => exact ⟨LinearEquiv.refl _ _⟩
  | cons a s ih =>
    obtain ⟨e⟩ := ih
    cases a with
    | zero =>
      have hf : (0 :: s).filter (fun a => 0 < a) = s.filter (fun a => 0 < a) := by simp
      rw [hf]
      exact ⟨(zeroEquiv P s).trans e⟩
    | succ m =>
      have hf : ((m + 1) :: s).filter (fun a => 0 < a) = (m + 1) :: s.filter (fun a => 0 < a) := by
        simp
      rw [hf]
      exact ⟨(consEquiv P _ s).trans (((LinearEquiv.refl _ _).prodCongr e).trans (consEquiv P _ _).symm)⟩

theorem inType_iso_sorted_pos : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : Ideal (𝓞 E)) (s : List ℕ),
    ∃ y : List ℕ, y.Pairwise (· ≥ ·) ∧ (∀ a ∈ y, 0 < a) ∧ Nonempty (inType P s ≃ₗ[𝓞 E] inType P y) := by
  intro E _ _ _ P s
  refine ⟨(s.filter (fun a => 0 < a)).insertionSort (· ≥ ·), List.pairwise_insertionSort _ _, ?_, ?_⟩
  · intro a ha
    have := ((List.perm_insertionSort (· ≥ ·) _).mem_iff).mp ha
    simpa using (List.mem_filter.mp this).2
  · obtain ⟨e1⟩ := iso_filter_pos P s
    obtain ⟨e2⟩ := iso_of_perm P (List.perm_insertionSort (· ≥ ·) (s.filter (fun a => 0 < a))).symm
    exact ⟨e1.trans e2⟩

end GlobalTheory.InertTypeIso
