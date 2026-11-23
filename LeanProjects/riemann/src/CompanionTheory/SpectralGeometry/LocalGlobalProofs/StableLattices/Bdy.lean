import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

abbrev lt {n : ℕ} (p q : Fin n) : FreeAlgebra ℂ (Fin n × Fin n) := FreeAlgebra.ι ℂ (p, q)

def fa (n : ℕ) (Y : ℂ) : FreeAlgebra ℂ (Fin n × Fin n) :=
  qdet (fun p q : Fin n => lt p q) (Y + ((n : ℂ) - 1) / 2)

def shift {M : ℕ} (d : Fin M → ℕ) (i : Fin M) : ℂ :=
  ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2

def fb {M n : ℕ} (d : Fin M → ℕ) (h : ∑ i, d i = n) (Y : ℂ) : FreeAlgebra ℂ (Fin n × Fin n) :=
  (List.ofFn fun i : Fin M => qdet (fun p q : Fin (d i) => lt (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩))
    (Y + shift d i)).prod

theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (ψ : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : ψ (qdet X u) = qdet (fun p q => ψ (X p q)) u := by
  unfold qdet qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_list_prod, List.map_ofFn]
  congr 1
  · simp
  · congr 2
    funext k
    simp [Function.comp, Tm]
    split_ifs <;> simp

abbrev lL {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (l : Fin n × Fin n) : Module.End ℂ (Cn n V) := if lev l.1 = lev l.2 then lF E l.1 l.2 else 0

section Spaces
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def cyc (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Submodule ℂ (Cn n V) where
  carrier := {x | SuppIn (inU lev) x ∧ Deg j x ∧ bd (allT n) E x = 0}
  add_mem' := by
    rintro x y ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
    refine ⟨fun A hA i hi => ?_, fun A hA => ?_, by rw [map_add, h3, g3, add_zero]⟩
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g1 A hy i hi
      · exact h1 A hx i hi
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g2 A hy
      · exact h2 A hx
  zero_mem' := ⟨fun A hA => absurd rfl hA, fun A hA => absurd rfl hA, map_zero _⟩
  smul_mem' := by
    rintro c x ⟨h1, h2, h3⟩
    have hne : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A hA hx => hA (by simp [hx])
    exact ⟨fun A hA => h1 A (hne A hA), fun A hA => h2 A (hne A hA), by rw [map_smul, h3, smul_zero]⟩

def bdy (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Submodule ℂ (Cn n V) where
  carrier := {x | ∃ w : Cn n V, SuppIn (inU lev) w ∧ Deg (j + 1) w ∧ bd (allT n) E w = x}
  add_mem' := by
    rintro _ _ ⟨x, h1, h2, rfl⟩ ⟨y, g1, g2, rfl⟩
    refine ⟨x + y, fun A hA i hi => ?_, fun A hA => ?_, map_add _ _ _⟩
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g1 A hy i hi
      · exact h1 A hx i hi
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g2 A hy
      · exact h2 A hx
  zero_mem' := ⟨0, fun A hA => absurd rfl hA, fun A hA => absurd rfl hA, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨x, h1, h2, rfl⟩
    have hne : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A hA hx => hA (by simp [hx])
    exact ⟨c • x, fun A hA => h1 A (hne A hA), fun A hA => h2 A (hne A hA), map_smul _ _ _⟩

end Spaces

def sz {n : ℕ} (lev : Fin n → ℕ) (M : ℕ) : Fin M → ℕ := fun i => (univ.filter fun a => lev a = (i : ℕ)).card

end GlobalTheory.CompanionTheory.RgCOBlock
