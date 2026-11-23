import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.TheRec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CBGal

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def SlightlyReg (π : CuspSub E a) : Prop :=
  ∃ (τ : E →+* ℂ) (z : Fin a → ℂ), (CG.mk π).infChar τ = Finset.univ.val.map z ∧ StrictAnti (fun i => (z i).re) ∧
    ∃ i j : Fin a, Even (i : ℕ) ∧ (j : ℕ) = i + 1 ∧ (z j).re + 1 < (z i).re

def OddOrSlightlyReg (π : CuspSub E a) : Prop := Odd a ∨ SlightlyReg π

theorem OddOrSlightlyReg.of_odd (π : CuspSub E a) (h : Odd a) : OddOrSlightlyReg π := Or.inl h

theorem OddOrSlightlyReg.of_slightlyReg {π : CuspSub E a} (h : SlightlyReg π) : OddOrSlightlyReg π := Or.inr h

theorem oddOrSlightlyReg_iff_of_even (π : CuspSub E a) (h : Even a) : OddOrSlightlyReg π ↔ SlightlyReg π :=
  ⟨fun h' => h'.resolve_left (Nat.not_odd_iff_even.2 h), Or.inr⟩

def SlightlyRegAll (π : CuspSub E a) : Prop :=
  ∃ (τ : E →+* ℂ) (z : Fin a → ℂ), (CG.mk π).infChar τ = Finset.univ.val.map z ∧ StrictAnti (fun i => (z i).re) ∧
    ∀ i j : Fin a, Even (i : ℕ) → (j : ℕ) = i + 1 → (z j).re + 1 < (z i).re

theorem SlightlyRegAll.slightlyReg {π : CuspSub E a} (ha : 2 ≤ a) (h : SlightlyRegAll π) : SlightlyReg π := by
  obtain ⟨τ, z, hz, hs, hg⟩ := h
  exact ⟨τ, z, hz, hs, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, rfl⟩, rfl, hg _ _ ⟨0, rfl⟩ rfl⟩

theorem slightlyReg_of_weight (π : CuspSub E a) (τ : E →+* ℂ) (w : Fin a → ℤ) (hw : Antitone w)
    (h : (CG.mk π).infChar τ = Finset.univ.val.map fun k : Fin a => (w k : ℂ) + (((a : ℂ) - 1) / 2 - (k : ℕ)))
    (k l : Fin a) (hk : Even (k : ℕ)) (hl : (l : ℕ) = k + 1) (hg : w l < w k) : SlightlyReg π := by
  refine ⟨τ, _, h, ?_, k, l, hk, hl, ?_⟩
  · intro x y hxy
    have h1 : w y ≤ w x := hw hxy.le
    have h2 : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast hxy
    have h3 : ((w y : ℤ) : ℝ) ≤ ((w x : ℤ) : ℝ) := by exact_mod_cast h1
    simp; linarith
  · have h1 : ((w l : ℤ) : ℝ) + 1 ≤ ((w k : ℤ) : ℝ) := by exact_mod_cast hg
    have h2 : ((l : ℕ) : ℝ) = ((k : ℕ) : ℝ) + 1 := by exact_mod_cast hl
    simp; linarith

example (π : CuspSub E 3) : OddOrSlightlyReg π := OddOrSlightlyReg.of_odd π ⟨1, rfl⟩

example (π : CuspSub E 4) (h : SlightlyRegAll π) : OddOrSlightlyReg π := .of_slightlyReg (h.slightlyReg (by norm_num))

example (π : CuspSub E 4) (τ : E →+* ℂ)
    (h : (CG.mk π).infChar τ = Finset.univ.val.map fun k : Fin 4 => ((![3, 2, 1, 1] k : ℤ) : ℂ) + (((4 : ℂ) - 1) / 2 - (k : ℕ))) :
    SlightlyReg π :=
  slightlyReg_of_weight π τ ![3, 2, 1, 1] (by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all <;> omega)
    (by simpa using h) 0 1 ⟨0, rfl⟩ rfl (by decide)

end GlobalTheory.CBGal

end
