import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsCuspHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.MainNotions.ArithmeticCylinders IsDedekindDomain MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLev

theorem isEnum_parA_zero (D : D7) {n : ℕ} (hn : n = D.R.r) (τ : D.what₂.Tau) :
    IsEnum (parA (tparRec D) 0 τ) (fun i : Fin n => lamS D.R (D.hc τ) (Fin.cast hn i))
      (fun i => epsS D.R (Fin.cast hn i)) := by
  subst hn
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  simp only [Fin.cast_eq_self]
  refine ⟨?_, fun i => if h : i.val < D.R.k - 1 then (D.hc τ).v ⟨i.val, h⟩
    else if h' : i.val - (D.R.k - 1) < D.R.m then -(D.hc τ).b ⟨i.val - (D.R.k - 1), h'⟩ else 0, ?_, ?_⟩
  · have h := (GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)).1
    intro a b hab
    have := h (a := Fin.cast (dimS_eq D.R).symm a) (b := Fin.cast (dimS_eq D.R).symm b) hab
    simpa [lamSH] using this
  · intro a
    simp only [lamS]
    split_ifs <;> simp
  · have hpar : ∀ a : ℕ, decide (a ≤ 0 ∨ Even (a - 0)) = decide (a % 2 = 0) := by
      intro a
      rw [decide_eq_decide, Nat.sub_zero, Nat.even_iff]
      omega
    ext x
    simp only [parA, TPar.Dpar, tparRec, tparHC, hpar, Nat.not_odd_zero, if_false, add_zero,
      Nat.not_lt_zero, Finset.filter_false, Finset.biUnion_empty, Finset.union_empty, Prod.mk.eta,
      Finset.image_id', Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · refine ⟨⟨i.val, by have := i.2; omega⟩, ?_⟩
        simp [epsS, i.2]
      · refine ⟨⟨i.val + (D.R.k - 1), by have := i.2; omega⟩, ?_⟩
        simp [epsS, i.2]
    · rintro ⟨a, rfl⟩
      by_cases h : a.val < D.R.k - 1
      · exact Or.inl ⟨⟨a.val, h⟩, by simp [epsS, h]⟩
      · have h' : a.val - (D.R.k - 1) < D.R.m := by have := a.2; omega
        exact Or.inr ⟨⟨_, h'⟩, by simp [epsS, h, h']⟩

end GlobalTheory.RowLev
