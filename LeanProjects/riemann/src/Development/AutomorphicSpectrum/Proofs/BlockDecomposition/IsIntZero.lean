import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

def IsInt {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {r s : Type}
    (M : Matrix r s (w.adicCompletion E)) : Prop :=
  ∀ i j, M i j ∈ Ov E w

def coef (q : ℕ) (c : ℂˣ) (a b i j : ℕ) : ℂ :=
  (c : ℂ) ^ (i * b + j * a) * (q : ℂ) ^ (((i : ℂ) * b + (j : ℂ) * a) / 2 - (i : ℂ) * j)

def pairs (a b k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.HasAntidiagonal.antidiagonal k).filter fun p => p.1 ≤ a ∧ p.2 ≤ b

theorem mem_pairs {a b k : ℕ} {p : ℕ × ℕ} : p ∈ pairs a b k ↔ p.1 + p.2 = k ∧ p.1 ≤ a ∧ p.2 ≤ b := by
  simp [pairs, Finset.mem_filter]

theorem IsInt.add {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s : Type}
    {M N : Matrix r s (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) : IsInt w (M + N) :=
  fun i j => (Ov E w).add_mem (hM i j) (hN i j)

theorem IsInt.neg {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s : Type}
    {M : Matrix r s (w.adicCompletion E)} (hM : IsInt w M) : IsInt w (-M) :=
  fun i j => (Ov E w).neg_mem (hM i j)

theorem isInt_zero {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r s : Type) :
    IsInt w (0 : Matrix r s (w.adicCompletion E)) :=
  fun _ _ => (Ov E w).zero_mem

def intSub {E : Type} [Field E] [NumberField E] (a b : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | IsInt w X}
  zero_mem' := isInt_zero w _ _
  add_mem' := fun h h' => h.add h'
  neg_mem' := fun h => h.neg

def latM {E : Type} [Field E] [NumberField E] {a b : ℕ} {w : HeightOneSpectrum (𝓞 E)} (ϖ : w.adicCompletion E)
    (m : GL (Fin a) (w.adicCompletion E) × GL (Fin b) (w.adicCompletion E)) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | IsInt w (m.1.val * X) ∧ IsInt w (ϖ • (X * (m.2⁻¹).val))}
  zero_mem' := by
    refine ⟨?_, ?_⟩ <;> simpa using isInt_zero w _ _
  add_mem' := by
    rintro X Y ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_add]; exact h1.add h3
    · rw [Matrix.add_mul, smul_add]; exact h2.add h4
  neg_mem' := by
    rintro X ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_neg]; exact h1.neg
    · rw [Matrix.neg_mul, smul_neg]; exact h2.neg

def latD {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} (ϖ : w.adicCompletion E) (a b i j : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {W | ∀ (r : Fin a) (s : Fin b), (if (r : ℕ) < i ∧ j ≤ (s : ℕ) then ϖ * W r s else W r s) ∈ Ov E w}
  zero_mem' := by
    intro r s
    simp only [Matrix.zero_apply, mul_zero, ite_self]
    exact (Ov E w).zero_mem
  add_mem' := by
    intro X Y h1 h2 r s
    have e1 := h1 r s
    have e2 := h2 r s
    simp only [Matrix.add_apply]
    split_ifs at e1 e2 ⊢
    · rw [mul_add]; exact (Ov E w).add_mem e1 e2
    · exact (Ov E w).add_mem e1 e2
  neg_mem' := by
    intro X h1 r s
    have e1 := h1 r s
    simp only [Matrix.neg_apply]
    split_ifs at e1 ⊢
    · rw [mul_neg]; exact (Ov E w).neg_mem e1
    · exact (Ov E w).neg_mem e1

end GlobalTheory.CompanionTheory.CtS
