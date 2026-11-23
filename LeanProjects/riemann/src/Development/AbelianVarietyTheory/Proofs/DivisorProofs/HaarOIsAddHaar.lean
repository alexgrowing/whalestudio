import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

noncomputable section

namespace GlobalTheory.StdPairLoc

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

variable {F : Type} [Field F] [NumberField F]

section Blocks

variable {R : Type} {n a m : ℕ}

def leftBlock (X : Matrix (Fin n) (Fin (a + m)) R) : Matrix (Fin n) (Fin a) R := fun i j => X i (Fin.castAdd m j)

def rightBlock' (X : Matrix (Fin n) (Fin (a + m)) R) : Matrix (Fin n) (Fin m) R := fun i j => X i (Fin.natAdd a j)

end Blocks

def InPow (v : Pl F) (c : ℕ) (x : Fv F v) : Prop := ((unifAt v : Fv F v) ^ c)⁻¹ * x ∈ v.adicCompletionIntegers F

def InGLO (v : Pl F) {p : ℕ} (A : Matrix (Fin p) (Fin p) (Fv F v)) : Prop :=
  (∀ i j, A i j ∈ v.adicCompletionIntegers F) ∧ A.det ≠ 0 ∧ A.det⁻¹ ∈ v.adicCompletionIntegers F

open Classical in

def stdBig (v : Pl F) (ν : (Fv F v)ˣ →* ℂˣ) {a m : ℕ} (X : Matrix (Fin a) (Fin (a + m)) (Fv F v)) : ℂ :=
  if h : InGLO v (leftBlock X) ∧ ∀ i j, InPow v (condExp ν) (rightBlock' X i j) then
    (((ν (Units.mk0 _ h.1.2.1))⁻¹ : ℂˣ) : ℂ) else 0

open Classical in

def stdSmall (v : Pl F) (ν : (Fv F v)ˣ →* ℂˣ) {a' a : ℕ} (Y : Matrix (Fin a') (Fin (a + a')) (Fv F v)) : ℂ :=
  if h : (∀ i j, InPow v (condExp ν) (leftBlock Y i j)) ∧ InGLO v (rightBlock' Y) then
    (((ν (Units.mk0 _ h.2.2.1))⁻¹ : ℂˣ) : ℂ) else 0

section Ins

variable {R : Type} [Zero R] {a b : ℕ}

def insB (Y : Matrix (Fin a) (Fin (a + b)) R) (t : Fin a → R) : Matrix (Fin a) (Fin (a + (b + 2))) R := fun i j =>
  if h₁ : j.1 < a then Y i ⟨j.1, by omega⟩ else if h₂ : j.1 = a then t i else if h₃ : j.1 = a + b + 1 then 0 else
    Y i ⟨j.1 - 1, by have := j.2; omega⟩

def insS (Y : Matrix (Fin b) (Fin (a + b)) R) (r : Fin (a + (b + 2)) → R) (c : Fin b → R) (l : R) :
    Matrix (Fin (b + 2)) (Fin (a + (b + 2))) R := fun i j =>
  if i0 : i.1 = 0 then (if j.1 = a + b + 1 then l else 0) else if i1 : i.1 = b + 1 then r j else
    if h₁ : j.1 < a then Y ⟨i.1 - 1, by have := i.2; omega⟩ ⟨j.1, by omega⟩ else if h₂ : j.1 = a then 0 else
      if h₃ : j.1 = a + b + 1 then c ⟨i.1 - 1, by have := i.2; omega⟩ else
        Y ⟨i.1 - 1, by have := i.2; omega⟩ ⟨j.1 - 1, by have := j.2; omega⟩

end Ins

def intInd (v : Pl F) {p r : ℕ} : Matrix (Fin p) (Fin r) (Fv F v) → ℂ :=
  Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1

def intPC (v : Pl F) : TopologicalSpace.PositiveCompacts (Fv F v) :=
  ⟨⟨v.adicCompletionIntegers F, isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)⟩,
    ⟨0, mem_interior_iff_mem_nhds.2 ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))⟩⟩

def haarO (v : Pl F) : MeasureTheory.Measure (Fv F v) := MeasureTheory.Measure.addHaarMeasure (intPC v)

def haarVec (v : Pl F) (p : ℕ) : MeasureTheory.Measure (Fin p → Fv F v) := MeasureTheory.Measure.pi fun _ => haarO v

theorem haarO_isAddHaar (v : Pl F) : (haarO v).IsAddHaarMeasure := MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure _

end GlobalTheory.StdPairLoc

end
