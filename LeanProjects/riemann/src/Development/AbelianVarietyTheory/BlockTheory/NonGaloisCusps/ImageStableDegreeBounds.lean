import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds

open PowerSeries GlobalTheory.BK

section Ring

variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ)

def SHigh : Ideal (S O K e) :=
  (Ideal.span {(X : K⟦X⟧) ^ (l * e)}).comap (S O K e).val

variable {O K l e} in
theorem mem_SHigh {f : S O K e} : f ∈ SHigh O K l e ↔ (X : K⟦X⟧) ^ (l * e) ∣ (f : K⟦X⟧) := by
  rw [SHigh, Ideal.mem_comap, Ideal.mem_span_singleton]
  rfl

structure RingModHigh : Prop where
  N_stable : ∀ f ∈ SHigh O K l e, ∃ g ∈ SHigh O K l e, (g : K⟦X⟧) = N K (f : K⟦X⟧)
  eq_add : ∀ f : K⟦X⟧, f ∈ S O K e ↔ ∃ g ∈ A O K, ∃ h ∈ SHigh O K l e, f = g + (h : K⟦X⟧)
  inter_eq : ∀ f : K⟦X⟧, (f ∈ A O K ∧ ∃ h ∈ SHigh O K l e, (h : K⟦X⟧) = f) ↔
    ∃ g ∈ A O K, f = ((X : K⟦X⟧) ^ e) ^ l * g

end Ring

section Degrees

variable {e : ℕ}

def degrees (Sig : Finset (ZMod e)) (c : ZMod e) (m m' : ℕ) : Finset ℕ :=
  (Sig ×ˢ Finset.Ico m m').image fun p => (c - p.1).val + p.2 * e

def D₁ (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) : Finset ℕ := degrees Sig c 0 A'

def D₂ (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) : Finset ℕ := degrees Sig c A' (2 * A')

def rootPoly (T : Finset ℕ) : Polynomial ℤ := ∏ i ∈ T, (Polynomial.X - Polynomial.C (i : ℤ))

def P₁ (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) : Polynomial ℤ := rootPoly (D₁ Sig c A')

def P₂ (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) : Polynomial ℤ := rootPoly (D₂ Sig c A')

structure DegreeBounds (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) : Prop where
  lt_of_mem₁ : ∀ i ∈ D₁ Sig c A', i < e * A'
  mem_Ico₂ : ∀ j ∈ D₂ Sig c A', e * A' ≤ j ∧ j < 2 * e * A'
  monic₁ : (P₁ Sig c A').Monic
  monic₂ : (P₂ Sig c A').Monic
  disjoint_roots : Disjoint (P₁ Sig c A').roots (P₂ Sig c A').roots
  card₁ : (D₁ Sig c A').card ≤ Sig.card * A'
  card₂ : (D₂ Sig c A').card ≤ Sig.card * A'

end Degrees

section Modules

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def MMHigh (P : PhiMod O K l e a ι) : Submodule O (Vec K a ι) :=
  (SHigh O K l e • P.MM).restrictScalars O

def mulL (P : PhiMod O K l e a ι) (f : K⟦X⟧) : Submodule O (Vec K a ι) :=
  (P.L.restrictScalars O).map ((mulV K a ι f).restrictScalars O)

theorem mem_mulL {P : PhiMod O K l e a ι} {f : K⟦X⟧} {x : Vec K a ι} :
    x ∈ mulL P f ↔ ∃ y ∈ P.L, f • y = x := by
  simp only [mulL, Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.restrictScalars_apply,
    mulV_apply]

abbrev uL (P : PhiMod O K l e a ι) (i : ℕ) : Submodule O (Vec K a ι) := mulL P (X ^ i)

abbrev vL (P : PhiMod O K l e a ι) (n : ℕ) : Submodule O (Vec K a ι) := mulL P ((X ^ e) ^ n)

abbrev part (W : Submodule K (Vec K a ι)) (V : Submodule O (Vec K a ι)) : Submodule O (Vec K a ι) :=
  V ⊓ W.restrictScalars O

variable [Fact l.Prime]

structure ModHigh (P : PhiMod O K l e a ι) (W : Submodule K (Vec K a ι)) : Prop where
  MM_eq : part W (P.MM.restrictScalars O) = part W (P.L.restrictScalars O) ⊔ part W (MMHigh P)
  inter_eq : part W (P.L.restrictScalars O) ⊓ part W (MMHigh P) = part W (vL P l)
  conn_MM : ∀ x ∈ part W (P.MM.restrictScalars O), P.conn x ∈ part W (P.MM.restrictScalars O)
  conn_high : ∀ x ∈ part W (MMHigh P), P.conn x ∈ part W (MMHigh P)
  conn_uL : ∀ i : ℕ, ∀ x ∈ part W (uL P i) ⊔ part W (MMHigh P),
    P.conn x ∈ part W (uL P i) ⊔ part W (MMHigh P)
  conn_graded : ∀ i : ℕ, i < l * e → ∀ x ∈ part W (uL P i),
    P.conn x - i • x ∈ part W (uL P (i + 1)) ⊔ part W (MMHigh P)

def ImageStable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)
    (W : Submodule K (Vec K a κ)) : Prop :=
  ∀ x ∈ part W (F.imL.restrictScalars O) ⊔ part W (MMHigh Q),
    Q.conn x ∈ part W (F.imL.restrictScalars O) ⊔ part W (MMHigh Q)

variable [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]

structure RaisesDegree {P : PhiMod O K l e a ι} (Δ : Descent P) (Sig : Finset (ZMod e)) (c : ZMod e)
    (A' : ℕ) : Prop where
  graded_eq_zero : ∀ i : ℕ, (¬ ∃ c' ∈ Sig, ∃ n : ℕ, i = (c - c').val + n * e) →
    part (Δ.isotypic c) (uL P i) ≤ uL P (i + 1)
  aeval₁ : ∀ x ∈ part (Δ.isotypic c) (P.L.restrictScalars O),
    Polynomial.aeval P.conn (P₁ Sig c A') x ∈ vL P A' ⊔ MMHigh P
  aeval₂ : ∀ x ∈ part (Δ.isotypic c) (vL P A'),
    Polynomial.aeval P.conn (P₂ Sig c A') x ∈ vL P (2 * A') ⊔ MMHigh P

end Modules

section Statement

variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]

def Reduction : Prop :=
  RingModHigh O K l e ∧
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H),
    ModHigh D.toPhiMod ⊤ ∧
    (∀ ζ x, D.desc.act (TameGal.inertia ζ) (D.conn x) = D.conn (D.desc.act (TameGal.inertia ζ) x)) ∧
    ∀ c : ZMod e, ModHigh D.toPhiMod (D.desc.isotypic c)) ∧
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (η H : ℕ)
    (B₁ : BKDat O K l e a ι η H) (B₂ : BKDat O K l e a κ η H) (F : BKHom B₁ B₂),
    (∀ x ∈ B₁.MM, F.app x ∈ B₂.MM ∧ F.app (B₁.conn x) = B₂.conn (F.app x)) ∧
    ImageStable F.toHom ⊤ ∧ ∀ c : ZMod e, ImageStable F.toHom (B₂.desc.isotypic c)

def Degrees : Prop :=
  ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ), 2 * A' ≤ l →
    DegreeBounds Sig c A' ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H),
      (∀ τ, D.desc.chars τ ⊆ (Sig : Set (ZMod e))) → RaisesDegree D.desc Sig c A'

end Statement

def NModHighDegree : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a],
    Reduction O K l e a ∧ Degrees O K l e a

example : D₁ ({0, 1, 3} : Finset (ZMod 8)) 1 1 = {0, 1, 6} ∧
    D₂ ({0, 1, 3} : Finset (ZMod 8)) 1 1 = {8, 9, 14} := by decide

example (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NeZero e] :
    uIn (S O K e) ^ (l * e) ∈ SHigh O K l e ∧ (1 : S O K e) ∉ SHigh O K l e := by
  refine ⟨mem_SHigh.2 (by simp), fun h => ?_⟩
  have h1 := X_pow_dvd_iff.1 (mem_SHigh.1 h) 0
    (Nat.mul_pos (Fact.out : l.Prime).pos (NeZero.pos e))
  simp at h1

end GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds
