import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Example
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Subbundle

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}

def IsSubbundle (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (segreCoord y) N E) (F : Submodule Ω E)
    (r : ℕ) : Prop :=
  ∀ c : (k : K) → ι k, segreCoord y c ≠ 0 →
    ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ chartRing ℤ (segreCoord y) c) ∧
      (∀ l, a l ∈ chartRing ℤ (segreCoord y) c) ∧ ∑ l, a l * f l = 1 ∧
      ∀ l, f l ≠ 0 → ∃ b : Fin N → E, IsFrameOver y W c (f l) b ∧
        Submodule.span Ω (b '' {i | (i : ℕ) < r}) = F

end Subbundle

structure ComponentDataHodge (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type)
    [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] extends ComponentData II Ψ K ι Ω E where

  F : ∀ τ, Submodule Ω (E τ)
  hodge : ∀ τ, IsSubbundle y (W τ) (F τ) j

namespace Line

def lineDataHodge (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2]) :
    ComponentDataHodge II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) where
  toComponentData := lineData II hII
  F _ := Submodule.span Ω ((Pi.basisFun Ω (Fin 2)) '' {i | (i : ℕ) < 1})
  hodge _ c hc := ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp,
    fun _ _ => ⟨Pi.basisFun Ω (Fin 2), ⟨hc, one_mem _, one_ne_zero,
      (Pi.basisFun Ω (Fin 2)).linearIndependent, trivial_frame_iff _ 2 c⟩, rfl⟩⟩

def lineDataHodgeZero : ComponentDataHodge zeroSystem Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) :=
  lineDataHodge zeroSystem fun _ _ => le_rfl

theorem finrank_lineDataHodge_F (II : IntersectionSystem) (hII) :
    Module.finrank Ω ((lineDataHodge II hII).F ()) = 1 := by
  show Module.finrank Ω (Submodule.span Ω ((Pi.basisFun Ω (Fin 2)) '' {i | (i : ℕ) < 1})) = 1
  have : (Pi.basisFun Ω (Fin 2)) '' {i | (i : ℕ) < 1} = {Pi.basisFun Ω (Fin 2) 0} := by
    ext v
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [show i = 0 from Fin.ext (Nat.lt_one_iff.mp hi)]
    · rintro rfl
      exact ⟨0, by simp, rfl⟩
  rw [this, finrank_span_singleton ((Pi.basisFun Ω (Fin 2)).ne_zero 0)]

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
