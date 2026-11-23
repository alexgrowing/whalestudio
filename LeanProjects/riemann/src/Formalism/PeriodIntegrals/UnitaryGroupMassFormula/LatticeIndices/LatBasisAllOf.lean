import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplitLat

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

section Gen

variable {K : Type} [Field K] (O : ValuationSubring K) {n : Type} [Fintype n] [DecidableEq n]

theorem dual_basis_iff (P : GL n K) (J : Matrix n n K) (z : n → K) :
    (∀ y : n → K, (∀ i, (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) i ∈ O) → z ⬝ᵥ (J *ᵥ y) ∈ O) ↔
      ∀ i, ((Matrix.transpose (P : Matrix n n K) * Matrix.transpose J) *ᵥ z) i ∈ O := by
  have key : ∀ c : n → K, z ⬝ᵥ (J *ᵥ ((P : Matrix n n K) *ᵥ c)) =
      ((Matrix.transpose (P : Matrix n n K) * Matrix.transpose J) *ᵥ z) ⬝ᵥ c := by
    intro c
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_mul]
  have hPP : ∀ c : n → K, ((P⁻¹ : GL n K) : Matrix n n K) *ᵥ ((P : Matrix n n K) *ᵥ c) = c := by
    intro c
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hPP' : ∀ y : n → K, (P : Matrix n n K) *ᵥ (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  constructor
  · intro h i
    have h1 := h ((P : Matrix n n K) *ᵥ Pi.single i 1) (by
      intro j
      rw [hPP]
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij])
    rw [key, dotProduct_single_one] at h1
    exact h1
  · intro h y hy
    rw [← hPP' y, key]
    exact sum_mem fun i _ => mul_mem (h i) (hy i)

end Gen

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

abbrev OpX : ValuationSubring (FpX X p) := p.1.adicCompletionIntegers X.B.I.F

def iota1 : X.B.I.E →+* FpX X p := (th1 X p θ).comp (inclR (FpX X p))

def iota2 : X.B.I.E →+* FpX X p := (th2 X p θ).comp (inclR (FpX X p))

def Mlat1 : Submodule (OpX X p) (Fin X.B.I.n → FpX X p) :=
  Submodule.span (OpX X p) ((fun l : Fin X.B.I.n → X.B.I.E => fun j => iota1 X p θ (l j)) ''
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))

def Mlat2 : Submodule (OpX X p) (Fin X.B.I.n → FpX X p) :=
  Submodule.span (OpX X p) ((fun l : Fin X.B.I.n → X.B.I.E => fun j => iota2 X p θ (l j)) ''
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))

def LatSplitP : Prop :=
  ∀ x : Fin X.B.I.n → TpX X p, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    (fun j => th1 X p θ (x j)) ∈ Mlat1 X p θ ∧ (fun j => th2 X p θ (x j)) ∈ Mlat2 X p θ

def LatFreeP : Prop :=
  ∃ P : GL (Fin X.B.I.n) (FpX X p), ∀ y, y ∈ Mlat1 X p θ ↔
    ∀ i, (((P⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *ᵥ y) i ∈ OpX X p

def LatDualP : Prop :=
  ∀ z, z ∈ Mlat2 X p θ ↔ ∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p

theorem latBasis_of (hS : LatSplitP X p θ) (hF : LatFreeP X p θ) (hD : LatDualP X p θ) :
    ∃ P, LatBasis X p θ P := by
  obtain ⟨P, hP⟩ := hF
  refine ⟨P, fun x => ?_⟩
  rw [hS x, hD, hP]
  refine and_congr Iff.rfl ?_
  rw [← dual_basis_iff (OpX X p) P (J1 X p θ)]
  exact ⟨fun h y hy => h y ((hP y).2 hy), fun h y hy => h y ((hP y).1 hy)⟩

theorem latBasisAll_of
    (hS : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatSplitP X p θ)
    (hF : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatFreeP X p θ)
    (hD : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatDualP X p θ) :
    LatBasisAll X p := fun θ hθ => latBasis_of X p θ (hS θ hθ) (hF θ hθ) (hD θ hθ)

end Loc

end MassDataIdxSteps
