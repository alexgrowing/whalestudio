import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.LocFub

open GlobalTheory.CxForm

def headL (n : ℕ) : V (n + 1) →L[ℂ] V n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun a : Fin n => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
      (Fin.castSucc a)).comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (n + 1) => ℂ)).toContinuousLinearMap)

def fibL (n : ℕ) : V 1 →L[ℂ] V (n + 1) :=
  (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ).smulRight (EuclideanSpace.single (Fin.last n) (1 : ℂ))

theorem headL_apply {n : ℕ} (v : V (n + 1)) (a : Fin n) : headL n v a = v (Fin.castSucc a) := rfl

theorem fibL_apply {n : ℕ} (v : V 1) : fibL n v = EuclideanSpace.single (Fin.last n) (v 0) := by
  ext a; simp [fibL, EuclideanSpace.single_apply]

variable {M : Type} [TopologicalSpace M]

def pbDensC {m k : ℕ} (A : HolAtlas M m) (α : A.Fld) (Ψ : V k → M) (v : V k) : ℂ :=
  dens (pull (fderiv ℂ (A.e (A.cover (Ψ v)).choose ∘ Ψ) v)
    (α ⟨((A.cover (Ψ v)).choose, Ψ v), (A.cover (Ψ v)).choose_spec⟩))

def pbDens {m k : ℕ} (A : HolAtlas M m) (α : A.Fld) (Ψ : V k → M) (v : V k) : ℝ := (pbDensC A α Ψ v).re

def fibDensC {m : ℕ} (A : HolAtlas M m) (α : A.Fld) (φ : ℂ → M) (x : ℂ) : ℂ :=
  dens (pull ((fderiv ℂ (A.e (A.cover (φ x)).choose ∘ φ) x).comp (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ))
    (α ⟨((A.cover (φ x)).choose, φ x), (A.cover (φ x)).choose_spec⟩))

def fibDens {m : ℕ} (A : HolAtlas M m) (α : A.Fld) (φ : ℂ → M) (x : ℂ) : ℝ := (fibDensC A α φ x).re

def prodMap {N : Type} [TopologicalSpace N] {n : ℕ} (A : HolAtlas N n) (i : A.ι) (Φ : N → ℂ → M) (v : V (n + 1)) : M :=
  Φ ((A.e i).symm (headL n v)) (v (Fin.last n))

end GlobalTheory.LocFub
