import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace

variable (D : D7) (u : D.what₂.Word)

def TwoTerm (A x : ℝ) : Prop := hsDev D u ≤ A * (d0 D u : ℝ) ^ 2 / D.what₂.Dstar + x * (d0 D u : ℝ)

def mfL (L : ℝ) : ℝ := (D.R.m : ℝ) ^ 5 * D.R.f * L

def kfk : ℝ := (D.R.k : ℝ) * D.R.f * Real.log D.R.k

def SDiag (L C : ℝ) : Prop :=
  TwoTerm D u (4 * (Real.exp (C * mfL D L) + 1)) (4 * Real.exp (-(kfk D / 2)) + 2 * Real.exp (-kfk D))

def Small (L C : ℝ) : Prop := (d0 D u : ℝ) ≤ D.what₂.Dstar * Real.exp (-(2 * C * mfL D L))

def eDiag (L C : ℝ) : ℝ := 8 * Real.exp (-(C * mfL D L)) + 6 * Real.exp (-(kfk D / 2))

def RankMu : Prop :=
  (d0 D u : ℝ) = ((D.mem u).A.duStar : ℝ) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def Road1At : Prop := ∃ e δ : ℝ, DiagS D u e ∧ KerIncl D u ∧ RamBig D u δ ∧ 2 * e < 1 - δ

def cK : ℝ := (c0 D.s u * c0 D.s u) ^ (-(1 / 2 : ℝ))

def KerInclOn (Rw : Submodule ℂ D.s.HH) : Prop :=
  ∃ FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u, Function.Injective FF ∧
    ∀ φ : (D.mem u).A.Mram, PhiC (D.mem u).C (D.mem u).A (D.mem u).P φ = 0 → ∀ y ∈ Rw, ⟪y, D.s.Pu u (FF φ)⟫_ℂ = 0

def BadMass (Rw : Submodule ℂ D.s.HH) (η : ℝ) : Prop :=
  cK D u * hsNormSq ((Rwᗮ).starProjection.comp (D.s.Pu u)) ≤ η * (d0 D u : ℝ)

def Road2At : Prop :=
  ∃ (Rw : Submodule ℂ D.s.HH) (e η δ : ℝ), 0 ≤ e ∧ 0 ≤ η ∧ DiagS D u e ∧ BadMass D u Rw η ∧ KerInclOn D u Rw ∧ RamBig D u δ ∧
    2 * (Real.sqrt e + Real.sqrt η) ^ 2 < 1 - δ

namespace Pts

variable (F : Pts)

def EvSome (Q : ℝ → ∀ D : D7, D.what₂.Word → Prop) : Prop := ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ i : F.Ix x, ∃ u, Q x (F.D x i) u

def EvAll (Q : ℝ → ∀ D : D7, D.what₂.Word → Prop) : Prop := ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ (i : F.Ix x) u, Q x (F.D x i) u

theorem EvAll.some {F : Pts} {Q : ℝ → ∀ D : D7, D.what₂.Word → Prop} (h : F.EvAll Q) : F.EvSome Q :=
  let ⟨x₀, h⟩ := h; ⟨x₀, fun x hx i => ⟨(F.D x i).u₀, h x hx i _⟩⟩

theorem EvAll.and {F : Pts} {Q Q' : ℝ → ∀ D : D7, D.what₂.Word → Prop} (h : F.EvAll Q) (h' : F.EvAll Q') :
    F.EvAll fun x D u => Q x D u ∧ Q' x D u :=
  let ⟨a, h⟩ := h; let ⟨b, h'⟩ := h'
  ⟨max a b, fun x hx i u => ⟨h x (le_trans (le_max_left _ _) hx) i u, h' x (le_trans (le_max_right _ _) hx) i u⟩⟩

theorem EvSome.rkAll {F : Pts} (h : F.EvSome fun _ D u => RK D u) : F.RKAll := h

end Pts

end GlobalTheory.Core.Rk

end
