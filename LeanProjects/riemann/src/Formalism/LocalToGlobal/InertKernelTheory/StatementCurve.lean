import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.ColumnData

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions
open Formalism.L2.Th1.H (cmL CmOK)

def CurveTie : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → Odd (Ideal.absNorm cc) → δ ≠ 0 →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧ cc ≤ Ideal.span {(g : 𝓞 D.host.K)} ∧
      TaylorLogMetric.lamOf D cc δ = (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup

def CurveTiePrim : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → Odd (Ideal.absNorm cc) →
    (∀ m : ℕ, 1 < m → ¬ cc ≤ Ideal.span {(m : 𝓞 D.host.K)}) → ∀ hδ : δ ≠ 0,
    ∃ (b₀ c₀ : ℤ) (ha : 0 < Ideal.absNorm cc) (hd : 0 < D.host.d),
      CmOK (Ideal.absNorm cc) b₀ c₀ D.host.d ∧
      TaylorLogMetric.lamOf D cc δ = (cmL (Ideal.absNorm cc) b₀ D.host.d ha hd δ hδ).lattice.toAddSubgroup

def CurveTieK : Prop :=
  ∀ (D : D7) (δ : ℂ) (hδ : δ ≠ 0),
    ∃ (b₀ c₀ : ℤ) (ha : 0 < Ideal.absNorm D.host.ccK) (hd : 0 < D.host.d),
      CmOK (Ideal.absNorm D.host.ccK) b₀ c₀ D.host.d ∧
      TaylorLogMetric.lamOf D D.host.ccK δ = (cmL (Ideal.absNorm D.host.ccK) b₀ D.host.d ha hd δ hδ).lattice.toAddSubgroup

def CurveTieCar : Prop :=
  ∀ (D : Formalism.L2.Ker.Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → Odd (Ideal.absNorm cc) → δ ≠ 0 →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧ cc ≤ Ideal.span {(g : 𝓞 D.host.K)} ∧
      Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ = (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup

def CmBaseExists : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → δ ≠ 0 →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0) (B : Formalism.L2.Ker.Base D cc δ),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧ B.IsCm a₀ b₀ ha hd ((g : ℂ) * δ) hl

def CmReBase : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → δ ≠ 0 →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧
      (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ ∧
      GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (((g : ℂ) * δ) * a₀ / 2) ∧
      (B.ω₀ - ((g : ℂ) * δ) * a₀) / 2 ∈ TaylorLogMetric.lamOf D cc δ

def BaseLatTie : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧
      B.L.lattice = (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice

end Formalism.L2.KerInert
