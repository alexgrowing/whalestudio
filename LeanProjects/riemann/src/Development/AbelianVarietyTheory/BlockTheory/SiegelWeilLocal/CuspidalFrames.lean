import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open MeasureTheory NumberField
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames

open Formalism.MainNotions.S GlobalTheory.Count

def IsCuspidalFrame (B : RowsAut) (Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
    (T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) : Prop :=
  (∀ i, T i ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
    (∀ i, T i ∈ B.I.HomS B.σs B.μf B.fund B.R) ∧
    (∀ i u, ‖T i u‖ = ‖u‖) ∧
    (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧
    Submodule.span ℂ (Set.range T) = B.I.eHom B.σs B.μf B.fund B.R B.Re ∧
    (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) ∧
    (∀ i u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T i u) = T i u) ∧
    Orthonormal ℂ (fun i => T i (B.tens B.w)) ∧
    Submodule.span ℂ (Set.range fun i => T i (B.tens B.w)) = LinearMap.range Rφ.toLinearMap

def CuspidalIntertwiners : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (h : ℝ),
    IsDSData B d → SigIs B p q → 1 ≤ min p q → 1 ≤ B.g → GapGe B h →
    40 * (B.I.n : ℝ) ^ 2 * Real.sqrt ((min p q : ℕ) : ℝ) ≤ h →
    16 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) < h →
    ∃ Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund,
      B.I.IsRConv B.μf B.fund B.R (phe B d) Rφ ∧
        ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), IsCuspidalFrame B Rφ T

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames
