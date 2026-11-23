import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MulInvLevAMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.NatSmulMulEq
import Mathlib

noncomputable section

namespace PI.IwaMeasEx.LP

open MeasureTheory Topology Set
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.AfT

variable {X : CData} {n₀ : ℕ} {A : ℝ} {J : ℕ}

theorem map_val_mul' {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (K : Subgroup G) (g : K) (α : Measure K) :
    (α.map (fun x => g * x)).map Subtype.val = (α.map Subtype.val).map (fun x => (g : G) * x) := by
  rw [Measure.map_map measurable_subtype_coe (measurable_const_mul g),
    Measure.map_map (measurable_const_mul _) measurable_subtype_coe]
  rfl

structure UnipotentMeasureProperties {J : ℕ} (D : BaseDatum X.I J) (c : Composition J) (μN : Measure X.I.GA) : Prop where
  sfin : SigmaFinite μN
  ne : μN ≠ 0
  supp : μN (D.toWittFrame.uniA c : Set X.I.GA)ᶜ = 0
  cpt : ∀ s : Set X.I.GA, IsCompact s → μN s ≠ ⊤
  inv : ∀ n ∈ D.toWittFrame.uniA c, μN.map (fun x => n * x) = μN

def ModL : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), PI.IwaMeasEx.Sk.Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    ∀ μN : Measure X.I.GA, UnipotentMeasureProperties D c μN → ∀ m ∈ D.toWittFrame.leviA c,
      μN.map (fun x => m * x * m⁻¹) = PI.IwaMeasEx.Sk.wgt D c m • μN

end PI.IwaMeasEx.LP

end
