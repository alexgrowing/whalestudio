import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridHC

open GlobalTheory.SignedHC Finset

theorem inCoset_weightX (D : D7) (τ : D.what₂.Tau) (j : ℕ) : InCoset (1 / 2) ((GlobalTheory.Grid.grid D τ).weightX j) := by
  induction j with
  | zero => exact GlobalTheory.ChiGrid.inCoset_weightX_zero (GlobalTheory.ChiGrid.odd_sLen D)
  | succ j ih =>
    rw [(GlobalTheory.Grid.grid D τ).weightX_succ]
    intro x hx
    rcases mem_union.1 hx with h | h
    · exact ih x h
    · obtain ⟨a, -, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
      obtain ⟨u, hu⟩ := D.R.t_odd
      have e : ((GlobalTheory.Grid.grid D τ).t : ℚ) = 2 * u + 1 := by
        have : ((GlobalTheory.Grid.grid D τ).t : ℚ) = D.R.t := rfl
        rw [this, hu]; push_cast; ring
      refine ⟨-(GlobalTheory.Grid.grid D τ).e (j + 1) + u - a, ?_⟩
      push_cast
      rw [e]
      ring

theorem even_rkX (D : D7) (j : ℕ) : Even (GlobalTheory.Grid.rkX D j) := GlobalTheory.ChiGrid.even_rankX D j

theorem isHCParam_parXp : ∀ (D : D7), HostHyp D → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ)
    (ε : Fin n → Bool), n = GlobalTheory.Grid.rkX D j → IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ j _ _ τ n lam ε hn hE
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : (q a, ε a) ∈ GlobalTheory.Grid.parXp D j τ := by
    rw [hS]; exact mem_image.2 ⟨a, mem_univ _, rfl⟩
  have hx : q a ∈ (GlobalTheory.Grid.grid D τ).weightX j := by
    obtain ⟨x, hx, hxe⟩ := mem_image.1 hmem
    have : x = q a := congrArg Prod.fst hxe
    exact this ▸ hx
  obtain ⟨z, hz⟩ := inCoset_weightX D τ j (q a) hx
  obtain ⟨k, hk⟩ := even_rkX D j
  refine ⟨z - k + 1, ?_⟩
  rw [hq a, hz, hn, hk]
  push_cast
  ring

end GlobalTheory.GridHC
