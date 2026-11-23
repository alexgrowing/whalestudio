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

namespace GlobalTheory.Grid

open GlobalTheory.SignedHC

theorem isHCParam_parP : ∀ (D : D7), HostHyp D → ∀ (i : ℕ), i ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkP D i → IsEnum (GlobalTheory.Grid.parP D i τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ i _ τ n lam ε hn hE
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : q a ∈ (grid D τ).weightX 0 := by
    have h0 : (q a, ε a) ∈ parP D i τ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rcases GridData.mem_parPi.1 h0 with ⟨l, hl, h⟩ | ⟨h1, _⟩ | ⟨l, h1, h2, h3, _⟩
    · exact GridData.mem_weightX.2 (Or.inl (GridData.mem_tops.2 ⟨l, hl, (Prod.ext_iff.1 h).1⟩))
    · exact GridData.mem_weightX.2 (Or.inr (Or.inl h1))
    · exact GridData.mem_weightX.2 (Or.inr (Or.inr (Or.inl ⟨l, by omega, h2, h3⟩)))
  have hs : Odd (grid D τ).s := GlobalTheory.ChiGrid.odd_sLen D
  obtain ⟨z, hz⟩ := GlobalTheory.ChiGrid.inCoset_weightX_zero hs _ hmem
  obtain ⟨u, hu⟩ := GlobalTheory.ChiGrid.even_rankP D i
  have hn' : (n : ℝ) = (u : ℝ) + u := by
    have : n = u + u := hn.trans hu
    rw [this]; push_cast; ring
  refine ⟨z + 1 - u, ?_⟩
  rw [hq a, hz, hn']
  push_cast
  ring

end GlobalTheory.Grid
