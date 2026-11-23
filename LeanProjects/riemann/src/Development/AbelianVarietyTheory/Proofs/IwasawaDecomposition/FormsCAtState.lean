import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.RatSide

theorem formsC_of_full {D : D7} (S : RatDat D.ntw)
    (h : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm ∧ (S.A j).MKFull) : FormsC S := by
  intro j h1 h2
  obtain ⟨hK, hM⟩ := h j h1 h2
  refine ⟨hK, ?_, ?_⟩
  · obtain ⟨n, b, -, -, hsp, -, -⟩ := hK
    show FiniteDimensional S.Ks ↥(S.A j).WK
    rw [← hsp]
    exact FiniteDimensional.span_of_finite S.Ks (Set.finite_range b)
  · obtain ⟨T, hT⟩ := hM.1
    refine ⟨T, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [← hT]; exact Submodule.subset_span hx
    · exact ⟨hx.fst, by rw [hT]; exact hx⟩
    · rw [← hM.2] at hx
      refine Submodule.span_le.2 (fun y hy => ?_) hx
      have hy' : y ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j)) := by rw [hT]; exact hy
      exact Submodule.span_le_restrictScalars (𝓞 S.Ks) S.Ks _ hy'

end GlobalTheory.HeightCounting.RatSide

namespace GlobalTheory.HeightCounting.RatSide

theorem formsC_at_state : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w =>
    ∀ (P : Pre2 K w) (x : St P), LA hL x → FormsC (SOf x) := by
  intro hL
  refine StepW.of_all fun K _ _ _ w _ _ _ P x _ => formsC_of_full _ fun j _ _ =>
    ⟨x.m.z.geo.fw.ks (idxOf _ j), GlobalTheory.GoodLat.Obj.mkFull_of_tie x.m.z.geo.fw (idxOf _ j)⟩

end GlobalTheory.HeightCounting.RatSide
