import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadWMemGoodW
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeDataAtState

theorem exists_hkDat_at_state : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x →
    ∀ (i : Fin (Dof x).R.m) (k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ k → k ≤ (Dof x).R.r → IsSplitPl (Dof x).host Pl →
      Pl ∉ SbD (Dof x) → ∃ α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ i k Pl _ hk hs hP => ?_
  obtain ⟨α, Rr, h, -⟩ := GlobalTheory.TwInputs.Eig.exists_hkDat (R := x.m.z.R) x.m.z.F x.m.z.pins.char.base.lev (subset_refl _)
    (GlobalTheory.TwInputs.Eig.low_SbD (Dof x)) i hs hP hk
  exact ⟨α, Rr, h⟩

end GlobalTheory.HeckeDataAtState
