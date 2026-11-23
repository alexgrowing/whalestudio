import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEqOfAutomorphismMapsParahoric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_eq_of_automorphism_maps_parahoric : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s s' s₁ : SplitPlace L) (θ : GAf L n ≃* GAf L n), 0 < r → r < n → s'.v = s.v → s₁.v = s.v → FrameAut θ → (∀ κ, TrivOutside {s.v} κ → NG.ParaRT s₁ r (s₁.loc n κ) → NG.ParaRT s r (s.loc n (θ κ)) ∧ NG.ParaRT s' r (s'.loc n (θ κ))) → s' = s := by
  first | exact @GlobalTheory.ParaOpp.splitPlace_eq_of_para | exact GlobalTheory.ParaOpp.splitPlace_eq_of_para | (intros; apply GlobalTheory.ParaOpp.splitPlace_eq_of_para <;> assumption)
