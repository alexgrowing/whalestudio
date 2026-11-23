import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesCharacterInverse
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_character_inverse : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ _ w _ x => ∀ l : StrictHenselianAcyclic hL x, (∀ g : Gc B w.px, x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U ↔ g ∈ x.m.z.F.P0) ∧
  ∀ i b (g : x.m.z.F.P0) (h : x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U), l.b.ser.ex.ρ.e i b ((Dof x).nexp.psiU i b ⟨_, h⟩ : (FractionRing ((Dof x).ntw.O i))ˣ) = ((Dof x).what₂.embLL (x.m.z.F.ψ0 g : (Dof x).what₂.LLˣ))⁻¹ := by
  first | exact @GlobalTheory.StateLevel.level_char_allSt | exact GlobalTheory.StateLevel.level_char_allSt | (intros; apply GlobalTheory.StateLevel.level_char_allSt <;> assumption)
