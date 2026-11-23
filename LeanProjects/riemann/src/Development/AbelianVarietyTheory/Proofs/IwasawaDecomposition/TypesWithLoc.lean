import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.HeightCounting.Fin

theorem types_withLoc : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ T w P x => ∀ (l : LC hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), GlobalTheory.CoefDuty.Built l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ {o : P.q.Over} (m : Moved o), m.Copy → m.Coh → ∀ (s : Side0 o) (r : ReadPk m s), r.Pin → TypesTrue (withLoc L).ntypes m.z.R.C.P m.z.R.C.W := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ o m _ _ s r _
  rw [m.z.lev.C, w.C_eq]
  have hg : TypesTrue x.o.N.ntypes f.P f.W := x.fits.grp
  exact ⟨fun k v => hg.pl k v, fun k => hg.teich k, fun k v j => hg.chi k v j, fun k p => hg.ser k p⟩

end GlobalTheory.HeightCounting.Fin

end
