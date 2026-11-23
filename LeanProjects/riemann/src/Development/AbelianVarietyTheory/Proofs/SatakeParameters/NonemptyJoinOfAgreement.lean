import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormAtEachLocationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaModuleOfCanonicalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.JoinExists

theorem main : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Nonempty (Join P) := by
  intro h1 h2 hL D P X hA
  have key : ∀ i : D.nd.Loc, ∃ Y : RowMod D P.rep (D.nd.j i),
      ∀ (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), GlobalTheory.NJoin.IsCanon X j hj Y := by
    intro i
    have hr := D.nd.j_range i
    have hlt : D.nd.j i - 1 < D.R.m := by omega
    obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_canonical_module_successor h1 h2 hL D P X hA ⟨D.nd.j i - 1, hlt⟩ (D.nd.j i) (by simp only; omega)
    refine ⟨Y, fun j hj => ?_⟩
    have hj' : j = ⟨D.nd.j i - 1, hlt⟩ := Fin.ext (by simp only; omega)
    subst hj'
    exact hY
  choose Y hY using key
  exact ⟨{ form := GlobalTheory.T.form_at_each_location hL D P X hA
           rowM := Y
           th := fun i j hj => (GlobalTheory.T.theta_module_of_canonical h1 h2 hL D P X hA i j hj (Y i) (hY i j hj)).some }⟩

end GlobalTheory.JoinExists
