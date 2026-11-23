import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisOfUnramifiedMatch
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_galois_of_unramified_match : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ → IsSSRep ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := by
  first | exact @GlobalTheory.NRows.isHeckeGaloisQ_of_wdOf_baseChange | exact GlobalTheory.NRows.isHeckeGaloisQ_of_wdOf_baseChange | (intros; apply GlobalTheory.NRows.isHeckeGaloisQ_of_wdOf_baseChange <;> assumption)
