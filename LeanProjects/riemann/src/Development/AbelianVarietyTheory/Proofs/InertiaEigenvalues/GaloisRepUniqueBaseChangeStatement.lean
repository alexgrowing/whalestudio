import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_rep_unique_base_change : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ → IsSSRep ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, mapRep (iotaOQ D.nd D.naut i) (r x) g = Pm⁻¹ * ρ g * Pm := by
  first | exact @GlobalTheory.BaseChangeConj.rep_conj_of_baseChange | exact GlobalTheory.BaseChangeConj.rep_conj_of_baseChange | (intros; apply GlobalTheory.BaseChangeConj.rep_conj_of_baseChange <;> assumption)
