import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepTwist
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_rep_twist : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ (π : D.naut.CG a) (e : ℤ), D.naut.csd π → (∀ τ, (D.naut.infG π τ).Nodup ∧ ∀ z ∈ D.naut.infG π τ, ∃ k : ℤ, z + (e : ℂ) / 2 = (k : ℂ)) → ∃ ρ : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i)), (SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((e : ℝ) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = (D.naut.infG π ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (e : ℂ) / 2))) := by
  first | exact @GlobalTheory.HalfTwist.exists_galRep_halfTwist | exact GlobalTheory.HalfTwist.exists_galRep_halfTwist | (intros; apply GlobalTheory.HalfTwist.exists_galRep_halfTwist <;> assumption)
