import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicCharacterFactorPrimitiveOnIdempotentSum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCharacter_factor_primitive_on_idempotentSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → (∀ Z : AE D, e * Z = Z → (toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ Z' : AE D, e * Z' = Z' → toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z'))) = 1)) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ Z : AE D, e * Z = Z → ∀ h : toEAf D (incA D (ϖ : D.host.E) * Z) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = ∏ PP ∈ Q.attach, ψP PP.1 (resS D.host.F PP.1 ⟨toEAf D (incA D (ϖ : D.host.E) * Z), h⟩) := by
  first | exact @GlobalTheory.IdemCharLift.factor_prim | exact GlobalTheory.IdemCharLift.factor_prim | (intros; apply GlobalTheory.IdemCharLift.factor_prim <;> assumption)
