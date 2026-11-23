import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleLevelPosOddBadPrimesPrimeToLevel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleLevel_pos_odd_badPrimes_prime_to_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι), 0 < levC I.sel (I.tup a) (I.cst a) u ∧ Odd (levC I.sel (I.tup a) (I.cst a) u) ∧ (∀ Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) := by
  first | exact @GlobalTheory.TupLevel.levC_pos_odd_and_off | exact GlobalTheory.TupLevel.levC_pos_odd_and_off | (intros; apply GlobalTheory.TupLevel.levC_pos_odd_and_off <;> assumption)
