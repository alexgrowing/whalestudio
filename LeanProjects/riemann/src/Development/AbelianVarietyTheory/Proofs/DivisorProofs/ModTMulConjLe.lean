import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section
namespace GlobalTheory.BotPairSmallTw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem modT_ne_bot (G : GridData L sc) (t : T) : modT G t ≠ ⊥ := by
  unfold modT
  exact mul_ne_zero (condE_ne_bot G.pl) (Finset.prod_ne_zero_iff.2 fun w _ => w.ne_bot)

theorem absNorm_modT (G : GridData L sc) (t : T) : Ideal.absNorm (modT G t) = levQ G.pl * Qn G t := by
  rw [modT, map_mul, map_prod, GlobalTheory.ModulusNorm.absNorm_condE, Qn]

theorem hatId_mono {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : hatId D I ≤ hatId D J :=
  AddSubgroup.closure_mono fun _ ⟨b, hb, s, hs, e⟩ => ⟨b, h hb, s, hs, e⟩

theorem modT_mul_conj_le (G : GridData L sc) (t : T) :
    modT G t * D.host.conj • modT G t ≤ condE G.pl * D.host.conj • condE G.pl := by
  have h : modT G t ≤ condE G.pl := by
    show condE G.pl * _ ≤ _
    exact Ideal.mul_le_inf.trans inf_le_left
  exact Ideal.mul_mono h (Ideal.map_mono h)

end GlobalTheory.BotPairSmallTw

end
