import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem satPol_val (q a : ℕ) (b : ℂˣ) (m : ℤ) :
    ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (b : ℂ)) ^ (-m) =
      ((q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ)) ^ m * ((b : ℂ)⁻¹) ^ m := by
  have hx : ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ))⁻¹ = (q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q), Complex.ofReal_natCast, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [zpow_neg, ← inv_zpow, mul_inv, ← hx, mul_zpow]

theorem UpperTheory.Gal.TP.Sub.satPol_holds :
    SatPol := by
  intro E Ω _ _ _ _ _ A w h a B g
  rw [GlobalTheory.SatChar.charPol_satWD]
  unfold unrPol algSat
  simp only [bind, pure, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  rw [satPol_val]
