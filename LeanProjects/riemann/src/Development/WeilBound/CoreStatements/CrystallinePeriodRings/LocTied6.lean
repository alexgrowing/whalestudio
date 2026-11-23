import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

namespace Formalism.BasicNotions

open Loc
open scoped Formalism.Per6

structure LocTied6 (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) where

  eB : P.R.B ≃+* Per6.Bcris l

  eD : P.R.BdR ≃+* Per6.BdR l

  zB : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] P.R.B (z : ℚ_[l])) = Per6.zB l z

  zD : ∀ z : ℤ_[l], eD (algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) = Per6.zD l z

  om : ∀ x : Om l, ∃ y : Per6.BdRp l, eD (algebraMap (Om l) P.R.BdR x) = algebraMap (Per6.BdRp l) (Per6.BdR l) y ∧
    Per6.θD l y = ((x : Om l) : ℂ_[l])

  actB : ∀ (g : GQ l) (b : P.R.B), eB (P.actQ g b) = Per6.σB g (eB b)

  actD : ∀ (g : GQ l) (b : P.R.BdR), eD (P.actQdR g b) = Per6.σD g (eD b)

  frob : ∀ b : P.R.B, eB (P.φB b) = Per6.φB l (eB b)

  incl : Per6.IsCrisDR l ((eD.toRingHom.comp (P.ιB : P.R.B →+* P.R.BdR)).comp eB.symm.toRingHom)

  fil : ∀ (K : FinExt l) (a : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil a ↔ eD x ∈ Per6.FilD l a

  t : ∃ y : Per6.BdRp l, Per6.IsLog l AI.ε y ∧ eD (P.ιB P.tB) = algebraMap (Per6.BdRp l) (Per6.BdR l) y

  ιA : ∀ a : Ainf l, eB (AI.ιA a) = Per6.aB l a

end Formalism.BasicNotions
