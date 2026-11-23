import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotDict

open GlobalTheory.ChainFr GlobalTheory.SquareComm

variable {D : D7}

theorem gramAt_eq_one {V : HSp D} (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold gramAt
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

def stdFr (V : HSp D) (h : V.gram = 1) : Fr V where
  ε _ _ := true
  fr _ := 1
  fr_unit _ := isUnit_one
  fr_gram τ := by
    rw [gramAt_eq_one h τ]
    simp [Formalism.REAL.Jm]

theorem cart_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (stdFr V h).cart τ = 1 := by
  simp [Fr.cart, stdFr, Formalism.REAL.Jm]

theorem onb_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (stdFr V h).onb τ = 1 := by
  simp [Fr.onb, stdFr]

theorem cart_frSgn_true_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (frSgn true (stdFr V h)).cart τ = -1 := by
  simp only [Fr.cart, frSgn, stdFr, Formalism.REAL.Jm]
  ext a b
  by_cases hab : a = b
  · subst hab; simp
  · simp [Matrix.one_apply, hab]

theorem cart_frSgn_false_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (frSgn false (stdFr V h)).cart τ = 1 := by
  simp [Fr.cart, frSgn, stdFr, Formalism.REAL.Jm]

theorem hasSignature_of_gram_eq_one {V : HSp D} (h : V.gram = 1) (τ : D.what₂.Tau) :
    Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 := by
  refine ⟨(Equiv.sumEmpty (Fin V.rank) (Fin 0)).symm, 1, ?_⟩
  rw [gramAt_eq_one h τ]
  ext (a | a) (b | b)
  · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
  · exact b.elim0
  · exact a.elim0
  · exact a.elim0

end GlobalTheory.BotDict

end
