import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowMovedVacuumEqUnitMulChosen
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_moved_vacuum_eq_unit_mul_chosen : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ i : ℕ, i < D.R.m → ∃ κ : ℂˣ, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ch.S.N.u (Pair.chi i D.R.m : Pair T).small).1 (ch.S.N.u (Pair.chi i D.R.m : Pair T).big).1) (ch.S.Z.vac (.chi i D.R.m)) = (κ : ℂ) • ch.rm.vX i D.R.m := by
  first | exact @GlobalTheory.RowVac.moved_vac_eq | exact GlobalTheory.RowVac.moved_vac_eq | (intros; apply GlobalTheory.RowVac.moved_vac_eq <;> assumption)
