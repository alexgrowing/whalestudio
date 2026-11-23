import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowInnerVertexVacuaScaledLocalProduct
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovY
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRowInnerVertex_vacua_scaled_localProduct : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ShapeAt ch → ∀ (t : T) (Φ : ch.G.Datum) (j : ℕ) (hj : j + 1 + 1 < D.R.m), ∀ k ∈ latGrp ch.G (j + 1), ∃ c₁ c₂ : ℂ, ch.W.om (.mu t D.R.m j) (1, k) (ch.rm.vT D.R.m j) = c₁ • ch.rm.vT D.R.m j ∧ ch.W.om (.mu t D.R.m (j + 1)) (k, 1) (ch.rm.vT D.R.m (j + 1)) = c₂ • ch.rm.vT D.R.m (j + 1) ∧ ∀ x y, c₁ * c₂ * ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x (GlobalTheory.RowKFix.movY ch.G j hj k y)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y) := by
  first | exact @GlobalTheory.RowKFix.local_prod_col | exact GlobalTheory.RowKFix.local_prod_col | (intros; apply GlobalTheory.RowKFix.local_prod_col <;> assumption)
