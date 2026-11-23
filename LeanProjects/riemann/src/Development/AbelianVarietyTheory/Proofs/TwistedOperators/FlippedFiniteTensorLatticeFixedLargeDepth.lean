import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowLatticesGoodPositionLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovY
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowInnerVertexVacuaScaledLocalProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepPairFixesFlippedTensorSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKFix

theorem key {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A)
    (hS : HidaSetting large₂ R F) (hch : ch.Is) (hsh : ShapeAt ch) : KFix ch := by
  intro t Φ τ hτ J hJ k hk y v
  have hJ' : 1 ≤ J ∧ J + 1 < D.R.m := by
    simp only [idx, List.mem_range'_1] at hJ
    omega
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
  have hj : j + 1 + 1 < D.R.m := hJ'.2
  obtain ⟨c₁, c₂, h1, h2, h3⟩ := GlobalTheory.T.lastRowInnerVertex_vacua_scaled_localProduct ch large₂ F hS hch hsh t Φ j hj k hk
  exact GlobalTheory.T.weilRep_pair_fixes_flippedTensorSum ch large₂ F hS hch t Φ τ hτ j hj k hk c₁ c₂ h1 h2 h3 y v

theorem kfix : Big fun ch => KFix ch := by
  obtain ⟨CF0, h⟩ := GlobalTheory.T.lastRowLatticesGoodPosition_large_depth
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  exact ⟨x₀, fun D large₂ he hx' Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc =>
    key ch large₂ F hS hch (hx D large₂ he hx' Γ Pl0 T A Ks R F hS ch hch hsc)⟩

end GlobalTheory.RowKFix
