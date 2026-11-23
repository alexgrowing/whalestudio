import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DataBoundOfHalfFlip
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DataBoundOfHalfFlipStatement

section
open MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.ArchTens.Unfold
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj GlobalTheory.SumSize Formalism.BasicNotions
section Integral
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
end Integral
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Local
section Grid
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D : D7} (σ : D.what₂.LL →+* ℂ)
variable [MeasurableSpace k] [BorelSpace k]
end Grid
end GlobalTheory.ArchTens.Unfold
namespace GlobalTheory.ArchTens.Unfold
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.RowTest
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
theorem archimedean_tensor_unfold_datum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => FlipAt ch (C / 2) → DatAt ch C := by
  classical
  intro _
  refine ⟨0, fun CF _ => ⟨12, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ hok hF σ Φ β hβ w x y => ?_⟩⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hP : w.1 ∈ ch.G.pl.W0 := by
    rcases Finset.mem_union.1 w.2 with h | h
    · exact h
    · rw [show R.toLevCh.Q A.μ0 = ∅ from GlobalTheory.BaseScalar.Q_base R hL] at h
      exact absurd h (Finset.notMem_empty _)
  have hsz : 0 ≤ (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w :=
    mul_nonneg (by positivity) (placeSz_nonneg ch.G w)
  refine absLe_mono (absLe_datum hL ch.S.toGridChoice hok A.μ0 Φ (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard A.μ0) hP w.2 hβ σ
    (hF σ Φ w) _ _) ?_
  nlinarith
end GlobalTheory.ArchTens.Unfold
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_tensor_factor_unfolding : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => FlipAt ch (C / 2) → DatAt ch C := by
  first | exact @_root_.GlobalTheory.ArchTens.Unfold.archimedean_tensor_unfold_datum | exact _root_.GlobalTheory.ArchTens.Unfold.archimedean_tensor_unfold_datum | (intros; apply _root_.GlobalTheory.ArchTens.Unfold.archimedean_tensor_unfold_datum <;> assumption)
end
