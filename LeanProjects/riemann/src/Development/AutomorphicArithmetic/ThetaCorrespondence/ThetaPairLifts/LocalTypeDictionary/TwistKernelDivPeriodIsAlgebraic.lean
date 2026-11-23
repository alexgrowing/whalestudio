import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicLiftedKernel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFieldMinorJetDescription
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicLiftedKernelStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
namespace GlobalTheory.BotDictAlg
theorem kernel_div_period_isAlgebraic_alt : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ n : D.what₂.Tau → ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ U : GlobalTheory.NormSum.Tup D A'.rank WW.rank n,
      IsAlgebraic ℚ (X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D U) h x / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX n
  obtain ⟨Ω, hΩ, H⟩ := _root_.GlobalTheory.T.bottom_field_minor_jet_description hP hI hL hX n
  refine ⟨Ω, hΩ, fun t x hx h hh U => ?_⟩
  obtain ⟨cc, δ, t0, e0, k, c, s, hc, ht0, he0, hca, hs, hU⟩ := H t x hx h hh
  obtain ⟨Q, hQ, heq⟩ := hU U
  rw [heq, mul_div_cancel_left₀ _ hΩ]
  refine applyAt0_isAlgebraic hQ ?_
  exact ((hI D).alg cc δ hc t0 ht0 A'.rank WW.rank (StandardLatticesGL3.stdL D A'.rank) (StandardLatticesGL3.stdL D WW.rank)
    (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) (even_bot hX) e0 he0.2.2.2.1).2.2.1 k c s
    (fun l => (mem_algebraicClosure_iff).2 (hca l)) hs
end GlobalTheory.BotDictAlg
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_kernel_div_period_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ n : D.what₂.Tau → ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ U : GlobalTheory.NormSum.Tup D A'.rank WW.rank n,
      IsAlgebraic ℚ (X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D U) h x / Ω) := by
  first | exact @_root_.GlobalTheory.BotDictAlg.kernel_div_period_isAlgebraic_alt | exact _root_.GlobalTheory.BotDictAlg.kernel_div_period_isAlgebraic_alt | (intros; apply _root_.GlobalTheory.BotDictAlg.kernel_div_period_isAlgebraic_alt <;> assumption)
end
