import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruenceStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.LevelVac
variable {D : D7}
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem level_vacuum_vector_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC A, ∀ k' ∈ GfC WW, GlobalTheory.Member.FinCong A N k →
      GlobalTheory.Member.FinCong WW N k' → ∃ ζ : ℂ, IsAlgebraic ℚ ζ ∧ X.ω t (k, k') X.vac = ζ • X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t
  have hI := hX.is
  obtain ⟨N, hN, h⟩ := exists_level_fix (S := GlobalTheory.Grid.neg A) (T := WW) (om := (X.ω t).toSgn true) (hI.weil t)
    (sS := fun τ => -X.rA.s τ) (fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1)
    (fun τ => (hI.rigW.2.2 τ).1) (GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1) hI.rigW.1 hI.rigA.2.1 hI.rigW.2.1 hI.isVac
  refine ⟨N, hN, fun k hk k' hk' hc hc' => ⟨1, isAlgebraic_one, ?_⟩⟩
  rw [one_smul]
  exact h ((GlobalTheory.Grid.ofSgn true A).symm k) hk k' hk' hc hc'
end GlobalTheory.LevelVac
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_vector_at_level_mem_fockAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC A, ∀ k' ∈ GfC WW, GlobalTheory.Member.FinCong A N k →
      GlobalTheory.Member.FinCong WW N k' → ∃ ζ : ℂ, IsAlgebraic ℚ ζ ∧ X.ω t (k, k') X.vac = ζ • X.vac := by
  first | exact @_root_.GlobalTheory.LevelVac.level_vacuum_vector_algebraic | exact _root_.GlobalTheory.LevelVac.level_vacuum_vector_algebraic | (intros; apply _root_.GlobalTheory.LevelVac.level_vacuum_vector_algebraic <;> assumption)
end
