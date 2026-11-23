import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsStd
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_model_selfDual_lattice : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (S : Sys W (SB (κ → R))), GoodChar ψ O u → IsModel ψ d μ S → ∃ (Γ : AddSubgroup W) (al : W → ℂ) (φ : SB (κ → R)), SelfDual S Γ ∧ IsSemi S al Γ ∧ Law S al Γ φ ∧ Cyclic S φ ∧ φ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.StdLattice.exists_std | exact GlobalTheory.CompanionTheory.StdLattice.exists_std | (intros; apply GlobalTheory.CompanionTheory.StdLattice.exists_std <;> assumption)
