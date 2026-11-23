import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepDualPairing
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_rep_dual_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ), (∀ u v, star (B u v) = B v u) → (∀ v, 0 ≤ (B v v).re) → (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v) → ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ f : S →ₗ[ℂ] (UA E n → ℂ), f ≠ 0 → (∀ v, IsAutFormU (f v)) → (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → ∃ π, IsAutRepU π ∧ ∃ f' : S →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ v, f' v ∈ π) ∧ (∀ (x : infU E n) v, f' (ρ x v) = RU E n x (f' v)) ∧ ∀ (κ : Type) (R : Finset κ) (s : κ → UA E n) (c : ℂ), (∀ i ∈ R, s i ∈ finU E n) → (∀ v, ∑ i ∈ R, RU E n (s i) (f v) = c • f v) → ∀ v, ∑ i ∈ R, RU E n (s i) (f' v) = c • f' v := by
  first | exact @GlobalTheory.FrameAut.VecProj.exists_autRep_projection | exact GlobalTheory.FrameAut.VecProj.exists_autRep_projection | (intros; apply GlobalTheory.FrameAut.VecProj.exists_autRep_projection <;> assumption)
