import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSchwartzMemSpanDatumTranslates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSchwartzVanishOffTranslates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCharDetFixHyperplaneEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_schwartz_mem_span_datum_translates_alt : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (n r : ℕ), r ≤ n → ∀ ϖ : O, Irreducible ϖ → ∀ ξ : (IsLocalRing.ResidueField O)ˣ →* ℂˣ, ξ ≠ 1 → ∀ Φ Φ₀ : Matrix (Fin n) (Fin r) K → ℂ, (∀ (z : Matrix (Fin n) (Fin r) O) (u : (IsLocalRing.ResidueField O)ˣ), LowZero r (z.map (IsLocalRing.residue O)) → (u : IsLocalRing.ResidueField O) = (topL r (z.map (IsLocalRing.residue O))).det → Φ₀ (z.map (algebraMap O K)) = ((ξ u : ℂˣ) : ℂ)⁻¹) → (∀ m, Φ₀ m ≠ 0 → ∃ z : Matrix (Fin n) (Fin r) O, m = z.map (algebraMap O K) ∧ LowZero r (z.map (IsLocalRing.residue O)) ∧ IsUnit (topL r (z.map (IsLocalRing.residue O))).det) → (∃ N : ℕ, (∀ m (z : Matrix (Fin n) (Fin r) O), Φ (m + (ϖ ^ N • z).map (algebraMap O K)) = Φ m) ∧ ∀ m, Φ m ≠ 0 → ∃ z : Matrix (Fin n) (Fin r) O, algebraMap O K (ϖ ^ N) • m = z.map (algebraMap O K)) → (∀ h : GL (Fin n) O, LowZero r (h.val.map (IsLocalRing.residue O)) → ∀ m m' : Matrix (Fin n) (Fin r) K, Φ (h.val.map (algebraMap O K) * m) * Φ₀ m' = Φ m * Φ₀ (h.val.map (algebraMap O K) * m')) → Φ ∈ Submodule.span ℂ {Ψ | ∃ γ : GL (Fin r) K, Ψ = fun m => Φ₀ (m * γ.val)} := by
  first | exact @GlobalTheory.parahoric_schwartz_mem_span_datum_translates | exact GlobalTheory.parahoric_schwartz_mem_span_datum_translates | (intros; apply GlobalTheory.parahoric_schwartz_mem_span_datum_translates <;> assumption)
