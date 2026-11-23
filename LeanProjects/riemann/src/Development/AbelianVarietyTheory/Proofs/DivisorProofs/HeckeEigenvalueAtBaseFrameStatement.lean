import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEigenvalueAtBaseFrame
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_eigenvalue_at_base_frame : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (PP : Pl D.host.E) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (c : ℕ → ℂ) (T : MMap M), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ P', P' ∈ L.Pg ∨ P' ∈ L.Q → P' ≠ PP ∧ ¬ IsConjPl P' PP) → Bridge.SplitOff PP ∅ → T ∈ Mult θ M (levG V β L : Set (GA D V)) (fun _ => 1) → ipM M μ 𝓕 T T ≠ 0 → (∀ k ≤ V.rank, ∀ α R, IsHeckeAt V PP k α → Bridge.IsDC (levG V β L) α⁻¹ R → heckeOn M R T = c k • T) → c V.rank ≠ 0 ∧ ∀ k ≤ V.rank, star (c k) * c V.rank = c (V.rank - k) := by
  first | exact @GlobalTheory.HeckeUnitary.star_eigenvalue_mul | exact GlobalTheory.HeckeUnitary.star_eigenvalue_mul | (intros; apply GlobalTheory.HeckeUnitary.star_eigenvalue_mul <;> assumption)
