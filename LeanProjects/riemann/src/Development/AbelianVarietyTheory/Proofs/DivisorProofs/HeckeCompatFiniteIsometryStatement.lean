import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
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
theorem _root_.GlobalTheory.T.hecke_compat_finite_isometry : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (β' : GL (Fin V'.rank) (EAf D)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N' : ℕ) (Pg : Finset (Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V') (PP : Pl D.host.E), IsFinIso V V' β β' Pg j Φ → IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ((N' : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ∀ k (α : GfC V), IsHeckeAt V PP k α ↔ IsHeckeAt V' PP k (Φ α) := by
  first | exact @GlobalTheory.HeckeTrans.isHeckeAt_iff | exact GlobalTheory.HeckeTrans.isHeckeAt_iff | (intros; apply GlobalTheory.HeckeTrans.isHeckeAt_iff <;> assumption)
