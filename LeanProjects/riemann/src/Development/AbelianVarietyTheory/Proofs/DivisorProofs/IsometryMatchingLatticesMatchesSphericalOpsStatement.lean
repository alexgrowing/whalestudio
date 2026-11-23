import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_matching_lattices_matches_spherical_ops : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (β' : GL (Fin V'.rank) (Lev.EAf D)) (Pg : Finset (Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (Lev.EAf D)) (Φ : GfC V ≃ₜ* GfC V') (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N N' : ℕ), IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → GlobalTheory.CuspMult.IsFinIso V V' β β' Pg j Φ → ∀ (P : Pl D.host.E), ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((N' : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (d : List ℤ) (B : Finset (GfC V)), GlobalTheory.Hk3.SphOp V P d (B.map ⟨Subtype.val, Subtype.val_injective⟩) ↔ GlobalTheory.Hk3.SphOp V' P d ((B.map Φ.toEquiv.toEmbedding).map ⟨Subtype.val, Subtype.val_injective⟩) := by
  first | exact @GlobalTheory.SphTrans.sphOp_iff | exact GlobalTheory.SphTrans.sphOp_iff | (intros; apply GlobalTheory.SphTrans.sphOp_iff <;> assumption)
