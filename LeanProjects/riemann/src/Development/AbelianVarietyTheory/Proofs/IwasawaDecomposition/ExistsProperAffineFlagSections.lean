import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetDivZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperFlagOverAffineStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDetDivisorTrivialStableStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagSectionsStableStatement

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.FlagAmple

theorem exists_plk_nhds : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (z : gen s.T.Z), ∃ (V : (gen s.T.Z).Opens) (f : ((Φ.C k).π ⁻¹ᵁ V).toScheme ⟶ Sp Γ(gen s.T.Z, V)), z ∈ V ∧ IsAffineOpen V ∧ IsProper f ∧ (∀ τ : D.host.E →+* ℂ, GlobalTheory.CechPic.pull ((Φ.C k).π ⁻¹ᵁ V).ι (toPic (GlobalTheory.FlagAmple.detDiv (Φ.C k) τ (S.Dw.mult τ))) = 0) ∧ ∃ (M : GlobalTheory.FlagAmple.Step S.Dw → ℕ) (t : ∀ x : GlobalTheory.FlagAmple.Step S.Dw, Fin (M x + 1) → (((Φ.C k).Y.lb (-GlobalTheory.FlagAmple.detDiv (Φ.C k) x.1 (x.2.1 : ℕ))).pull ((Φ.C k).π ⁻¹ᵁ V).ι).Sec) (ht : ∀ x, ⨆ m, nonzeroLocus (t x m) = ⊤), ∀ (K : Type) [Field K] [IsAlgClosed K] (a a' : Sp K ⟶ ((Φ.C k).π ⁻¹ᵁ V).toScheme), a ≫ f = a' ≫ f → (∀ x, a ≫ GlobalTheory.ProjSpace.toProj f (t x) (ht x) = a' ≫ GlobalTheory.ProjSpace.toProj f (t x) (ht x)) → a = a' := by
  intro D A N j S κ s Φ k z
  obtain ⟨V, hV, φ, g, hz, hstr, hst⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame _ _ _ _ _ _ _ _ s.T.Z z
  have h1 := GlobalTheory.T.flag_det_divisor_trivial_stable D A N j S κ s Φ k V hV φ g hstr hst
  have hP := GlobalTheory.T.isProper_flag_over_affine D A N j S κ s Φ k V hV
  have h23 := GlobalTheory.T.exists_flag_sections_stable D A N j S κ s Φ k V hV φ g hstr hst
  refine ⟨V, ((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom, hz, hV, ?_, ?_, ?_⟩
  · exact hP
  · exact h1
  · exact h23

end GlobalTheory.FlagAmple
