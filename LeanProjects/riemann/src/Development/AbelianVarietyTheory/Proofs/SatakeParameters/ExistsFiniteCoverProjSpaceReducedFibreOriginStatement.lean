import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteCoverProjSpaceReducedFibreOrigin
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential
theorem _root_.GlobalTheory.T.exists_finiteCover_projSpace_reduced_fibre_origin : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ X.functionField], inst = ffAlg p → IsProjOver p → ∀ S : Finset (CxPts p (RingHom.id ℂ)), ∃ (F : IntermediateField ℂ X.functionField) (x : Fin (d + 1) → F) (U : Fin (d + 1) → X.Opens), IsFinCover ℂ X.functionField x ∧ IsAffCover p U (rB ℂ X.functionField x) ∧ IsReduced ((rB ℂ X.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ X.functionField x j⟩ : rB ℂ X.functionField x {0})))) ∧ ∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (U 0) ∧ ∀ j : Fin d, ∀ (hg : genericPoint X ∈ U 0) (f : Sec p (U 0)), (X.presheaf.germ (U 0) (genericPoint X) hg).hom f = algebraMap F X.functionField (x j.succ / x 0) → CxPts.ev p (RingHom.id ℂ) (U 0) f y = 0 := by
  first | exact @GlobalTheory.PD.FibRed.exists_finCover_fibre_reduced | exact GlobalTheory.PD.FibRed.exists_finCover_fibre_reduced | exact @GlobalTheory.PD.FibRed.quotEquiv_of_germ | exact GlobalTheory.PD.FibRed.quotEquiv_of_germ
