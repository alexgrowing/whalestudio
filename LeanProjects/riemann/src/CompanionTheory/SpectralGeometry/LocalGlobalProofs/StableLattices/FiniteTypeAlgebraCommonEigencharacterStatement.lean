import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteTypeAlgebraCommonEigencharacter
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_type_algebra_common_eigencharacter : ∀ (R : Type) [CommRing R] [Algebra ℂ R] [Algebra.FiniteType ℂ R] (W : Type) [AddCommGroup W] [Module ℂ W] [Module R W] [IsScalarTower ℂ R W] (t : W), t ≠ 0 → ∃ φ : R →ₐ[ℂ] ℂ, ∀ (r : R) (c : ℂ), r • t = c • t → φ r = c := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.exists_character_of_smul_ne_zero | exact GlobalTheory.CompanionTheory.RgCOBlock.exists_character_of_smul_ne_zero | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.exists_character_of_smul_ne_zero <;> assumption)
