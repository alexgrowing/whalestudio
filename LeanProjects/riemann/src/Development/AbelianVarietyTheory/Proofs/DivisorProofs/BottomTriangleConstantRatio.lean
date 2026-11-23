import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTrianglePolynomialSurjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleIntegralsNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConstRatio

theorem bottomTri_factor (hPr : GlobalTheory.FunPr.Hypotheses₂) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hL : LNe) :
    GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW), IsBottomTri W i j X → ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam := by
  obtain ⟨c, h⟩ := GlobalTheory.T.bottom_triangle_polynomial_surjection hPr.minguezThetaGL hPr hK hM
  obtain ⟨c', h'⟩ := GlobalTheory.T.bottom_triangle_integrals_ne_zero hPr hK hM hL
  refine ⟨max c c', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  refine ⟨max C0 C1, max x0 x1, fun C hC D large₂ a b r T Lc μ hLc G W hW i j A A' WW X hX => ?_⟩
  obtain ⟨Pi, p, p', J, hs, hJ, hlam, hI'⟩ :=
    h C (le_of_max_le_left hC) D large₂ a (le_of_max_le_left b) r T Lc μ hLc G W hW i j A A' WW X hX
  have hnv := h' C (le_of_max_le_right hC) D large₂ a (le_of_max_le_right b) r T Lc μ hLc G W i j A A' WW X hX
  obtain ⟨P', g', hg'⟩ := (hnv μ).2
  have hP' : p' P' ≠ 0 := fun h0 => hg' (by rw [hI' μ P', h0]; simp)
  choose lam hlam using hlam
  have key : ∀ t, lam t ≠ 0 ∧ Function.Injective (J t) := fun t => by
    obtain ⟨P, g, hPg⟩ := (hnv t).1
    rw [hlam t P] at hPg
    refine ⟨fun h0 => hPg (by simp [h0]), (hJ t).resolve_left fun h0 => hPg (by simp [h0])⟩
  refine ⟨lam, fun t => (key t).1, Pi, p, p', J, hs, fun t => (key t).2, fun t P g => (hX.integrable t).1 P g,
    fun t P => hlam t P, fun t P' _ => hI' t P', P', hP', fun t g => (hX.integrable t).2 P' g⟩

end GlobalTheory.ConstRatio
