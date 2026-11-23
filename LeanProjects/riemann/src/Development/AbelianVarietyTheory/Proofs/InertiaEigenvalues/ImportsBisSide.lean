import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleThreePrime
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSumOfInputs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParOfTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistInvOfCharLawsMultOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstCharacterTrivialWildInertiaTypePrimeStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AdmTame

open Polynomial

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → GlobalTheory.RowTie.LabTame D.nd D.naut → AdmissibleThreePrime.LabelDegreeHypotheses D := by
  intro D h0 hG hA hL
  obtain ⟨hLP, hAut, -⟩ := h0
  have hW : GlobalTheory.TypeLeaf.WildOne D := hL
  have hGal : GlobalTheory.TypeLeaf.GalAway D := by
    intro i a ha π hc hr
    obtain ⟨ρ, hρc, -, hρw, -⟩ := (hG i).1 a ha π hc hr
    exact ⟨ρ, hρc, fun w hw => (hρw w hw).1⟩
  have hF : GlobalTheory.TypeLeaf.FrobDense D := by
    intro T hT
    rw [dense_iff_closure_eq]
    exact hA.2.2.1 T hT
  have hCL : GlobalTheory.TypeLeaf.CharLaws D := by
    intro w a χ χ' hχ hχ'
    obtain ⟨-, -, -, h4, h5, -⟩ := hLP w a a χ χ' 0 hχ hχ'
    exact ⟨h4, h5⟩
  have hM : GlobalTheory.TypeLeaf.MultOne D := by
    intro a π π' ha h
    have hp := hA.1 [⟨a, π, 1⟩] [⟨a, π', 1⟩] (by simp [ha]) (by simp [ha])
      (Filter.Eventually.of_forall fun w => by simp [isoLoc, spehLoc, h w])
    rw [List.singleton_perm_singleton] at hp
    simp only [Formalism.BasicNotions.Part.mk.injEq, heq_eq_eq, true_and] at hp
    exact hp.1
  have hT : GlobalTheory.TypeLeaf.TwistInv D := GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne D hCL hM
  have hz : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ,
      ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) := by
    intro τ z hz
    obtain ⟨m, hm⟩ := D.R.t_odd
    obtain ⟨h1, h2⟩ := hAut.2.1 τ
    rw [h2] at hz
    rcases h1 with h1 | h1 <;> rw [h1] at hz <;> simp at hz <;> subst hz
    · refine ⟨-(m : ℤ) - 1, ?_⟩
      rw [hm]; push_cast; ring
    · refine ⟨-(m : ℤ), ?_⟩
      rw [hm]; push_cast; ring
  have hP : GlobalTheory.TypeLeaf.PointPar D := GlobalTheory.TypeLeaf.pointPar_of_twist D hT hAut.1.1 hz
  exact GlobalTheory.TypeLeaf.tameSum_of_inputs D hW (GlobalTheory.T.firstCharacter_trivial_wildInertia_typePrime D) hGal hF hP

end GlobalTheory.AdmTame
