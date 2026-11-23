import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCoeffFinitePlaceOffLevelConstMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientVanishesOffLevelGroupAtBadPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.LocalFactor

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem pureTensor_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : R.ptP i t 1 = R.vP i t := by
  unfold RealDat.ptP pureTensorO pureTensorL
  have : (1 : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp
  rw [this, Module.Basis.constr_basis]
  simp [opPow]

theorem trivAt_one (V : HSp D) (f : AE D) : TrivAt V f 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := rfl
  intro a b
  simp [this]

theorem finMult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Laws R F → R.FullP → ∀ i t, FinMult R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ v f hf γ hγ hγt k hk
  have hmul : ∀ g : GA D (Wc D i),
      R.ωP i t (1, g * k) (R.vP i t) = R.ωP i t (1, g) (R.ωP i t (1, k) (R.vP i t)) := by
    intro g
    have e : ((1 : GA D (Vc D i)), g * k) = (1, g) * (1, k) := by simp
    rw [e, map_mul, Module.End.mul_apply]
  have hone : R.ωP i t (1, 1) = 1 := map_one _
  unfold coef
  by_cases hbad : ∃ P, (P ∈ R.Pg ∨ P ∈ R.Q t) ∧ ∃ e, IsPrimeIdem P e f
  · obtain ⟨P, hP, e, he⟩ := hbad
    by_cases hkl : k ∈ levW R i
    · have hfix : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
        have := GlobalTheory.T.coeffSpaceLevel_fixes_fockVectors D G Pl0 T A Ks R F hL hF i t k hkl 1
        rwa [pureTensor_one] at this
      rw [hmul γ, hfix]
      by_cases hN : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
      · simp [hN]
      · rw [div_self hN, mul_one]
    · have h0 := GlobalTheory.T.coefficient_vanishes_off_level_group_at_bad_prime D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ P hP e f he γ hγ hγt k hk hkl
      have h1 := GlobalTheory.T.coefficient_vanishes_off_level_group_at_bad_prime D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ P hP e f he 1 (one_mem _) (trivAt_one _ f) k hk hkl
      rw [one_mul] at h1
      rw [h0, h1]
      simp
  · have hgood : ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f :=
      fun P hP e f' he hff => hbad ⟨P, hP, e, hff ▸ he⟩
    obtain ⟨c, hc⟩ := GlobalTheory.T.matrixCoeff_finitePlace_offLevel_const_mul D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ v f hf hgood k hk
    have h1 := hc 1 (one_mem _) (trivAt_one _ f)
    rw [one_mul, hone, Module.End.one_apply] at h1
    rw [hc γ hγ hγt, h1]
    by_cases hN : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
    · simp [hN]
    · field_simp

end GlobalTheory.RawLift.LocalFactor

end
