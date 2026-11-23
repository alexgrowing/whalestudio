import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousOperatorLinear
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_homogeneous_operator_linear : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (ψ : AddChar K ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ (n m : ℕ) (A : (Matrix (Fin n) (Fin m) K → ℂ) → Matrix (Fin n) (Fin m) K → ℂ),
    (∀ f ∈ SB (Matrix (Fin n) (Fin m) K), ∀ f' ∈ SB (Matrix (Fin n) (Fin m) K), A (f + f') = A f + A f') →
    (∀ (c : ℂ), ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A (c • f) = c • A f) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => f (Y + Z)) = fun Y => A f (Y + Z)) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * f Y) = fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * A f Y) →
    ∃ c : ℂ, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A f = c • f := by
  first | exact @GlobalTheory.SchurLin.schur_linear_model | exact GlobalTheory.SchurLin.schur_linear_model | (intros; apply GlobalTheory.SchurLin.schur_linear_model <;> assumption)
