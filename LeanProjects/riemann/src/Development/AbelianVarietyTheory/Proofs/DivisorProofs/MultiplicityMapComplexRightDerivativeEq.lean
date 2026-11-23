import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDerivStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.MultDer

theorem rderC_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (y : M.sm τ), (y : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z (v τ : M.H τ) → RderC θ V τ Z (T v) = T (Function.update v τ y) := by
  intro D θ V _ S M J χ T hT v τ Z y hy
  obtain ⟨hc, hU, -⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
  have hu := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  obtain ⟨hsp, hsm⟩ := GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ)
    (GlobalTheory.SmoothAutCheck.gramAt_herm V τ) hu.ne_zero hU
  have hv : SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) := hsp _ (v τ).2
  obtain ⟨h1, -, -, h4⟩ := hsm _ hv
  funext g
  obtain ⟨ℓ, hℓ, hval⟩ := hT.cont τ v g
  have key : ∀ X ∈ lieAt V τ, Rder θ V τ X (T v) g = ℓ (dRep (M.rep τ) X (v τ : M.H τ)) := by
    intro X hX
    have e : (fun t : ℝ => T v (g * oneP θ V τ X t)) =
        fun t : ℝ => ℓ (M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)) := by
      funext t
      have hm := GlobalTheory.SmoothAutCheck.exp_mem_UH hu hX t
      let w : M.sm τ := ⟨M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ), Submodule.subset_span (h1 _ hm)⟩
      have h := congrFun (hT.equiv τ _ hm v w rfl) g
      exact ((hval w).trans h).symm
    unfold Rder
    rw [e]
    exact (h4 ℓ hℓ X hX).deriv
  obtain ⟨p1, p2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have h := hval y
  rw [hy] at h
  refine Eq.trans ?_ h
  unfold RderC dRepC
  rw [Pi.add_apply, Pi.smul_apply, key _ p1, key _ p2, map_add, map_smul]
  rfl

end GlobalTheory.MultDer
