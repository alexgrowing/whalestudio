import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainRationalMatricesTower
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.TowerFD

theorem thetaFunOF_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
      ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ ψ f → ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ hψ f hf
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  have hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :
      Set (WOF F E nS nT)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  have hmem : ratWF (Matrix.of fun i j => c (w i j)) + w ∈
      (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) : Set (WOF F E nS nT)) :=
    fun i _ j _ => hc (w i j)
  have h := hC _ hmem
  have hq := hf.quasi (Matrix.of fun i j => c (w i j)) w
  have h2 : ‖f w‖ = ‖f (ratWF (Matrix.of fun i j => c (w i j)) + w)‖ := by
    rw [hq, norm_mul, hψ.2.1, one_mul]
  exact h2.trans_le h

end GlobalTheory.TowerFD
