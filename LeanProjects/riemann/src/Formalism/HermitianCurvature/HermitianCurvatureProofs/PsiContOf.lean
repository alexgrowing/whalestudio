import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem psi_cont_of {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous (fun g : B.Mat k r => psi k r z c g) := by
  have hl : Continuous fun g : B.Mat k r => ell k r z g := Formalism.FourierDecayAlt.P.B7.continuous_ell (k := k) (r := r) z
  unfold psi
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul hl))))

theorem krI_aesm {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (y₀ : B.Mat k (p + ρ))
    (hy₀ : y₀ ∈ B.GV k (p + ρ)) (hD : U.DjU k p ρ y₀ ≠ 0) :
    AEStronglyMeasurable (LeftFubiniLemmas.KrI B0 H y₀) (B0.μW'.prod B0.μN) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite B0.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite B0.haarN
  set S := {ξ : Mt k (p + ρ) × Mt k (p + ρ) | Formalism.FourierDecayAlt.P.PBG.InR B0 ξ} with hS
  have hcG := Formalism.FourierDecayAlt.P.unitary_group_closed k (p + ρ)
  have hcW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k (p + ρ) B0.z'
  have hmem : ∀ ξ ∈ S, y₀ * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    intro ξ hξ
    refine ⟨hcG.mul_mem _ (hcG.mul_mem _ hy₀ _ hξ.2.1) _ hξ.1.1, ?_⟩
    show U.DjU k p ρ (y₀ * Matrix.of ξ.2 * Matrix.of ξ.1) ≠ 0
    rw [LeftFubiniLemmas.djU_mul_UW B0.z' _ _ hξ.1, LeftFubiniLemmas.djU_mul_N _ _ hξ.2]
    exact hD
  have hof1 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.1 : B.Mat k (p + ρ))) :=
    continuous_fst
  have hof2 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.2 : B.Mat k (p + ρ))) :=
    continuous_snd
  have hc1 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => y₀ * Matrix.of ξ.2 * Matrix.of ξ.1) :=
    (continuous_const.matrix_mul hof2).matrix_mul hof1
  have hH : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => H (y₀ * Matrix.of ξ.2 * Matrix.of ξ.1)) S :=
    hHc.comp hc1.continuousOn hmem
  have hinv : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.1 : B.Mat k (p + ρ))⁻¹) S :=
    Formalism.FourierDecayAlt.P.PBG.inv_cont_GV.comp hof1.continuousOn (fun ξ hξ => hξ.1.1)
  have hπ : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => B0.π' (Matrix.of ξ.1 : B.Mat k (p + ρ))⁻¹) S :=
    B0.π'_cont.comp hinv (fun ξ hξ => hcW.inv_mem _ hξ.1)
  have hψ : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => star (psi k (p + ρ) B0.z' cStd (Matrix.of ξ.2))) :=
    continuous_star.comp ((psi_cont_of B0.z' cStd).comp hof2)
  have hK : ContinuousOn (LeftFubiniLemmas.KrI B0 H y₀) S := hψ.continuousOn.smul (hH.clm_comp hπ)
  have hm := hK.aestronglyMeasurable (μ := B0.μW'.prod B0.μN) (Formalism.FourierDecayAlt.P.PBG.isClosed_InR B0).measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (s := S) (Formalism.FourierDecayAlt.P.PBG.ae_inR B0)] at hm

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
