import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaTransformInj

theorem linear_injective : ∀ (D : D7) {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d), Mo.IsGood ψ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → Y.J.det ≠ 0 → Z.J.det ≠ 0 → G.det ≠ 0 →
    ∃ T : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ),
      (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ) ∧
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = 0 → Φ = 0 := by
  intro D m k d Y Z Mo ψ G e _ hψ _ _ hG
  have hGG : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), Matrix.map_one _ (map_zero _) (map_one _)]
  have hsur : ∀ u, ∃ x, GlobalTheory.TripleRead.ptO G e x = u := by
    intro u
    refine ⟨(HMul.hMul (u.submatrix id e.symm)ᵀ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G) : Matrix (Fin d) (Fin m) (AE D)), ?_⟩
    simp only [GlobalTheory.TripleRead.ptO, Matrix.mul_assoc, hGG, Matrix.mul_one, Matrix.transpose_transpose]
    ext i j
    simp
  have hadd : ∀ (u : Matrix (Fin m) (Fin k) (AE D)) (Φ Ψ : (Fin m × Fin k → AF D.host.F) → ℂ),
      Mo.co.rho ψ u (Φ + Ψ) = Mo.co.rho ψ u Φ + Mo.co.rho ψ u Ψ := by
    intro u Φ Ψ
    funext y
    simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]
  have hsmul : ∀ (u : Matrix (Fin m) (Fin k) (AE D)) (c : ℂ) (Φ : (Fin m × Fin k → AF D.host.F) → ℂ),
      Mo.co.rho ψ u (c • Φ) = c • Mo.co.rho ψ u Φ := by
    intro u c Φ
    funext y
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
    ring
  let f : GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ) :=
    { toFun := fun Φ => GlobalTheory.TripleRead.thO Mo ψ G e Φ.1
      map_add' := fun Φ Ψ => by
        funext x
        simp only [GlobalTheory.TripleRead.thO, Submodule.coe_add, Pi.add_apply, hadd]
        exact GlobalTheory.WeilM.thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA Mo ψ hψ _ _ Φ.2)
          (GlobalTheory.HeisSchA.rho_mem_schA Mo ψ hψ _ _ Ψ.2)
      map_smul' := fun c Φ => by
        funext x
        simp only [GlobalTheory.TripleRead.thO, Submodule.coe_smul, Pi.smul_apply, hsmul, smul_eq_mul, RingHom.id_apply]
        exact GlobalTheory.WeilM.thetaSum_smul _ c _ }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend f
  have hTf : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ := by
    intro Φ hΦ
    exact LinearMap.congr_fun hT ⟨Φ, hΦ⟩
  refine ⟨T, hTf, fun Φ hΦ h0 => ?_⟩
  rw [hTf Φ hΦ] at h0
  refine GlobalTheory.ThetaInj.theta_inj Mo ψ hψ (fun u => u) Φ 0 (fun _ => 0) ⟨hΦ, fun u => ?_⟩
    ⟨Submodule.zero_mem _, fun u => ?_⟩
  · obtain ⟨x, rfl⟩ := hsur u
    exact congrFun h0 x
  · simp [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

end GlobalTheory.ThetaTransformInj
