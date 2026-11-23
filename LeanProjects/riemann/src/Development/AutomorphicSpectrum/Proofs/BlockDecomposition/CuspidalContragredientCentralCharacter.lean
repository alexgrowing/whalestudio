import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformiser
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.ContraCusp

theorem contra_facts : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ),
    (contra σ.ρ).IsIrreducible ∧ IsCuspidal (contra σ.ρ) ∧
    ∃ (z : GL (Fin (m + 1)) k) (ϖ : k) (ω : ℂ), (z : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ϖ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ∧
      ValuativeRel.valuation k ϖ < 1 ∧ ϖ ≠ 0 ∧ ω ≠ 0 ∧ (∀ a, σ.ρ z a = ω • a) ∧ ∀ l, contra σ.ρ z l = ω⁻¹ • l := by
  intro k _ _ _ _ m σ hc
  have hadm : IsAdmissible σ.ρ :=
    PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k (m + 1) _ σ.ρ σ.smooth σ.irr
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k (m + 1)
  refine ⟨GlobalTheory.ContraRefl.contra_isIrreducible hG hadm σ.irr,
    GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k (m + 1) _ _
      (GlobalTheory.CompanionTheory.DualCusp.isSupercuspidal_contra hG hadm
        (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k (m + 1) _ _ hc)), ?_⟩
  obtain ⟨ϖ, -, hϖ0, hϖ, -⟩ := GlobalTheory.CompanionTheory.LocalField.exists_uniformiser k
  obtain ⟨χ, -, hχ⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar σ.smooth σ.irr
  let t : kˣ := Units.mk0 ϖ hϖ0
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) t, ϖ, (χ t : ℂ), ?_, hϖ, hϖ0, (χ t).ne_zero,
    fun a => hχ t a, fun l => ?_⟩
  · ext i j
    simp [Matrix.GeneralLinearGroup.scalar, t, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  · refine Subtype.ext (LinearMap.ext fun v => ?_)
    have h1 : (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) t)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) t⁻¹ := (map_inv _ t).symm
    have h2 : ((χ t⁻¹ : ℂˣ) : ℂ) = ((χ t : ℂˣ) : ℂ)⁻¹ := by
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [contra_apply, h1, hχ t⁻¹ v, map_smul, h2]
    rfl

end GlobalTheory.CompanionTheory.ContraCusp
