import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSiegelHeisenbergInvariantFormUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagonalSiegelParabolicRuleStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblTargetSiegel

theorem mul_diagCols_transpose {X : Type} [CommRing X] {m n : ℕ} (z : Matrix (Fin m) (Fin n) X) :
    z * ((GlobalTheory.WeilM.diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) X).submatrix finSumFinEquiv.symm id)ᵀ =
      GlobalTheory.DiagSiegel.diagMat z := by
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.mul_apply,
    Matrix.transpose_apply]
  rcases j with j | j <;> simp [GlobalTheory.WeilM.diagCols, Matrix.one_apply]

end GlobalTheory.DblTargetSiegel

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.DblTargetSiegel.siegelRule_dblTarget : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS : (AE D)ˣ →* Circle), IsHeckeChar D χS → ResEta D χS S.rank →
      ∀ (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ωd omp →
            GlobalTheory.WeilM.SiegelRule (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ (incM D.host.F JB)
              (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) χS
              ((GlobalTheory.WeilM.diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank) (AE D)).submatrix
                finSumFinEquiv.symm id)
              (omp.comp (MonoidHom.inl _ _)) := by
  intro D ψ hψ S T χS hS rS JB ξ hξ κ _ co hco ωd hωd omp htr
  intro l hl hinv p t hpt φ hφ
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) T S
  have hinv' : ∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
          (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ := by
    intro z Φ hΦ
    have h1 := hinv z Φ hΦ
    rwa [GlobalTheory.DblTargetSiegel.mul_diagCols_transpose] at h1
  obtain ⟨c, hc⟩ := GlobalTheory.T.diagonalSiegel_heisenbergInvariant_form_unique D ψ hψ S T JB ξ hξ κ co hco ν 𝓕 hν l hl hinv'
  obtain ⟨hmem, hrule⟩ := GlobalTheory.T.thetaDiagonal_siegelParabolic_rule D ψ hψ S T JB ξ hξ κ co hco ν 𝓕 hν χS hS rS ωd hωd omp htr p t hpt φ hφ
  show l (omp (p, 1) φ) = _
  rw [hc _ hmem, hrule, hc _ hφ]
  simp only [GlobalTheory.DiagSiegel.ruleFac]
  ring

end
