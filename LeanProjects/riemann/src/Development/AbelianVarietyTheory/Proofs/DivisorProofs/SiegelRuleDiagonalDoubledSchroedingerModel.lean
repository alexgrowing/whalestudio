import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalHeisenbergInvariantFormEqSmulDiagonalIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralEqNonzeroMulDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralSiegelRuleDoubledWeilStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegel

open MeasureTheory

theorem dblD_diagCols {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Invertible (2 : R)] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E} {JA : Matrix α α E}
    {JB : Matrix β β E} {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ)
    (z : Matrix α β E) :
    (GlobalTheory.DblSchr.dblD c d).e (z * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β E)ᵀ) =
      (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) := by
  have h : z * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β E)ᵀ = Matrix.fromCols z z := by
    simp [GlobalTheory.WeilM.diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols]
  rw [h]
  exact GlobalTheory.DblSchr.isDblCoord_dblD c d z z

end GlobalTheory.DiagSiegel

theorem GlobalTheory.DiagSiegel.siegelRule_ddr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          GlobalTheory.WeilM.SiegelRule (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ (incM D.host.F JA)
            (GlobalTheory.WeilM.dbl (incM D.host.F JB)) (GlobalTheory.DblSchr.dblD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) χT
            (GlobalTheory.WeilM.diagCols (Fin S.rank)) (GlobalTheory.DblSchr.omdOf omd₀) := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hξ κ _ co hco ωd hωd omd₀ htr
  intro l hl hinv p t hpt φ hφ
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) S T
  letI mκ : MeasurableSpace (κ → AF D.host.F) := borel _
  haveI : BorelSpace (κ → AF D.host.F) := ⟨rfl⟩
  let μ : MeasureTheory.Measure (κ → AF D.host.F) := MeasureTheory.Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hinv' : ∀ x y : κ → AF D.host.F, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
      l (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ := by
    intro x y Φ hΦ
    have h1 := hinv (co.e.symm (x, y)) Φ hΦ
    rw [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.DiagSiegel.dblD_diagCols, LinearEquiv.apply_symm_apply] at h1
    exact h1
  obtain ⟨c, hc⟩ := GlobalTheory.T.diagonalHeisenbergInvariant_form_eq_smul_diagonalIntegral D ψ hψ κ l hl hinv' μ hμ
  obtain ⟨c₂, hc₂0, hc₂⟩ := GlobalTheory.T.diagonalThetaIntegral_eq_nonzero_mul_diagonal D ψ hψ S T JA JB ξ hJA hξ κ co hco ν 𝓕 hν μ hμ
  obtain ⟨hmem, hrule⟩ := GlobalTheory.T.diagonalThetaIntegral_siegelRule_doubledWeil D ψ hψ S T JA JB ξ hJA hξ κ co hco ν 𝓕 hν χS χT hS hT rS rT ωd hωd omd₀ htr p t hpt φ hφ
  rw [hc₂ _ hmem, hc₂ _ hφ] at hrule
  have e := mul_left_cancel₀ hc₂0 (hrule.trans (mul_left_comm _ _ _))
  show l (GlobalTheory.DblSchr.omdOf omd₀ p φ) = _
  refine (hc _ hmem).trans ?_
  refine (congrArg (c * ·) e).trans ?_
  refine (mul_left_comm _ _ _).trans ?_
  have h3 := hc _ hφ
  rw [h3]
  rfl

end
