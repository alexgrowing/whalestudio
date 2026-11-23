import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairPartnerInverseTransposeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformFixedBySmallFiniteHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformAdelicSchwartzRealDirectioStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaTransportCont

theorem thetaTr_om_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ w, Continuous fun p => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) w := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom Φ hΦ w
  choose g h hh hg using fun p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) =>
    GlobalTheory.T.unitaryPair_partner_inverse_transpose D S T JA JB ξ hA hB p.1 p.2
  have hθ : Formalism.IndefR.Datum.IsThetaFunO ψ S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) :=
    ⟨GlobalTheory.T.thetaTransform_rational_translate_quasiInvariant D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ, GlobalTheory.T.thetaTransform_fixed_by_small_finiteHeisenberg D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ,
      GlobalTheory.T.continuous_thetaTransform_adelicSchwartz D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ, GlobalTheory.T.contDiff_thetaTransform_adelicSchwartz_realDirections D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ⟩
  have hhU : ∀ p, matHom T (h p) = p.1.1 := fun p => Units.ext (hh p)
  have hgU : ∀ p, (matHom S (g p))⁻¹.1 = p.2.1.1ᵀ := by
    intro p
    apply Units.inv_eq_of_mul_eq_one_right
    change mt S (g p) * _ = 1
    rw [hg p, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one]
  have hcH' : Continuous fun p => matHom T (h p) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have e : (Units.val ∘ fun p => matHom T (h p)) = fun p => p.1.1.1 := funext fun p => hh p
      rw [e]
      exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
    · have e : (fun p => (matHom T (h p))⁻¹.1) = fun p => (p.1.1)⁻¹.1 := funext fun p => by rw [hhU p]
      rw [e]
      exact Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)
  have hcG' : Continuous fun p => matHom S (g p) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have e : (Units.val ∘ fun p => matHom S (g p)) = fun p => ((p.2.1)⁻¹).1ᵀ := funext fun p => hg p
      rw [e]
      exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
    · have e : (fun p => (matHom S (g p))⁻¹.1) = fun p => p.2.1.1ᵀ := funext hgU
      rw [e]
      exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
  have hcH : Continuous h := continuous_induced_rng.2 hcH'
  have hcG : Continuous g := continuous_induced_rng.2 hcG'
  have heq : ∀ p, GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) w =
      ω (g p, h p) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w := fun p =>
    congrFun (hom p.1 p.2 (g p) (h p) (hh p) (hg p) Φ hΦ).2 w
  exact ((hω.om_cont _ hθ w).comp (hcG.prodMk hcH)).congr fun p => (heq p).symm

end GlobalTheory.ThetaTransportCont

end
