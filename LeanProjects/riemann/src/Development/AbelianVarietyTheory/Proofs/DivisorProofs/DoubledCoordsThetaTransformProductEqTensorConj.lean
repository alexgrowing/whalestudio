import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOperatorMemAdelicSchwartzStdChar

namespace DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.DblTheta

section Gen

variable {R : Type} [CommRing R] [Invertible (2 : R)]

theorem schr_boxFun_elim (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ] [Fintype κ'] (x₁ y₁ : κ → R) (x₂ y₂ : κ' → R)
    (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ (Sum.elim x₁ x₂, Sum.elim y₁ y₂) (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
      GlobalTheory.WeilM.boxFun (GlobalTheory.WeilM.schr ψ (x₁, y₁) φ₁) (GlobalTheory.WeilM.schr ψ (x₂, y₂) φ₂) := by
  funext z
  have e₁ : (z + Sum.elim x₁ x₂) ∘ Sum.inl = z ∘ Sum.inl + x₁ := rfl
  have e₂ : (z + Sum.elim x₁ x₂) ∘ Sum.inr = z ∘ Sum.inr + x₂ := rfl
  have e₃ : z ⬝ᵥ Sum.elim y₁ y₂ + ⅟(2 : R) * (Sum.elim x₁ x₂ ⬝ᵥ Sum.elim y₁ y₂) =
      ((z ∘ Sum.inl) ⬝ᵥ y₁ + ⅟(2 : R) * (x₁ ⬝ᵥ y₁)) + ((z ∘ Sum.inr) ⬝ᵥ y₂ + ⅟(2 : R) * (x₂ ⬝ᵥ y₂)) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun, e₁, e₂, e₃]
  rw [AddChar.map_add_eq_mul]
  ring

end Gen

section Sums

variable (F : Type) [Field F] [NumberField F]

theorem thetaSum_boxFun {κ κ' : Type} [Fintype κ] [Fintype κ'] {A : (κ → AdeleRing (𝓞 F) F) → ℂ}
    {B : (κ' → AdeleRing (𝓞 F) F) → ℂ} (hA : A ∈ GlobalTheory.WeilM.schA F κ) (hB : B ∈ GlobalTheory.WeilM.schA F κ') :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.boxFun A B) = GlobalTheory.WeilM.thetaSum F A * GlobalTheory.WeilM.thetaSum F B := by
  unfold GlobalTheory.WeilM.thetaSum
  rw [tsum_mul_tsum_of_summable_norm (GlobalTheory.WeilM.summable_norm_of_mem_schA F hA)
    (GlobalTheory.WeilM.summable_norm_of_mem_schA F hB), ← (Equiv.sumArrowEquivProdArrow κ κ' F).tsum_eq]
  exact tsum_congr fun ξ => rfl

theorem thetaSum_schr_neg [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hu : ∀ a, ‖ψ a‖ = 1) {κ : Type} [Fintype κ] (x y : κ → AdeleRing (𝓞 F) F)
    (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, -y) φ) =
      starRingEnd ℂ (GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u))))) := by
  have hc : ∀ t, starRingEnd ℂ (ψ t) = ψ (-t) := fun t => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hu t)]
  have key : ∀ ξ : κ → F,
      GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        starRingEnd ℂ (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u)))
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) := by
    intro ξ
    have ha : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        -(fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by
      funext i; simp
    rw [ha]
    generalize (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = a
    simp only [GlobalTheory.WeilM.schr, map_mul, Complex.conj_conj, hc]
    have h1 : -a + x = -(a + -x) := by abel
    have h2 : -a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (x ⬝ᵥ -y) =
        -(a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (-x ⬝ᵥ -y)) := by
      simp only [neg_dotProduct, dotProduct_neg]
      ring
    rw [h1, h2]
  unfold GlobalTheory.WeilM.thetaSum
  calc _ = ∑' ξ : κ → F, GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) :=
        ((Equiv.neg (κ → F)).tsum_eq
          (fun ξ : κ → F => GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))).symm
    _ = _ := tsum_congr key
    _ = _ := (Complex.conj_tsum _).symm

end Sums

theorem thetaTr_ddr_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro D ψ hψ S T JA JB ξ κ _ co φ₁ h₁ φ₂ h₂
  funext x
  have he : (GlobalTheory.DblSchr.ddr co).e x =
      (Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).1 (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1,
        Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).2 (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2)) := rfl
  have hn : co.e (-GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x) =
      (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1, -(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2) := by
    rw [map_neg]; rfl
  have hs : ∀ (w : (κ → AF D.host.F) × (κ → AF D.host.F)) (φ : (κ → AF D.host.F) → ℂ),
      φ ∈ GlobalTheory.WeilM.schA D.host.F κ → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun w φ hφ => GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar D ψ hψ κ w φ hφ
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta]
  rw [he, hn, schr_boxFun_elim, thetaSum_boxFun _ (hs _ _ h₁) (hs _ _ h₂),
    thetaSum_schr_neg _ ψ hψ.1.2.1]

end GlobalTheory.CompanionTheory.DblTheta

end

end

end DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | exact DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | (intros; apply DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun <;> assumption)

end
