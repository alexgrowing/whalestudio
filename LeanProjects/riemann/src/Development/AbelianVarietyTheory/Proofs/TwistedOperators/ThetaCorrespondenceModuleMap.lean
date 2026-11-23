import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScaling
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.CoinvLine

variable {D : D7}

theorem isThetaFunO_of_mem_algF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ)
    (hψ : IsStdChar D ψ (-1)) [Nonempty D.what₂.Tau] {W₁ X : HSp D} (A₁ : Fr W₁) (B : Fr X) {Ψ : WO W₁ X → ℂ}
    (hΨ : Ψ ∈ algF ψ θ false A₁ B) : IsThetaFunO ψ W₁ X Ψ := by
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact (GlobalTheory.LieScalar.ptF_laws hθ hψ (frSgn false A₁) B hf).1 (Classical.arbitrary _) P
  | zero => exact Formalism.IndefR.Fock.CCR.theta_zero ψ W₁ X
  | add x y _ _ hx hy => exact Formalism.IndefR.Fock.CCR.theta_add hx hy
  | smul c x _ hx => exact Formalism.IndefR.Fock.CCR.theta_smul hx c

theorem coinv_kills_line_deriv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsTriple W W₁ X α β → IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank) (hJ : Vs.J = (-1 : D.host.E) • W₁.gram),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Vs, ∀ Ψ ∈ algF ψ θ false A₁ B, ∀ Ψ₁ ∈ algF ψ θ false A₁ B,
    (∀ z, HasDerivAt (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
      (γ (Multiplicative.ofAdd t)), 1) Ψ z) (Ψ₁ z) 0) → p' Ψ₁ = 0 := by
  intro _ D ψ θ W W₁ X A A₁ B α β ωA ωB Pi rf rl p p' hθ _ _ hM Vs hJ γ hγ Ψ hΨ Ψ₁ _ hder
  have hω : IsWeilDatumO ψ W₁ X α (α / β) ωB := hM.weilB
  have hψ : IsStdChar D ψ (-1) := hω.std
  have hc : (-1 : D.host.E) ≠ 0 := neg_ne_zero.2 one_ne_zero
  obtain ⟨g, h1, h2, h3, h4⟩ := GlobalTheory.OmegaDer.exists_line W₁ hc Vs hJ γ hγ
  have hg : ∀ t : ℝ, GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ (γ (Multiplicative.ofAdd t)) = g t :=
    fun t => by rw [← h1 t]; exact (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc hJ).left_inv (g t)
  obtain ⟨Z, hZ⟩ := GlobalTheory.OmegaDer.exists_expInf hθ W₁ g h2 h3 h4

  have hst := fun τ => hM.mapB.stabM.2 τ (Z τ).1 (Z τ).2 Ψ hΨ
  choose Ψ' hΨ' hd using hst
  have hk : ∀ τ, p' (Ψ' τ) = 0 := fun τ => hM.mapB.invl τ (Z τ).1 (Z τ).2 Ψ hΨ (Ψ' τ) (hΨ' τ) (hd τ)
  have hsum : Ψ₁ = ∑ τ, Ψ' τ := by
    funext z
    rw [Finset.sum_apply]
    have e1 : (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
        (γ (Multiplicative.ofAdd t)), 1) Ψ z) = fun t : ℝ => ωB (GlobalTheory.SmoothForms.expInf θ W₁ (t • Z), 1) Ψ z := by
      funext t; rw [hg t, hZ t]
    have hz := hder z
    rw [e1] at hz
    rcases isEmpty_or_nonempty D.what₂.Tau with h0 | h0
    · have e : ∀ t : ℝ, t • Z = Z := fun t => funext fun τ => isEmptyElim τ
      simp only [e] at hz
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact hz.unique (hasDerivAt_const _ _)
    · let 𝒮 : Set (GA D W₁ → ℂ) := {φ | ∃ f z, IsThetaFunO ψ W₁ X f ∧ φ = fun g => ωB (g, 1) f z}
      have hΘ := isThetaFunO_of_mem_algF hθ hψ A₁ B hΨ
      refine hz.unique (GlobalTheory.OmegaDer.der_sum hθ 𝒮 ?_ ?_ ⟨Ψ, z, hΘ, rfl⟩ Z (fun τ => Ψ' τ z) fun τ => hd τ z)
      · rintro _ ⟨f, z, hf, rfl⟩
        exact (hω.om_cont f hf z).comp (continuous_id.prodMk continuous_const)
      · rintro _ ⟨f, z, hf, rfl⟩ τ' Y hY
        obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genS hθ hω τ' Y hY f hf
        refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
        have := h (g, 1) z
        simpa only [MonoidHom.inl_apply, Prod.mk_mul_mk, mul_one] using this
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun τ _ => hk τ

end GlobalTheory.CoinvLine
