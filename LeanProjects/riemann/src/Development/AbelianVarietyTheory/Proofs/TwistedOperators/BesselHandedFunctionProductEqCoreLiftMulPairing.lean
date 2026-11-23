import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumPreservesThetaFundamentalDomainPairing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.HandProd

theorem handP_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χA χz : (AE D)ˣ →* Circle) (omb : Om J.W₀ B.A) (omz : Om J.W₀ B.L), s.χW = χA * χz → IsWeilDatumO ψ J.W₀ B.A s.χV χA omb → IsWeilDatumO ψ J.W₀ B.L s.χV χz omz → ∀ (φ : GA D J.W₀ → ℂ) Ξ₁ Φ' Φ₀, IsThetaFunO ψ J.W₀ B.A Ξ₁ → IsThetaFunO ψ J.W₀ B.L Φ' → IsThetaFunO ψ J.W₀ B.L Φ₀ → handP s vL omz φ Φ₀ (B.o.boxT J.W₀ Ξ₁ Φ') = thPair vL.μ vL.𝓕 Φ' Φ₀ • liftT omb J.v0.μ J.v0.𝓕 φ Ξ₁ := by
  intro D ψ σ J B s vL χA χz omb omz hχ hb hz φ Ξ₁ Φ' Φ₀ h1 h' h0
  have hW₀ : IsWeilDatumO ψ J.W₀ B.V₀ s.χV (χA * χz) s.om₀ := hχ ▸ s.weil₀
  have tt := GlobalTheory.TensorTargetRule.tensorTarget D ψ hb.std B.V₀ B.A B.L B.o J.W₀
  funext h₁
  have hpt : ∀ h₀, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (B.o.boxT J.W₀ Ξ₁ Φ')) (omz (h₀, 1) Φ₀) 0 =
      omb (h₀, h₁) Ξ₁ 0 * thPair vL.μ vL.𝓕 Φ' Φ₀ := by
    intro h₀
    rw [tt.om_box s.χV χA χz s.om₀ omb omz hW₀ hb hz h₀ h₁ 1 Ξ₁ Φ' h1 h',
      ← GlobalTheory.WeilPairing.thPair_om_eq D ψ J.W₀ B.L s.χV χz omz hz vL (h₀, 1) Φ' Φ₀ h' h0]
    have e : (fun v => B.o.boxT J.W₀ (omb (h₀, h₁) Ξ₁) (omz (h₀, 1) Φ') ((B.o.resT J.W₀).symm (0, v))) =
        fun v => omb (h₀, h₁) Ξ₁ 0 * omz (h₀, 1) Φ' v := by
      funext v
      simp only [OrthDec.boxT, AddEquiv.apply_symm_apply]
    simp only [contractT, e, thPair]
    rw [← integral_const_mul]
    congr 1; funext w
    have ew := congrFun e w
    rw [ew]; ring
  simp only [handP, hpt, Pi.smul_apply, smul_eq_mul, liftT_apply]
  rw [← integral_const_mul]
  congr 1; funext h₀; ring

end GlobalTheory.HandProd

end
