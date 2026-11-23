import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSource
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLine
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineVectorsInvertibleOnThetaFunctionsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.LinkProd

variable {D : D7}

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem heisO_at_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  simp [heisO, symplOH_zero_left]

theorem lnk_point {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (l : Lnk L ζ L' ζ')
    {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (n : GA D W) :
    l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d L (yZero L ρ ζ) n ∧
      cenT d L (yZero L ρ ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  constructor
  · have h : (rat l.τ : Mx D L.rank L'.rank) ⬝ zEll L' ρ ζ' = yZero L ρ ζ := by
      have h0 : ratV (-ζ) = -ratV ζ := funext fun i => map_neg (incA D) _
      rw [yZero, zEll, zEll, Matrix.mul_vecMulVec, ← ratV_mulVec, l.map, h0, Matrix.neg_vecMulVec]
    rw [GlobalTheory.Unf.LinkPoint.ptT_eq, Lnk.κ, ptS, d.extX_apply, ← h]
    simp only [Matrix.mul_assoc]
  · have hN : D.host.xi0 * star D.host.xi0 ≠ 0 :=
      mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (star_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
    rw [GlobalTheory.Unf.LinkPoint.cenT_eq, GlobalTheory.Unf.LinkPoint.neg_cenS_eq, yZero, adj_neg, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg, GlobalTheory.Unf.LinkPoint.gram_zEll, GlobalTheory.Unf.LinkPoint.gram_zEll,
      smul_smul, ← map_mul, l.norm, inv_mul_cancel_left₀ hN]

theorem perAll_box_eq_per : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Lnk B.L B.ζ L' ζ') (χA χz χ' : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omz : Om J.W₀ L'), s.χV = χA * χz → IsWeilDatumO ψ B.A J.W₀ χA s.χW oma → IsWeilDatumO ψ J.W₀ L' χ' χz omz → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) Ξ₁ Ξ₂, IsThetaFunO ψ B.A J.W₀ Ξ₁ → IsThetaFunO ψ B.L J.W₀ Ξ₂ → J.perAll ψ B s.om₀ φ G (B.o.boxS J.W₀ Ξ₁ Ξ₂) = J.per ψ ζ' omz (liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁) G (fun w => star (Ξ₂ (l.κ J.W₀ w))) := by
  intro D ψ ρ B J s L' ζ' hL' l χA χz χ' oma omz hχ hoa hoz φ G Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have hψ := hoa.std
  have hrk : B.L.rank = L'.rank := B.line.1.trans hL'.1.symm
  have hres : ResEta D χz B.L.rank := by rw [hrk]; exact hoz.resT
  obtain ⟨omL, hoL⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D B.L J.W₀ ψ χz s.χW hψ hoz.hecT hoa.hecT hres hoa.resT
  obtain ⟨hg, -⟩ := GlobalTheory.T.linkedLineVectors_invertible_on_theta_functions D ψ hψ B.L L' J.W₀ B.ζ ζ' B.line hL' l
  have hg' : l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram := by
    rw [Int.cast_one, one_mul]; exact hg
  have hcl := (GlobalTheory.ConjLine.conj_line D ψ B.L L' J.W₀ l.τ hrk hg' χz s.χW χ' omL omz hoL hoz Ξ₂ hΞ₂).2
  have hTS := GlobalTheory.TensorSrc.tensorSource D ψ hψ B.V₀ B.A B.L B.o J.W₀
  have hw0 : IsWeilDatumO ψ B.V₀ J.W₀ (χA * χz) s.χW s.om₀ := hχ ▸ s.weil₀
  have hbt : IsThetaFunO ψ B.V₀ J.W₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) := hTS.box_theta Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have key : ∀ n ∈ flagN J.d, ∀ h, ∫ h₀ in B.vA.𝓕, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) h₀ n h ∂B.vA.μ =
      liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁ h * star (thetaJS ψ J.d ζ' omz (fun w => star (Ξ₂ (l.κ J.W₀ w))) n h) := by
    intro n _ h
    obtain ⟨hp, hc⟩ := lnk_point l J.d n
    have e1 : ∀ h₀, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) h₀ n h =
        oma (h₀, h) Ξ₁ 0 * φ h₀ * (ψ (cenT J.d B.L (yZero B.L ρ B.ζ) n) * omL (1, h) Ξ₂ (ptT J.d B.L (yZero B.L ρ B.ζ) n)) := by
      intro h₀
      rw [GlobalTheory.Unf.fjKer_eq_om_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ _ _ s.om₀ s.weil₀ _ hbt,
        hTS.om_box χA χz s.χW s.om₀ oma omL hw0 hoa hoL h₀ 1 h Ξ₁ Ξ₂ hΞ₁ hΞ₂]
      simp only [OrthDec.boxS, AddEquiv.apply_symm_apply]
      ring
    simp_rw [e1]
    rw [integral_mul_const, liftT_apply]
    congr 1
    have hcl' : omz (h, 1) (fun w => star (Ξ₂ (l.κ J.W₀ w))) = fun w => star (omL (1, h) Ξ₂ (l.κ J.W₀ w)) := hcl h
    rw [thetaJS, jacS, hcl', Pi.smul_apply, smul_eq_mul, heisO_at_zero, star_mul', star_star, star_psi hψ, hp, hc]
  unfold JacL.perAll JacL.per fjAll fjSrc
  congr 1
  funext h
  congr 1
  funext n
  rw [fjAllFun, fjSrcFun, key n.1 n.2 h]
  ring

end GlobalTheory.LinkProd

end
