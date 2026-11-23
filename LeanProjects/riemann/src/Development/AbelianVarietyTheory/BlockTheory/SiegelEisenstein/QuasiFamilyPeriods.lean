import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.QuasiFamilyPeriods

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
  {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}

def conjTr (l : Link B L' ζ') (S : HSp D) (f : WO B.L S → ℂ) : WO S L' → ℂ := fun w => star (f (l.κ S w))

def JacobiConj (ψ : AddChar (AF D.host.F) ℂ) (J : JacLev D ρ) (l : Link B L' ζ') : Prop :=
  ∀ n ∈ flagN J.d, ∀ f : WO B.L J.W₀ → ℂ,
    conjTr l J.W₀ (jacT ψ J.d B.L (yZero B.L ρ B.ζ) n f) = jacS ψ J.d L' (zEll L' ρ ζ') n (conjTr l J.W₀ f)

structure IsQuasiFam (ψ : AddChar (AF D.host.F) ℂ) (S L : HSp D) (Y : GA D S → WO S L → ℂ) : Prop where
  cont : Continuous fun p : GA D S × WO S L => Y p.1 p.2
  quasi : ∀ h γ w, Y h (ratW L S γ + w) = ψ (-(symplOH S L (ratW L S γ) w)) * Y h w
  left : ∀ γ ∈ GQ S, ∀ h w, Y (γ * h) w = Y h (w ⬝ mt S γ)

theorem isQuasiFam_of_isThetaFam {S L : HSp D} {Y : GA D S → WO S L → ℂ} (hY : IsThetaFam ψ S L Y) : IsQuasiFam ψ S L Y :=
  ⟨hY.cont, fun h => (hY.theta h).quasi, hY.left⟩

structure PeriodsAgree (s : StepBF ψ B J) (l : Link B L' ζ') (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ)
    (G' : GA D J.W → ℂ) : Prop where

  handInt : ∀ (h : GA D J.W₀) (w : WO J.W₀ L'), IntegrableOn
    (fun h₀ => φ h₀ * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) B.vA.𝓕 B.vA.μ

  kerInt : ∀ n ∈ flagN J.d, ∀ h : GA D J.W₀,
    IntegrableOn (fun h₀ => φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ Ξ h₀ n h) B.vA.𝓕 B.vA.μ

  ker_eq : ∀ n ∈ flagN J.d, ∀ h : GA D J.W₀,
    ∫ h₀ in B.vA.𝓕, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ Ξ h₀ n h ∂B.vA.μ = J.ker ψ ζ' (handBF s l φ Ξ) n h

  absProd : AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ G' Ξ)

  absCons : AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fjSrcKerFun ψ J.d (J.ker ψ ζ' (handBF s l φ Ξ)) G')

  per_eq : J.perAll ψ B s.om₀ φ G' Ξ = J.per ψ ζ' (handBF s l φ Ξ) G'

def PeriodLink (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ l : Link B L' ζ',
    JacobiConj ψ J l ∧
    ∀ φ : GA D B.A → ℂ, IsContAut B.A φ → ∀ Ξ : WO B.V₀ J.W₀ → ℂ, IsThetaFunO ψ B.V₀ J.W₀ Ξ →
      IsThetaFam ψ J.W₀ L' (handBF s l φ Ξ) ∧
      ∀ G' : GA D J.W → ℂ, RapidDec J.W G' → PeriodsAgree s l φ Ξ G'

def PeriodLinkQuasi (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ l : Link B L' ζ',
    JacobiConj ψ J l ∧
    ∀ φ : GA D B.A → ℂ, IsContAut B.A φ → ∀ Ξ : WO B.V₀ J.W₀ → ℂ, IsThetaFunO ψ B.V₀ J.W₀ Ξ →
      IsQuasiFam ψ J.W₀ L' (handBF s l φ Ξ) ∧
      ∀ G' : GA D J.W → ℂ, RapidDec J.W G' → PeriodsAgree s l φ Ξ G'

theorem PeriodLink.quasi (H : PeriodLink D) : PeriodLinkQuasi D := fun ψ ρ B J s L' ζ' hL l =>
  ⟨(H ψ ρ B J s L' ζ' hL l).1, fun φ hφ Ξ hΞ =>
    ⟨isQuasiFam_of_isThetaFam ((H ψ ρ B J s L' ζ' hL l).2 φ hφ Ξ hΞ).1, ((H ψ ρ B J s L' ζ' hL l).2 φ hφ Ξ hΞ).2⟩⟩

def LinkClass (D : D7) : Prop :=
  ∀ (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ₁ : Fin L'.rank → D.host.E), IsLineVec L' ζ₁ →
    ((∃ a : D.host.E, a ≠ 0 ∧ Nonempty (Link B L' (a • ζ₁))) ↔
      ∃ t : D.host.E, t ≠ 0 ∧ star ζ₁ ⬝ᵥ L'.gram *ᵥ ζ₁ = (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * (t * star t))

example (B : BesLev D ρ) (h0 : D.host.xi0 ≠ 0) : Nonempty (Link B B.L (D.host.xi0⁻¹ • B.ζ)) := by
  refine ⟨⟨(-D.host.xi0) • 1, ?_, ?_⟩⟩
  · rw [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, neg_mul, mul_inv_cancel₀ h0, neg_smul, one_smul]
  · have h1 : star D.host.xi0 ≠ 0 := star_ne_zero.2 h0
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, star_inv₀]
    field_simp

example (l : Link B L' ζ') (f : WO B.L J.W₀ → ℂ) :
    conjTr l J.W₀ (jacT ψ J.d B.L (yZero B.L ρ B.ζ) 1 f) = jacS ψ J.d L' (zEll L' ρ ζ') 1 (conjTr l J.W₀ f) := by
  rw [jacT_one, jacS_one]; rfl

end GlobalTheory.IndefiniteRowSideFullHecke.QuasiFamilyPeriods

end
