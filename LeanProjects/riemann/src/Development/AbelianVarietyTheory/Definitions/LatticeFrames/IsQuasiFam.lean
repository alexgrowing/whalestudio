import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

structure IsQuasiFam (ψ : AddChar (AF D.host.F) ℂ) (S L : HSp D) (Y : GA D S → WO S L → ℂ) : Prop where
  quasi : ∀ h γ w, Y h (ratW L S γ + w) = ψ (-(symplOH S L (ratW L S γ) w)) * Y h w
  cont : Continuous fun p : GA D S × WO S L => Y p.1 p.2
  left : ∀ γ ∈ GQ S, ∀ h w, Y (γ * h) w = Y h (w ⬝ mt S γ)

def JointCont (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    ∀ f, IsThetaFunO ψ S T f → Continuous fun p : (GA D S × GA D T) × WO S T => om p.1 f p.2

def Descent (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    (∀ (S₀ : HSp D) (ρ : ℕ), HypDec S S₀ ρ → ∃ om₀ : Om S₀ T, IsWeilDatumO ψ S₀ T χS χT om₀) ∧
    ∀ (T₀ : HSp D) (ρ : ℕ), HypDec T T₀ ρ → ∃ om₀ : Om S T₀, IsWeilDatumO ψ S T₀ χS χT om₀

def FlatLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ)
    (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ)
    (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ (y : Mx D V₀.rank σ)
    (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ →
      (∀ w, Integrable (flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y Ψ w) vU.ν) ∧
      IsThetaFunO ψ V₀ W₀ (flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y Ψ)

def UnfBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (φ : GA D B.A → ℂ)
    (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ →
      IsQuotIntL1 J.μR s.vW.μ (fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (flatBF s (s.om (1, h) Φ)))
        (B.per ψ φ (s.lift G Φ))

def EvalBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (φ : GA D B.A → ℂ)
    (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ →
    ∀ (ν₀ : Measure (radX J.d)) (𝓝₀ : Set (radX J.d)), ν₀.IsHaarMeasure →
      IsFundamentalDomain ((GQ J.W).subgroupOf (radX J.d)) 𝓝₀ ν₀ → ν₀ 𝓝₀ = 1 →
      IsQuotIntL1 (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) s.vW.μ
        (fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (evalBF s (s.om (1, h) Φ))) (B.per ψ φ (s.lift G Φ))

def UnfFB (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ),
    IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ →
      IsQuotIntL1 B.μR s.vW.μ (fun h => B.per ψ (handFB s vL Y (flatFB s (s.om (1, h) Φ))) (rTrans h G))
        (J.per ψ B.ζ Y (s.lift G Φ))

def HandFBLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ),
    IsQuasiFam ψ J.W₀ B.L Y → IsThetaFunO ψ J.W₀ B.V₀ Ξ → IsContAut B.A (handFB s vL Y Ξ)

def LinkLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (L' : HSp D)
    (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ') (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ),
    IsContAut B.A φ → IsThetaFunO ψ B.V₀ J.W₀ Ξ →
      IsQuasiFam ψ J.W₀ L' (handBF s l φ Ξ) ∧
      ∀ G' : GA D J.W → ℂ, J.perAll ψ B s.om₀ φ G' Ξ = J.per ψ ζ' (handBF s l φ Ξ) G'

def LastLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D) (B : BesLev D 0) (t : Last ψ T B) (φ : GA D B.A → ℂ)
    (Φ₁ : WO B.V t.J.W → ℂ) (Φ₂ : WO t.J.W T → ℂ) (F : GA D T → ℂ), IsContAut B.A φ → IsContAut T F →
    IsThetaFunO ψ B.V t.J.W Φ₁ → IsThetaFunO ψ t.J.W T Φ₂ →
      B.per ψ φ (t.s.lift (liftS t.om t.vT.μ t.vT.𝓕 F Φ₂) Φ₁) = t.Q φ Φ₁ Φ₂ F

def DoubleStep (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (G : GA D B'.V → ℂ) (g : GA D B.V),
    IsThetaFunO ψ B.V J.W Φ₁ → IsThetaFunO ψ J.W B'.V Φ₂ → IsContAut B.A φ → RapidDec B'.V G →
    RapidDec J.W (s₂.lift G Φ₂) →
      (∀ h₁ h₂, IsContAut B'.A (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂)) ∧
      ∃ f₁ : GA D J.W → ℂ, IsQuotIntL1 J.μR s₁.vW.μ f₁ (B.per ψ φ (rTrans g (s₁.lift (s₂.lift G Φ₂) Φ₁))) ∧
        ∀ h₁, IsQuotIntL1 B'.μR s₂.vW.μ
          (fun h₂ => B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) (rTrans h₂ G)) (f₁ h₁)

def IT (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D) (ρ : ℕ) (B : BesLev D ρ) (c : Chain ψ T ρ B) (Φ : c.Data) (F : GA D T → ℂ)
    (φ : GA D B.A → ℂ) (g : GA D B.V), c.IsTheta Φ → IsContAut T F → IsContAut B.A φ → c.Rapid Φ F →
      c.Iter (c.Q Φ F φ g) (B.per ψ φ (rTrans g (c.down Φ F)))

def contr {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank)
    (Ξ₁ : WO B.V₀ S → ℂ) (Ξ₂ : WO S B'.V₀ → ℂ) (u : WO B.A S) (v : WO S B'.A) : ℂ :=
  ∫ w in vL.𝓕, Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) ∂vL.μ

def ContrLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (χA χA' χz : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L),
    s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz →
    IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' →
    ∀ (φ : GA D B.A → ℂ) (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsContAut B.A φ →
      IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ →
      (∀ v, IsThetaFunO ψ B.A J.W₀ fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) ∧
      (∀ p, IsThetaFunO ψ J.W₀ B'.A fun v => oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) ∧
      ∀ h₂, handFB s₂ vL (handBF s₁ l φ Ξ₁) Ξ₂ h₂ = ∫ h₁ in J.v0.𝓕, (∫ h₀ in B.vA.𝓕, φ h₀ *
        omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) 0 ∂B.vA.μ) ∂J.v0.μ

def SeeLast (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), L.rank = 1 → L''.rank = 1 →
    τᴴ ⬝ (L.gram ⬝ τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram →
    ∀ (χA χz χS χS' χT : (AE D)ˣ →* Circle) (om₁ : Om V₀ S) (oma : Om A S) (omz : Om L S) (omX : Om S X) (omT : Om S T)
      (omz'' : Om S L''), IsWeilDatumO ψ V₀ S (χA * χz) χS om₁ → IsWeilDatumO ψ A S χA χS oma →
      IsWeilDatumO ψ L S χz χS omz → IsWeilDatumO ψ S X χS' (χT * χz⁻¹) omX → IsWeilDatumO ψ S T χS' χT omT →
      IsWeilDatumO ψ S L'' χS' χz⁻¹ omz'' →
      ∀ (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), IsThetaFunO ψ V₀ S Ξ → IsThetaFunO ψ S T Φ₂ →
        (∀ u, IsThetaFunO ψ S L'' fun w => Ξ ((o.resS S).symm
          (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)))) ∧
        ∀ h₀ h h', omT (h, h') Φ₂ 0 * om₁ (o.emb (h₀, 1), h) Ξ 0 =
          oma (h₀, h) (fun u => omX (h, o''.emb (h', 1)) (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm
            (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)))) 0) 0

def hypZero (V : HSp D) : HypDec V V 0 where
  e := 0
  e' := 0
  i₀ := 1
  ee := Subsingleton.elim _ _
  e'e' := Subsingleton.elim _ _
  e'e := Subsingleton.elim _ _
  iso := by simp
  i₀e := Subsingleton.elim _ _
  i₀e' := Subsingleton.elim _ _
  rank_add := by simp

end GlobalTheory.Unf

end
