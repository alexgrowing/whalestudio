import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf

variable {D : D7}

def CoCpt (V : HSp D) : Prop := ∃ K : Set (GA D V), IsCompact K ∧ ∀ g, ∃ γ ∈ GQ V, γ * g ∈ K

structure Vol (V : HSp D) where
  μ : Measure (GA D V)
  𝓕 : Set (GA D V)
  haar : μ.IsHaarMeasure
  fund : IsFundamentalDomain (GQ V) 𝓕 μ

structure VolN {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) where
  ν : Measure (flagN d)
  𝓝 : Set (flagN d)
  unit : GlobalTheory.Per.IsUnitN S d.e ν 𝓝

structure VolM (D : D7) (m n : ℕ) where
  μ : Measure (Mx D m n)
  𝓕 : Set (Mx D m n)
  covol : IsCovolOne (ratMx D m n) μ 𝓕

structure VolU (D : D7) (ρ : ℕ) where
  ν : Measure (UX D ρ)
  unit : IsUnitU D ρ ν

def IsContAut (V : HSp D) (φ : GA D V → ℂ) : Prop := (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ Continuous φ

structure IsThetaFam (ψ : AddChar (AF D.host.F) ℂ) (S L : HSp D) (Y : GA D S → WO S L → ℂ) : Prop where
  theta : ∀ h, IsThetaFunO ψ S L (Y h)
  cont : Continuous fun p : GA D S × WO S L => Y p.1 p.2
  left : ∀ γ ∈ GQ S, ∀ h w, Y (γ * h) w = Y h (w ⬝ mt S γ)

structure BesLev (D : D7) (ρ : ℕ) where
  V : HSp D
  V₀ : HSp D
  A : HSp D
  L : HSp D
  d : HypDec V V₀ ρ
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  cpt : CoCpt A
  vA : Vol A
  vN : VolN d

structure JacLev (D : D7) (ρ : ℕ) where
  W : HSp D
  W₀ : HSp D
  d : HypDec W W₀ ρ
  cpt : CoCpt W₀
  v0 : Vol W₀
  vN : VolN d

def BesLev.per {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) : ℂ :=
  besPer ψ 1 B.d B.o B.ζ B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 φ f

def BesLev.μR {ρ : ℕ} (B : BesLev D ρ) : Measure (besGrp B.d B.o) := semiMeas (flagN B.d) (embA B.d B.o) B.vA.μ B.vN.ν

def JacLev.μR {ρ : ℕ} (J : JacLev D ρ) : Measure (jacGrp J.d) := semiMeas (flagN J.d) J.d.emb0 J.v0.μ J.vN.ν

def JacLev.ker {ρ : ℕ} (J : JacLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) {L' : HSp D} (ζ' : Fin L'.rank → D.host.E)
    (Y : GA D J.W₀ → WO J.W₀ L' → ℂ) (n : GA D J.W) (h : GA D J.W₀) : ℂ :=
  star (jacS ψ J.d L' (zEll L' ρ ζ') n (Y h) 0)

def JacLev.per {ρ : ℕ} (J : JacLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) {L' : HSp D} (ζ' : Fin L'.rank → D.host.E)
    (Y : GA D J.W₀ → WO J.W₀ L' → ℂ) (f : GA D J.W → ℂ) : ℂ :=
  fjSrcKer ψ J.d J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (J.ker ψ ζ' Y) f

def JacLev.perAll {ρ : ℕ} (J : JacLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (B : BesLev D σ) (om₀ : Om B.V₀ J.W₀)
    (φ : GA D B.A → ℂ) (G' : GA D J.W → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) : ℂ :=
  fjAll ψ J.d B.o B.ζ om₀ B.vA.μ B.vA.𝓕 J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 φ G' Ξ

structure Step (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) where
  χV : (AE D)ˣ →* Circle
  χW : (AE D)ˣ →* Circle
  om : Om V W
  om₀ : Om V₀ W₀
  weil : IsWeilDatumO ψ V W χV χW om
  weil₀ : IsWeilDatumO ψ V₀ W₀ χV χW om₀
  vW : Vol W
  vS : VolM D W.rank ρ
  vT : VolM D σ V₀.rank
  vU : VolU D ρ

variable {ψ : AddChar (AF D.host.F) ℂ}

def Step.lift {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (s : Step ψ V V₀ W W₀ ρ σ) (G : GA D W → ℂ) (Φ : WO V W → ℂ) : GA D V → ℂ :=
  liftS s.om s.vW.μ s.vW.𝓕 G Φ

abbrev StepBF (ψ : AddChar (AF D.host.F) ℂ) {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) := Step ψ B.V B.V₀ J.W J.W₀ ρ ρ

abbrev StepFB (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) :=
  Step ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ

def flatBF {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) (Ψ : WO B.V J.W → ℂ) : WO B.V₀ J.W₀ → ℂ :=
  flat ψ B.d B.o B.ζ J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν Ψ

def evalBF {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) (Ψ : WO B.V J.W → ℂ) : WO B.V₀ J.W₀ → ℂ :=
  evalZero ψ B.d B.o B.ζ J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ

def flatFB {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) (Ψ : WO J.W B.V → ℂ) : WO J.W₀ B.V₀ → ℂ :=
  flatLast ψ J.d B.d B.o B.ζ s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν Ψ

def pairKer {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank)
    (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ) (h₀ : GA D J.W₀) (h₁ : GA D B.A) : ℂ :=
  contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ) (Y h₀) 0

def handFB {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank)
    (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ) : GA D B.A → ℂ :=
  fun h₁ => ∫ h₀ in J.v0.𝓕, pairKer s vL Y Ξ h₀ h₁ ∂J.v0.μ

structure Link {ρ : ℕ} (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) where
  τ : Matrix (Fin B.L.rank) (Fin L'.rank) D.host.E
  map : τ *ᵥ ζ' = -B.ζ
  norm : star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = D.host.xi0 * star D.host.xi0 * (star ζ' ⬝ᵥ L'.gram *ᵥ ζ')

def Link.κ {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') (S : HSp D)
    (w : WO S L') : WO B.L S :=
  GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L S ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ w)

def handBF {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) : GA D J.W₀ → WO J.W₀ L' → ℂ :=
  fun h w => star (∫ h₀ in B.vA.𝓕,
    φ h₀ * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) ∂B.vA.μ)

structure Last (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D) (B : BesLev D 0) where
  J : JacLev D 0
  s : StepBF ψ B J
  cptS : CoCpt J.W
  cptT : CoCpt T
  χS : (AE D)ˣ →* Circle
  χT : (AE D)ˣ →* Circle
  om : Om J.W T
  weil : IsWeilDatumO ψ J.W T χS χT om
  vT : Vol T

inductive Chain (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D) : (ρ : ℕ) → BesLev D ρ → Type 1
  | last {B : BesLev D 0} (t : Last ψ T B) : Chain ψ T 0 B
  | step {σ : ℕ} {B : BesLev D (σ + 1)} (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (c : Chain ψ T σ B') : Chain ψ T (σ + 1) B

namespace Chain

variable {T : HSp D}

noncomputable def Data : {ρ : ℕ} → {B : BesLev D ρ} → Chain ψ T ρ B → Type
  | _, B, .last t => (WO B.V t.J.W → ℂ) × (WO t.J.W T → ℂ)
  | _, B, .step J B' _ _ _ _ c => (WO B.V J.W → ℂ) × (WO J.W B'.V → ℂ) × c.Data

noncomputable def IsTheta : {ρ : ℕ} → {B : BesLev D ρ} → (c : Chain ψ T ρ B) → c.Data → Prop
  | _, B, .last t, Φ => IsThetaFunO ψ B.V t.J.W Φ.1 ∧ IsThetaFunO ψ t.J.W T Φ.2
  | _, B, .step J B' _ _ _ _ c, Φ => IsThetaFunO ψ B.V J.W Φ.1 ∧ IsThetaFunO ψ J.W B'.V Φ.2.1 ∧ c.IsTheta Φ.2.2

noncomputable def down : {ρ : ℕ} → {B : BesLev D ρ} → (c : Chain ψ T ρ B) → c.Data → (GA D T → ℂ) → GA D B.V → ℂ
  | _, _, .last t, Φ, F => t.s.lift (liftS t.om t.vT.μ t.vT.𝓕 F Φ.2) Φ.1
  | _, _, .step _ _ s₁ s₂ _ _ c, Φ, F => s₁.lift (s₂.lift (c.down Φ.2.2 F) Φ.2.1) Φ.1

noncomputable def Rapid : {ρ : ℕ} → {B : BesLev D ρ} → (c : Chain ψ T ρ B) → c.Data → (GA D T → ℂ) → Prop
  | _, _, .last _, _, _ => True
  | _, _, .step J B' _ s₂ _ _ c, Φ, F =>
      RapidDec J.W (s₂.lift (c.down Φ.2.2 F) Φ.2.1) ∧ RapidDec B'.V (c.down Φ.2.2 F) ∧ c.Rapid Φ.2.2 F

end Chain

def Last.Q {B : BesLev D 0} {T : HSp D} (t : Last ψ T B) (φ : GA D B.A → ℂ) (Φ₁ : WO B.V t.J.W → ℂ) (Φ₂ : WO t.J.W T → ℂ)
    (F : GA D T → ℂ) : ℂ :=
  ∫ h' in t.vT.𝓕, F h' * (∫ h in t.s.vW.𝓕, t.om (h, h') Φ₂ 0 *
    (∫ h₀ in B.vA.𝓕, φ h₀ * t.s.om (embA B.d B.o h₀, h) Φ₁ 0 ∂B.vA.μ) ∂t.s.vW.μ) ∂t.vT.μ

namespace Chain

variable {T : HSp D}

noncomputable def Var : {ρ : ℕ} → {B : BesLev D ρ} → Chain ψ T ρ B → Type
  | _, _, .last _ => Unit
  | _, _B, .step J B' _ _ _ _ c => GA D J.W × GA D B'.V × c.Var

def hand {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
    (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ)
    (φ : GA D B.A → ℂ) (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V) : GA D B'.A → ℂ :=
  handFB s₂ vL (handBF s₁ l φ (flatBF s₁ (s₁.om (g, h₁) Φ₁))) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂))

noncomputable def Q : {ρ : ℕ} → {B : BesLev D ρ} → (c : Chain ψ T ρ B) → c.Data → (GA D T → ℂ) → (GA D B.A → ℂ) → GA D B.V →
    c.Var → ℂ
  | _, _, .last t, Φ, F, φ, g, _ => t.Q φ (t.s.om (g, 1) Φ.1) Φ.2 F
  | _, _, .step _ _ s₁ s₂ l vL c, Φ, F, φ, g, h =>
      c.Q Φ.2.2 F (hand s₁ s₂ l vL Φ.1 Φ.2.1 φ g h.1 h.2.1) h.2.1 h.2.2

noncomputable def Iter : {ρ : ℕ} → {B : BesLev D ρ} → (c : Chain ψ T ρ B) → (c.Var → ℂ) → ℂ → Prop
  | _, _, .last _, q, z => z = q ()
  | _, _, .step J B' s₁ s₂ _ _ c, q, z =>
      ∃ (f₁ : GA D J.W → ℂ) (f₂ : GA D J.W → GA D B'.V → ℂ), IsQuotIntL1 J.μR s₁.vW.μ f₁ z ∧
        ∀ h₁, IsQuotIntL1 B'.μR s₂.vW.μ (f₂ h₁) (f₁ h₁) ∧ ∀ h₂, c.Iter (fun h => q (h₁, h₂, h)) (f₂ h₁ h₂)

end Chain

end GlobalTheory.Unf

end
