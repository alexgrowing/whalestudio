import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair (Pair Unif resChar phiOne inX avec)
open GlobalTheory.SplitWeil (HasConductor IsUnitVol)
open GlobalTheory.StepData (XIx Ix latOf box)
open GlobalTheory.SymChain (SymData)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences

variable {D : D7}

structure LocF : Type 1 where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [ms : MeasurableSpace k]
  [bor : BorelSpace k]

attribute [instance] LocF.fld LocF.val LocF.top LocF.loc LocF.ms LocF.bor

def Steps {ι X : Type} (R : ι → X → X → Prop) (l : List ι) (f₀ : X) : X → Prop :=
  l.foldr (fun i (Q : X → Prop) f => ∃ f₁, Q f₁ ∧ R i f₁ f) fun f => f = f₀

def StepsAll {N : ℕ} {X : Type} (R : Fin N → X → X → Prop) : X → X → Prop := Steps R (List.finRange N)

structure Base (S : HSp D) where
  L : Lat S
  M : Lat S
  t : GA D S
  fin : t ∈ grpAt S fun _ => True
  sd : IsSelfDualC S L
  mv : Moves S t L M fun _ => True

def Base.one (S : HSp D) (L : Lat S) (h : IsSelfDualC S L) : Base S :=
  ⟨L, L, 1, one_mem _, h, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩

def realPts (S : HSp D) : Subgroup (GA D S) := grpOff S fun _ => True

def IsFockOver (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T)
    (R : (WO S T → ℂ) → (WO S T → ℂ) → Prop) (Φ : WO S T → ℂ) : Prop :=
  ∃ (θ : InfFam D) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ) (f₀ f : WO S T → ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) ∧ (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) ∧
    (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) ∧ (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) ∧
    IsVacO ψ θ S T sS sT (LS : Set _) (LT : Set _) f₀ ∧ R f₀ f ∧ Φ = pureTensorO ψ θ S T sS sT BS BT f P

def dblKer {A S X : HSp D} (oma : Om A S) (omb : Om S X) (C : WO A S → WO S X → ℂ) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ℂ :=
  omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0

def dblCol {A S X : HSp D} (vA : Vol A) (vS : Vol S) (oma : Om A S) (omb : Om S X) (C : WO A S → WO S X → ℂ)
    (φ : GA D A → ℂ) (h₂ : GA D X) : ℂ :=
  ∫ h₁ in vS.𝓕, (∫ h₀ in vA.𝓕, φ h₀ * dblKer oma omb C h₀ h₁ h₂ ∂vA.μ) ∂vS.μ

def IsColDatum (ψ : AddChar (AF D.host.F) ℂ) {A S X : HSp D} (oma : Om A S) (omb : Om S X) (LA : Lat A) (LS : Lat S)
    (LX : Lat X) (R₁ : (WO A S → ℂ) → (WO A S → ℂ) → Prop) (R₂ : (WO S X → ℂ) → (WO S X → ℂ) → Prop)
    (C C' : WO A S → WO S X → ℂ) : Prop :=
  (∀ v, Vac ψ A S LA LS (fun _ => True) fun u => C u v) ∧ (∀ u, Vac ψ S X LS LX (fun _ => True) (C u)) ∧
  (∃ C₁ : WO A S → WO S X → ℂ, (∀ v, R₁ (fun u => C u v) fun u => C₁ u v) ∧ ∀ u, R₂ (C₁ u) (C' u)) ∧
  (∀ v, IsThetaFunO ψ A S fun u => C' u v) ∧ (∀ p, IsThetaFunO ψ S X fun v => oma p (fun u => C' u v) 0) ∧
  Continuous fun p : GA D A × GA D S × GA D X => dblKer oma omb C' p.1 p.2.1 p.2.2

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

def vec {S : HSp D} (β : Frame p S n) (i : n) : Fin S.rank → k := fun r => β.b r i

def atW (p : SplitPt D k) {m : ℕ} (y : Fin m → AE D) : Fin m → k := fun r => p.pr (y r)

def IsMoved {S : HSp D} (t : GA D S) (γ β : Frame p S n) : Prop := β.b = (mt S t).map p.pr * γ.b

def InAt {S : HSp D} (γ : Frame p S n) (J : Subgroup (GL n k)) (κ : GA D S) : Prop :=
  ∃ u ∈ J, (mt S κ).map p.pr = γ.b * u.val * γ.b'

def InvOnUnits (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (μ : kˣ →* ℂˣ) : Prop :=
  ∀ (x : (AE D)ˣ) (u : kˣ), valuation k (u : k) = 1 → (x : AE D) = 1 - p.e + p.sec u → ((χ x : Circle) : ℂ) * μ u = 1

def OnLines {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (β : Frame p S (n ⊕ Fin c)) : Prop :=
  ∀ (i : Fin ρ) (l : Fin c), (l.val = i.val → ∃ s : k, vec β (.inr l) = s • atW p fun r => d.jX r i) ∧
    (l.val + i.val + 1 = c → ∃ s : k, vec β (.inr l) = s • atW p fun r => d.jY r i)

def zV {ρ : ℕ} (B : BesLev D ρ) : Fin B.V.rank → AE D := B.d.j0 *ᵥ ratV (vecB B.o B.ζ)

structure IsBesFrame (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) {ρ : ℕ} (B : BesLev D ρ) (α : Frame p B.A n)
    (β : Frame p B.V (n ⊕ Fin c)) : Prop where
  card : c = 2 * ρ + 1
  core : ∀ i, vec β (.inl i) = (B.d.j0 ⬝ B.o.jA).map p.pr *ᵥ vec α i
  lines : OnLines B.d β
  mid : ∀ l : Fin c, l.val = ρ → ∃ s : k, vec β (.inr l) = s • atW p (zV B)
  char : ∀ u ∈ RootEx.N k n c (ρ + 1), psiBes ψ B.d 1 (vecB B.o B.ζ) (β.gl u) = (χ (RootEx.simpleSum u) : ℂ)

structure IsJacFrame (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) {ρ : ℕ} (J : JacLev D ρ) (α : Frame p J.W₀ n)
    (β : Frame p J.W (n ⊕ Fin c)) : Prop where
  card : c = 2 * ρ
  core : ∀ i, vec β (.inl i) = J.d.j0.map p.pr *ᵥ vec α i
  lines : OnLines J.d β
  char : ∀ u ∈ RootEx.N k n c ρ ⊓ RootEx.N k n c (ρ + 1),
    (∀ l l' : Fin c, l.val + 1 = ρ → l'.val = ρ → u.val (.inr l) (.inr l') = 0) →
      psiFlag ψ J.d (β.gl u) = (χ (RootEx.simpleSum u) : ℂ)

def FrameMapsPrefix {S T : HSp D} (x : WO S T) (β' : Frame p S (n' ⊕ Fin c')) (β : Frame p T (n ⊕ Fin c)) (b : ℕ) : Prop :=
  ∀ (l' : Fin c') (l : Fin c), l'.val = l.val → l.val < b → Matrix.map x p.pr *ᵥ vec β' (.inr l') = vec β (.inr l)

def jacLat (q : Unif k) (c ρ : ℕ) (Λ : Submodule 𝒪[k] (n → k)) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  Λ.map (inX k n c) ⊔ Submodule.span 𝒪[k] {y | ∃ i, 1 ≤ i ∧ i ≤ ρ ∧ i ≤ c ∧ y = avec k n c i} ⊔
    Submodule.span 𝒪[k] {y | ∃ i, ρ < i ∧ i ≤ c ∧ y = q.inv • avec k n c i}

end Frames

def ptBF {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) : WO B.V J.W :=
  B.d.extX J.W (xZero J.d) + B.d.ext0 J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)))

def ptFB {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) : WO J.W B.V := J.d.extX B.V (xLast B.d (vecB B.o B.ζ))

structure Dbl (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) where
  B : BesLev D (σ + 1)
  J : JacLev D (σ + 1)
  B' : BesLev D σ
  s₁ : StepBF ψ B J
  s₂ : StepFB ψ J B'
  l : Link B B'.L B'.ζ
  vL : VolM D B'.L.rank J.W₀.rank
  b₀ : Base B.V
  b₁ : Base J.W
  b₂ : Base B'.V
  M₀ : Lat B.V₀
  M₂ : Lat B'.V₀
  L₀ : Lat B.A
  L₁ : Lat J.W₀
  L₂ : Lat B'.A
  Lz : Lat B.L
  Lz' : Lat B'.L
  sd₀ : IsSelfDualC B.A L₀
  sd₁ : IsSelfDualC J.W₀ L₁
  sd₂ : IsSelfDualC B'.A L₂
  sdz : IsSelfDualC B.L Lz
  sdz' : IsSelfDualC B'.L Lz'
  χA : (AE D)ˣ →* Circle
  χA' : (AE D)ˣ →* Circle
  χz : (AE D)ˣ →* Circle
  oma : Om B.A J.W₀
  omz : Om B.L J.W₀
  omb : Om J.W₀ B'.A
  omz' : Om J.W₀ B'.L
  chV : s₁.χV = χA * χz
  chW : s₂.χW = χA' * χz
  wa : IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma
  wz : IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz
  wb : IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb
  wz' : IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz'

namespace Dbl

variable {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (X : Dbl ψ σ)

structure GoodAt (v : Pl D) : Prop where
  bf : GoodBF ψ X.B X.J X.b₀.M X.M₀ X.b₁.M X.L₁ v
  fb : AdaptFB ψ X.J X.B' X.b₁.M X.L₁ X.b₂.M X.M₂ v
  split : OrthAt X.B.o X.M₀ X.L₀ X.Lz v
  split' : OrthAt X.B'.o X.M₂ X.L₂ X.Lz' v
  unr₁ : UnrAt X.s₁ v
  unr₂ : UnrAt X.s₂ v

structure Frames (K : LocF) (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] where
  p : SplitPt D K.k
  χ : AddChar K.k Circle
  cond : HasConductor χ 1
  unit : p.UnitAA
  α₀ : Frame p X.B.A n₀
  α₁ : Frame p X.J.W₀ n₁
  α₂ : Frame p X.B'.A n₂
  β₀ : Frame p X.B.V (n₀ ⊕ Fin (2 * σ + 1 + 1 + 1))
  β₁ : Frame p X.J.W (n₁ ⊕ Fin (2 * σ + 1 + 1))
  β₂ : Frame p X.B'.V (n₂ ⊕ Fin (2 * σ + 1))
  fr₀ : IsBesFrame ψ χ X.B α₀ β₀
  fr₁ : IsJacFrame ψ χ X.J α₁ β₁
  fr₂ : IsBesFrame ψ χ X.B' α₂ β₂
  st₁ : FrameMapsPrefix (ptBF X.B X.J) β₀ β₁ (σ + 2)
  st₂ : FrameMapsPrefix (ptFB X.J X.B') β₁ β₂ (σ + 1)

structure LevPl where
  K : LocF
  F : X.Frames K (Fin X.B.A.rank) (Fin X.J.W₀.rank) (Fin X.B'.A.rank)
  q : Unif K.k
  P₀ : Pair K.k (Fin X.B.A.rank)
  P₁ : Pair K.k (Fin X.J.W₀.rank)
  P₂ : Pair K.k (Fin X.B'.A.rank)
  row₀ : F.β₀.IsLat X.b₀.M (P₀.glued q (2 * σ + 1 + 1 + 1) (σ + 2))
  row₁ : F.β₁.IsLat X.b₁.M (jacLat q (2 * σ + 1 + 1) (σ + 1) P₁.lat)
  row₂ : F.β₂.IsLat X.b₂.M (P₂.glued q (2 * σ + 1) (σ + 1))
  col₀ : F.α₀.IsLat X.L₀ P₀.lat
  col₁ : F.α₁.IsLat X.L₁ P₁.lat
  col₂ : F.α₂.IsLat X.L₂ P₂.lat
  unr₁ : UnrAt X.s₁ F.p.v
  unr₂ : UnrAt X.s₂ F.p.v

structure TypePl (s κ t j : ℕ) (H : j + 1 + 1 + 2 * σ = s) where
  K : LocF
  S : SymData K.k s κ
  ν : Measure K.k
  vol : IsUnitVol ν
  F : X.Frames K (XIx (Fin κ) (Fin t) j) (XIx (Fin κ) (Fin t) (j + 1)) (XIx (Fin κ) (Fin t) (j + 1 + 1))
  char : F.χ = S.ψ
  γ₀ : Frame F.p X.B.V (XIx (Fin κ) (Fin t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  γ₁ : Frame F.p X.J.W (XIx (Fin κ) (Fin t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
  γ₂ : Frame F.p X.B'.V (XIx (Fin κ) (Fin t) (j + 1 + 1) ⊕ Fin (2 * σ + 1))
  mv₀ : IsMoved X.b₀.t γ₀ F.β₀
  mv₁ : IsMoved X.b₁.t γ₁ F.β₁
  mv₂ : IsMoved X.b₂.t γ₂ F.β₂
  row₀ : F.β₀.IsLat X.b₀.M (latOf ((S.T (Fin t)).bas j (2 * σ + 1 + 1 + 1) (by omega)))
  row₁ : F.β₁.IsLat X.b₁.M (latOf ((S.T (Fin t)).bas (j + 1) (2 * σ + 1 + 1) (by omega)))
  row₂ : F.β₂.IsLat X.b₂.M (latOf ((S.T (Fin t)).bas (j + 1 + 1) (2 * σ + 1) (by omega)))
  col₀ : F.α₀.IsLat X.L₀ (box _ 1)
  col₁ : F.α₁.IsLat X.L₁ (box _ 1)
  col₂ : F.α₂.IsLat X.L₂ (box _ 1)
  mu₁ : InvOnUnits F.p X.s₁.χV (S.μ (j + 1)) ∧ InvOnUnits F.p X.s₁.χW (S.μ (j + 1))
  mu₂ : InvOnUnits F.p X.s₂.χV (S.μ (j + 1 + 1)) ∧ InvOnUnits F.p X.s₂.χW (S.μ (j + 1 + 1))

structure Tower (s κ t j : ℕ) (H : j + 1 + 1 + 2 * σ = s) where
  nT : ℕ
  ng : ℕ
  T : Fin nT → X.LevPl
  G : Fin ng → X.TypePl s κ t j H
  inj : Function.Injective (Sum.elim (fun i => (T i).F.p.v) fun i => (G i).F.p.v)
  good : ∀ v, (∀ i, (T i).F.p.v ≠ v) → (∀ i, (G i).F.p.v ≠ v) → X.GoodAt v
  Φ₁ : WO X.B.V X.J.W → ℂ
  Φ₂ : WO X.J.W X.B'.V → ℂ
  dat₁ : IsFockOver ψ X.B.V X.J.W X.b₀.L X.b₁.L (StepsAll fun i f₀ f => Over ψ (G i).γ₀ (G i).γ₁ X.b₀.L X.b₁.L f₀
    (((G i).S.T (Fin t)).Phi j (2 * σ + 1 + 1) (by omega)) f) Φ₁
  dat₂ : IsFockOver ψ X.J.W X.B'.V X.b₁.L X.b₂.L (StepsAll fun i f₀ f => Over ψ (G i).γ₁ (G i).γ₂ X.b₁.L X.b₂.L f₀
    (((G i).S.T (Fin t)).Phi (j + 1) (2 * σ + 1) (by omega)) f) Φ₂

namespace Tower

variable {X} {s κ t j : ℕ} {H : j + 1 + 1 + 2 * σ = s} (Y : X.Tower s κ t j H)

def InJ₁ (u : GA D X.J.W) : Prop :=
  InK X.J.W X.b₁.L (fun _ => True) u ∧
    ∀ i, InAt (Y.G i).γ₁ (((Y.G i).S.T (Fin t)).lev (j + 1) (2 * σ + 1 + 1) (by omega)).J u

def InJ₂ (u : GA D X.B'.V) : Prop :=
  InK X.B'.V X.b₂.L (fun _ => True) u ∧
    ∀ i, InAt (Y.G i).γ₂ (((Y.G i).S.T (Fin t)).lev (j + 1 + 1) (2 * σ + 1) (by omega)).J u

def Ram (φ : GA D X.B.A → ℂ) : Prop := IsContAut X.B.A φ ∧ ∀ i, RamAt (Y.T i).F.α₀ (Y.T i).P₀ φ

def opS (φ : GA D X.B.A → ℂ) : GA D X.B.A → ℂ :=
  (List.finRange Y.nT).foldr (fun i => sOp (Y.T i).F.α₀ (Y.T i).P₀ (Y.T i).q
    (resChar (Y.T i).F.χ (Y.T i).F.cond (Y.T i).q) (-1)) φ

def Col₁ (f₀ f : WO X.B.A X.J.W₀ → ℂ) : Prop :=
  ∃ f₁, StepsAll (fun i g₀ g => Over ψ (Y.T i).F.α₀ (Y.T i).F.α₁ X.L₀ X.L₁ g₀ (phiOne (Y.T i).P₀ (Y.T i).P₁) g) f₀ f₁ ∧
    StepsAll (fun i g₀ g => Over ψ (Y.G i).F.α₀ (Y.G i).F.α₁ X.L₀ X.L₁ g₀
      (((Y.G i).S.T (Fin t)).entry (Y.G i).S.ψ (Y.G i).ν j (2 * σ + 1) (by omega) 1 1) g) f₁ f

def Col₂ (f₀ f : WO X.J.W₀ X.B'.A → ℂ) : Prop :=
  ∃ f₁, StepsAll (fun i g₀ g => Over ψ (Y.T i).F.α₁ (Y.T i).F.α₂ X.L₁ X.L₂ g₀ (phiOne (Y.T i).P₁ (Y.T i).P₂) g) f₀ f₁ ∧
    StepsAll (fun i g₀ g => Over ψ (Y.G i).F.α₁ (Y.G i).F.α₂ X.L₁ X.L₂ g₀
      (((Y.G i).S.T (Fin t)).entry (Y.G i).S.ψ (Y.G i).ν (j + 1) (2 * σ) H 1 1) g) f₁ f

def SupportJac : Prop :=
  ∀ a ∈ realPts X.B.V, ∀ h₁, flatBF X.s₁ (X.s₁.om (a * X.b₀.t, h₁) Y.Φ₁) ≠ 0 →
    ∃ r ∈ jacGrp X.J.d, ∃ a₁ ∈ realPts X.J.W, ∃ u, Y.InJ₁ u ∧ h₁ = r * a₁ * X.b₁.t * u

def SupportBes : Prop :=
  ∀ φ, Y.Ram φ → ∀ a ∈ realPts X.B.V, ∀ h₁ h₂,
    Chain.hand X.s₁ X.s₂ X.l X.vL Y.Φ₁ Y.Φ₂ φ (a * X.b₀.t) h₁ h₂ ≠ 0 →
      ∃ r ∈ besGrp X.B'.d X.B'.o, ∃ a₂ ∈ realPts X.B'.V, ∃ u, Y.InJ₂ u ∧ h₂ = r * a₂ * X.b₂.t * u

def Value : Prop :=
  ∀ a₀ ∈ realPts X.B.V, ∀ a₁ ∈ realPts X.J.W, ∀ a₂ ∈ realPts X.B'.V,
    ∃ C C' : WO X.B.A X.J.W₀ → WO X.J.W₀ X.B'.A → ℂ, IsColDatum ψ X.oma X.omb X.L₀ X.L₁ X.L₂ Y.Col₁ Y.Col₂ C C' ∧
      ∀ φ, Y.Ram φ → Chain.hand X.s₁ X.s₂ X.l X.vL Y.Φ₁ Y.Φ₂ φ (a₀ * X.b₀.t) (a₁ * X.b₁.t) (a₂ * X.b₂.t) =
        dblCol X.B.vA X.J.v0 X.oma X.omb C' (Y.opS φ)

end Tower

end Dbl

structure End (ψ : AddChar (AF D.host.F) ℂ) (X' : HSp D) where
  B : BesLev D 0
  t : Last ψ X' B
  Xm : HSp D
  Z : HSp D
  o : OrthDec Xm X' Z
  rk : Z.rank = 1
  τ : Matrix (Fin B.L.rank) (Fin Z.rank) D.host.E
  norm : τᴴ ⬝ (B.L.gram ⬝ τ) = (-(D.host.xi0 * star D.host.xi0)) • Z.gram
  b₀ : Base B.V
  M₀ : Lat B.V₀
  L₀ : Lat B.A
  Lz : Lat B.L
  L₁ : Lat t.J.W
  L' : Lat X'
  Lz' : Lat Z
  L₂ : Lat Xm
  sdM : IsSelfDualC B.V₀ M₀
  sd₀ : IsSelfDualC B.A L₀
  sdz : IsSelfDualC B.L Lz
  sd₁ : IsSelfDualC t.J.W L₁
  sd' : IsSelfDualC X' L'
  sdz' : IsSelfDualC Z Lz'
  sd₂ : IsSelfDualC Xm L₂
  χA : (AE D)ˣ →* Circle
  χz : (AE D)ˣ →* Circle
  oma : Om B.A t.J.W
  omz : Om B.L t.J.W
  omb : Om t.J.W Xm
  omz' : Om t.J.W Z
  chV : t.s.χV = χA * χz
  wa : IsWeilDatumO ψ B.A t.J.W χA t.s.χW oma
  wz : IsWeilDatumO ψ B.L t.J.W χz t.s.χW omz
  wb : IsWeilDatumO ψ t.J.W Xm t.χS (t.χT * χz⁻¹) omb
  wz' : IsWeilDatumO ψ t.J.W Z t.χS χz⁻¹ omz'

namespace End

variable {ψ : AddChar (AF D.host.F) ℂ} {X' : HSp D} (X : End ψ X')

def Unr (v : Pl D) : Prop := UnrAt X.t.s v ∧ CharUnramAt D X.t.χS v ∧ CharUnramAt D X.t.χT v

structure GoodAt (v : Pl D) : Prop where
  tame : Tame D v
  mono : MonoAt X.B.d X.b₀.M X.M₀ v
  split : OrthAt X.B.o X.M₀ X.L₀ X.Lz v
  split' : OrthAt X.o X.L₂ X.L' X.Lz' v
  line : ∀ w : WO X.t.J.W X.Z, MxAt (· = v) w →
    (w ∈ latO X.t.J.W X.Z (X.L₁ : Set _) (X.Lz' : Set _) (· = v) ↔
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj X.B.L X.t.J.W ((rat X.τ : Mx D X.B.L.rank X.Z.rank) ⬝ w) ∈
        latO X.B.L X.t.J.W (X.Lz : Set _) (X.L₁ : Set _) (· = v))
  unr : X.Unr v

structure Frames (K : LocF) (n₀ n₁ n₂ u : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] [Fintype u] [DecidableEq u] where
  p : SplitPt D K.k
  χ : AddChar K.k Circle
  cond : HasConductor χ 1
  unit : p.UnitAA
  α₀ : Frame p X.B.A n₀
  α₁ : Frame p X.t.J.W n₁
  α₂ : Frame p X.Xm (n₂ ⊕ u)
  β₀ : Frame p X.B.V (n₀ ⊕ Fin (0 + 1))
  δ : Frame p X' n₂
  fr₀ : IsBesFrame ψ χ X.B α₀ β₀
  fr₂ : ∀ i, vec α₂ (.inl i) = X.o.jA.map p.pr *ᵥ vec δ i
  θ : K.k
  s : K.k
  z₀ : Fin X.Z.rank → K.k
  char : ∀ a, (χ a : ℂ) = psiE ψ (p.sec (θ * a))
  aux : vec β₀ (.inr 0) = s • atW p (zV X.B)
  last : ∀ i, vec α₂ (.inr i) = X.o.jB.map p.pr *ᵥ z₀
  link : (rat X.τ : Mx D X.B.L.rank X.Z.rank).map p.pr *ᵥ z₀ = -(θ * s) • atW p (ratV X.B.ζ)

structure LevPl where
  K : LocF
  F : X.Frames K (Fin X.B.A.rank) (Fin X.t.J.W.rank) (Fin X'.rank) (Fin 1)
  q : Unif K.k
  P₀ : Pair K.k (Fin X.B.A.rank)
  P₁ : Pair K.k (Fin X.t.J.W.rank)
  Λ : Submodule 𝒪[K.k] (Fin X'.rank → K.k)
  [lat : Λ.IsLattice K.k]
  row₀ : F.β₀.IsLat X.b₀.M (P₀.glued q (0 + 1) 1)
  row₂ : F.δ.IsLat X.L' Λ
  col₀ : F.α₀.IsLat X.L₀ P₀.lat
  col₁ : F.α₁.IsLat X.L₁ P₁.lat
  col₂ : F.α₂.IsLat X.L₂ (lastPair q Λ).lat
  unr : X.Unr F.p.v

attribute [instance] LevPl.lat

structure TypePl (s κ t : ℕ) where
  K : LocF
  S : SymData K.k s κ
  ν : Measure K.k
  vol : IsUnitVol ν
  F : X.Frames K (XIx (Fin κ) (Fin t) s) (XIx (Fin κ) (Fin t) (s + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) (s + 2)) Unit
  char : F.χ = S.ψ
  γ₀ : Frame F.p X.B.V (XIx (Fin κ) (Fin t) s ⊕ Fin (0 + 1))
  γ₁ : Frame F.p X.t.J.W (XIx (Fin κ) (Fin t) (s + 1) ⊕ Fin 0)
  mv₀ : IsMoved X.b₀.t γ₀ F.β₀
  same : ∀ i, vec γ₁ (.inl i) = vec F.α₁ i
  row₀ : F.β₀.IsLat X.b₀.M (latOf ((S.T (Fin t)).bas s (0 + 1) rfl))
  row₂ : F.δ.IsLat X.L' (box _ 1)
  col₀ : F.α₀.IsLat X.L₀ (box _ 1)
  col₁ : F.α₁.IsLat X.L₁ (box _ 1)
  col₂ : F.α₂.IsLat X.L₂ (box _ 1)
  mu₁ : InvOnUnits F.p X.t.s.χV (S.μ (s + 1)) ∧ InvOnUnits F.p X.t.s.χW (S.μ (s + 1))
  mu₂ : InvOnUnits F.p X.t.χS (S.μ (s + 2)) ∧ InvOnUnits F.p X.t.χT (S.μ (s + 2))

structure Tower (s κ t : ℕ) where
  nT : ℕ
  ng : ℕ
  T : Fin nT → X.LevPl
  G : Fin ng → X.TypePl s κ t
  inj : Function.Injective (Sum.elim (fun i => (T i).F.p.v) fun i => (G i).F.p.v)
  good : ∀ v, (∀ i, (T i).F.p.v ≠ v) → (∀ i, (G i).F.p.v ≠ v) → X.GoodAt v
  Φ₁ : WO X.B.V X.t.J.W → ℂ
  Φ₂ : WO X.t.J.W X' → ℂ
  dat₁ : IsFockOver ψ X.B.V X.t.J.W X.b₀.L X.L₁ (StepsAll fun i f₀ f => Over ψ (G i).γ₀ (G i).γ₁ X.b₀.L X.L₁ f₀
    (((G i).S.T (Fin t)).Phi s 0 rfl) f) Φ₁
  dat₂ : IsFockOver ψ X.t.J.W X' X.L₁ X.L' (StepsAll fun i f₀ f => Over ψ (G i).γ₁ (G i).F.δ X.L₁ X.L' f₀
    ((G i).S.T (Fin t)).PhiTop f) Φ₂

namespace Tower

variable {X} {s κ t : ℕ} (Y : X.Tower s κ t)

def Ram (φ : GA D X.B.A → ℂ) : Prop := IsContAut X.B.A φ ∧ ∀ i, RamAt (Y.T i).F.α₀ (Y.T i).P₀ φ

def opS (φ : GA D X.B.A → ℂ) : GA D X.B.A → ℂ :=
  (List.finRange Y.nT).foldr (fun i => sOp (Y.T i).F.α₀ (Y.T i).P₀ (Y.T i).q
    (resChar (Y.T i).F.χ (Y.T i).F.cond (Y.T i).q) (-1)) φ

def Col₁ (f₀ f : WO X.B.A X.t.J.W → ℂ) : Prop :=
  ∃ f₁, StepsAll (fun i g₀ g => Over ψ (Y.T i).F.α₀ (Y.T i).F.α₁ X.L₀ X.L₁ g₀ (phiOne (Y.T i).P₀ (Y.T i).P₁) g) f₀ f₁ ∧
    StepsAll (fun i g₀ g => Over ψ (Y.G i).F.α₀ (Y.G i).F.α₁ X.L₀ X.L₁ g₀
      (((Y.G i).S.T (Fin t)).xiPen (box _ 1) 1 (Submodule.Quotient.mk ((Y.G i).S.y0 (Fin t)))) g) f₁ f

def Col₂ (f₀ f : WO X.t.J.W X.Xm → ℂ) : Prop :=
  ∃ f₁, StepsAll (fun i g₀ g => Over ψ (Y.T i).F.α₁ (Y.T i).F.α₂ X.L₁ X.L₂ g₀
      (phiOne (Y.T i).P₁ (lastPair (Y.T i).q (Y.T i).Λ)) g) f₀ f₁ ∧
    StepsAll (fun i g₀ g => Over ψ (Y.G i).F.α₁ (Y.G i).F.α₂ X.L₁ X.L₂ g₀
      (((Y.G i).S.T (Fin t)).xiTop (box _ 1) (Y.G i).S.ψ (Y.G i).ν (-1)
        (Submodule.Quotient.mk ((Y.G i).S.y0 (Fin t)))) g) f₁ f

def Value : Prop :=
  ∀ a ∈ realPts X.B.V, ∃ C C' : WO X.B.A X.t.J.W → WO X.t.J.W X.Xm → ℂ,
    IsColDatum ψ X.oma X.omb X.L₀ X.L₁ X.L₂ Y.Col₁ Y.Col₂ C C' ∧
      ∀ φ, Y.Ram φ → ∀ F, IsContAut X' F → X.t.Q φ (X.t.s.om (a * X.b₀.t, 1) Y.Φ₁) Y.Φ₂ F =
        ∫ h in X.t.vT.𝓕, F h * dblCol X.B.vA X.t.s.vW X.oma X.omb C' (Y.opS φ) (X.o.emb (h, 1)) ∂X.t.vT.μ

end Tower

end End

def Route (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ,
    (∀ (σ : ℕ) (X : Dbl ψ σ) (s κ t j : ℕ) (H : j + 1 + 1 + 2 * σ = s) (Y : X.Tower s κ t j H),
      Y.SupportJac ∧ Y.SupportBes ∧ Y.Value) ∧
    ∀ (X' : HSp D) (X : End ψ X') (s κ t : ℕ) (Y : X.Tower s κ t), Y.Value

example {X : Type} (R : Fin 0 → X → X → Prop) (f₀ f : X) : StepsAll R f₀ f ↔ f = f₀ := Iff.rfl

example {X : Type} (R : Fin 1 → X → X → Prop) (f₀ f : X) : StepsAll R f₀ f ↔ R 0 f₀ f := by
  simp [StepsAll, List.finRange_succ, Steps]

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences

end
