import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

structure PairDat (p : ι → SplitPt D k) (A S : HSp D) (n : Type) [Fintype n] [DecidableEq n] where
  α : ∀ i, Frame (p i) A n
  α₀ : ∀ i, Frame (p i) S (n ⊕ Fin 1)
  P : ι → Pair k n

structure MidDat (p : ι → SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] where
  β : ∀ i, Frame (p i) S n
  Q : ι → Pair k n

variable {p : ι → SplitPt D k} {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n'']
  [DecidableEq n'']

def PairDat.Ram {A S : HSp D} (a : PairDat p A S n) (φ : GA D A → ℂ) : Prop := IsContAut A φ ∧ ∀ i, RamAt (a.α i) (a.P i) φ

def PairDat.sAll {A S : HSp D} (a : PairDat p A S n) (q : Unif k) (χ : ι → AddChar 𝓀[k] ℂ) (ε : ι → 𝓀[k]ˣ) (l : List ι)
    (φ : GA D A → ℂ) : GA D A → ℂ :=
  l.foldr (fun i ψ => sOp (a.α i) (a.P i) q (χ i) (ε i) ψ) φ

def OverAll (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S)
    (LT : Lat T) (Ψ : ι → Matrix n n' k → ℂ) (l : List ι) (f f' : WO S T → ℂ) : Prop :=
  l.foldr (fun i (r : (WO S T → ℂ) → Prop) f₂ => ∃ g, r g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f₂) (fun f₂ => f₂ = f) f'

structure DblLat {σ : ℕ} (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) where
  L₀ : Lat B.V
  M₀ : Lat B.V₀
  L₁ : Lat J.W
  M₁ : Lat J.W₀
  L₂ : Lat B'.V
  M₂ : Lat B'.V₀

structure DblShape {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (Λ : DblLat B J B') (P : Pl D → Prop) (q : Unif k) (a : PairDat p B.A B.V₀ n')
    (b : MidDat p J.W₀ n) (a' : PairDat p B'.A B'.V₀ n'') : Prop where
  inj : Function.Injective fun i => (p i).v
  mem : ∀ i, P (p i).v
  good : ∀ v, P v → GoodBF ψ B J Λ.L₀ Λ.M₀ Λ.L₁ Λ.M₁ v
  adapt : ∀ v, P v → AdaptFB ψ J B' Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ v
  unr : ∀ v, P v → UnrAt s₁ v ∧ UnrAt s₂ v
  split : ∀ v, P v → (∀ i, v ≠ (p i).v) → SplitCore B' Λ.M₂ v
  gl : ∀ i, GluedCore B Λ.M₀ q (a.α i) (a.α₀ i) (a.P i)
  gl' : ∀ i, GluedCore B' Λ.M₂ q (a'.α i) (a'.α₀ i) (a'.P i)
  mid : ∀ i, (b.β i).IsLat Λ.M₁ (b.Q i).lat

def ShiftLaw (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (x : Mx D W.rank ρ)
    (P : Pl D → Prop) (𝔉 : (WO V W → ℂ) → (WO V₀ W₀ → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ V W f → ∀ N : Mx D ρ ρ, MxAt P N → (∀ i j, j ≤ i → N i j = 0) →
    𝔉 (heisO ψ V W (dV.extX W (x ⬝ N)) f) = psiE ψ (upSum N) • 𝔉 f

def FlatShift (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop),
    (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J), ShiftLaw ψ B.d (xZero J.d) P (flatBF s)) ∧
    ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B),
      ShiftLaw ψ J.d (xLast B.d (vecB B.o B.ζ)) P (flatFB s)

def SupportShift (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W)
    (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D), AdaptFB ψ J B LV LV₀ LW LW₀ v → UnrAt s v →
    ∀ 𝔉, IsFlatFB s (· = v) 𝔉 → ShiftLaw ψ J.d (xLast B.d (vecB B.o B.ζ)) (· = v) 𝔉 → ∀ f, Vac ψ J.W B.V LV LW (· = v) f →
      Vac ψ J.W₀ B.V₀ LV₀ LW₀ (· = v) (𝔉 f) ∧
      ∀ h ∈ grpAt B.V (· = v), 𝔉 (s.om (1, h) f) ≠ 0 →
        ∃ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) ∧ ∃ γ ∈ grpAt B.V₀ (· = v), ∃ κ, InK B.V LW (· = v) κ ∧
          h = n * B.d.emb0 γ * κ ∧ ∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ LW₀ (· = v) →
            mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ LW₀ (· = v)

def InBig (S : HSp D) (R : Subgroup (GA D S)) (L : Lat S) (P : Pl D → Prop) (h : GA D S) : Prop :=
  ∃ r ∈ R, r ∈ grpAt S P ∧ ∃ g ∈ grpOff S P, ∃ κ, InK S L P κ ∧ h = r * g * κ

def SuppFirst (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V)
    (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (P : Pl D → Prop), (∀ v, P v → GoodBF ψ B J LV LV₀ LW LW₀ v) →
    (∀ v, P v → UnrAt s v) → IsSelfDualC J.W LW → ∀ Φ, Vac ψ B.V J.W LV LW P Φ →
      (∀ κ κ', InK B.V LV P κ → InK J.W LW P κ' → s.om (κ, κ') Φ = Φ) ∧
      ∀ g ∈ grpOff B.V P, (∀ h, flatBF s (s.om (g, h) Φ) ≠ 0 → InBig J.W (jacGrp J.d) LW P h) ∧
        ∀ h ∈ grpOff J.W P, Vac ψ B.V₀ J.W₀ LV₀ LW₀ P (flatBF s (s.om (g, h) Φ))

def SuppSecond (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n'']
    [DecidableEq n''] (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1))
    (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Λ : DblLat B J B') (P : Pl D → Prop) (a : PairDat p B.A B.V₀ n') (b : MidDat p J.W₀ n) (a' : PairDat p B'.A B'.V₀ n''),
    DblShape s₁ s₂ Λ P q a b a' → IsSelfDualC B'.V Λ.L₂ → ∀ Φ₁ Φ₂, Vac ψ B.V J.W Λ.L₀ Λ.L₁ P Φ₁ → Vac ψ J.W B'.V Λ.L₁ Λ.L₂ P Φ₂ →
      (∀ κ κ', InK J.W Λ.L₁ P κ → InK B'.V Λ.L₂ P κ' → s₂.om (κ, κ') Φ₂ = Φ₂) ∧
      ∀ h₁ ∈ grpOff J.W P, (∀ h₂ ∈ grpOff B'.V P, Vac ψ J.W₀ B'.V₀ Λ.M₁ Λ.M₂ P (flatFB s₂ (s₂.om (h₁, h₂) Φ₂))) ∧
        ∀ g ∈ grpOff B.V P, ∀ φ, a.Ram φ → ∀ h₂, Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂ ≠ 0 →
          InBig B'.V (besGrp B'.d B'.o) Λ.L₂ P h₂

def ValueDouble (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (χ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ i) 1), (∀ i, (p i).IsChar ψ (χ i)) → ∃ ε : ι → 𝓀[k]ˣ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
      (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (Λ : DblLat B J B') (P : Pl D → Prop)
      (a : PairDat p B.A B.V₀ n') (b : MidDat p J.W₀ n) (a' : PairDat p B'.A B'.V₀ n''), DblShape s₁ s₂ Λ P q a b a' →
      ∀ I : List ι, I.Nodup → (∀ i, i ∈ I) → ∃ c c' : ℂ, ∀ Ξ₁ Ξ₂, Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ P Ξ₁ → Vac ψ J.W₀ B'.V₀ Λ.M₁ Λ.M₂ P Ξ₂ →
        (∃ Ξ₁', OverAll ψ a.α₀ b.β Λ.M₀ Λ.M₁ (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) I Ξ₁ Ξ₁') ∧
        (∃ Ξ₂', OverAll ψ b.β a'.α₀ Λ.M₁ Λ.M₂ (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) I Ξ₂ Ξ₂') ∧
        ∀ Ξ₁' Ξ₂',
          OverAll ψ a.α₀ b.β Λ.M₀ Λ.M₁ (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) I Ξ₁ Ξ₁' →
          OverAll ψ b.β a'.α₀ Λ.M₁ Λ.M₂ (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) I Ξ₂ Ξ₂' →
          ∀ φ, a.Ram φ →
            hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ = c • hand0 s₁ s₂ l vL (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I φ) Ξ₁' Ξ₂' ∧
            hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ = c' • a'.sAll q (fun i => resChar (χ i) (hχ i) q) ε I (hand0 s₁ s₂ l vL φ Ξ₁' Ξ₂') ∧
            a'.Ram (hand0 s₁ s₂ l vL φ Ξ₁' Ξ₂') ∧ a'.Ram (hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂)

def ValueLast (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D)
    (B : BesLev D 0) (t : Last ψ T B) (o : OrthDec B.V B.A B.L), (∀ x, o.emb (x, 1) = embA B.d B.o x) →
    ∀ (a : PairDat p B.A B.V n') (b : MidDat p t.J.W n) (L₁ : Lat B.V) (L₂ : Lat t.J.W) (L₃ : Lat T),
      Function.Injective (fun i => (p i).v) → IsSelfDualC B.V L₁ → IsSelfDualC t.J.W L₂ → IsSelfDualC T L₃ →
      (∀ i, (p i).UnitAA ∧ ExtUnramAt D (p i).v ∧ UnrAt t.s (p i).v ∧ CharUnramAt D t.χS (p i).v ∧
        CharUnramAt D t.χT (p i).v ∧ IsSumFrame o B.ζ (a.α i) (a.α₀ i) ∧
        (a.α₀ i).IsLat L₁ (gluedS q 1 (a.P i).ker (a.P i).vec) ∧ (b.β i).IsLat L₂ (b.Q i).lat) →
      ∀ I : List ι, I.Nodup → (∀ i, i ∈ I) → ∃ c : ℂ, ∀ Φ₁ Φ₂, Vac ψ B.V t.J.W L₁ L₂ (fun v => ∃ i, v = (p i).v) Φ₁ →
        Vac ψ t.J.W T L₂ L₃ (fun v => ∃ i, v = (p i).v) Φ₂ →
        (∃ Φ₁', OverAll ψ a.α₀ b.β L₁ L₂
          (fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (b.Q i))) I Φ₁ Φ₁') ∧
        ∀ Φ₁', OverAll ψ a.α₀ b.β L₁ L₂
            (fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (b.Q i))) I Φ₁ Φ₁' →
          ∀ φ, a.Ram φ → ∀ F, IsContAut T F →
            t.Q φ Φ₁ Φ₂ F = c * t.Q (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun _ => 1) I φ) Φ₁' Φ₂ F

def AllBijective (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : ι → 𝓀[k]ˣ)
    (n : Type) [Fintype n] [DecidableEq n] (A S : HSp D) (a : PairDat p A S n), Function.Injective (fun i => (p i).v) →
    ∀ I : List ι, Set.BijOn (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I) {φ | a.Ram φ} {φ | a.Ram φ} ∧
      ∃ c c' : GA D A →₀ ℂ, (∀ g, c g ≠ 0 ∨ c' g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v) ∧
        (∀ φ, a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I φ = c.sum fun g x => x • rTrans g φ) ∧
        ∀ φ, a.Ram φ → a.Ram (c'.sum fun g x => x • rTrans g φ) ∧
          a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I (c'.sum fun g x => x • rTrans g φ) = φ

def CollapseInt : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ G₂ R J : Subgroup G),
    IsClosed (G₁ : Set G) → IsClosed (G₂ : Set G) → IsClosed (R : Set G) → (∀ x ∈ G₁, ∀ y ∈ G₂, x * y = y * x) →
    IsHomeomorph (fun x : G₁ × G₂ => (x.1 : G) * x.2) → (∀ r ∈ R, ∃ x ∈ R ⊓ G₁, ∃ y ∈ R ⊓ G₂, r = x * y) →
    J ≤ G₂ → IsCompact (J : Set G) → IsOpen ((J.subgroupOf G₂ : Subgroup G₂) : Set G₂) →
    ∀ (μG : Measure G) (μR : Measure R) (μ₁ : Measure G₁) (ν₁ : Measure (R.subgroupOf G₁)), μG.IsHaarMeasure →
      μR.IsHaarMeasure → μR.IsMulRightInvariant → μ₁.IsHaarMeasure → ν₁.IsHaarMeasure →
      ∃ c : ℝ, 0 < c ∧ ∀ (f : G → ℂ) (z : ℂ), IsQuotIntL1 μR μG f z → (∀ g, ∀ j ∈ J, f (g * j) = f g) →
        (∀ g, f g ≠ 0 → ∃ r ∈ R, ∃ x ∈ G₁, ∃ j ∈ J, g = r * x * j) →
        ∃ z₁, IsQuotIntL1 ν₁ μ₁ (fun x : G₁ => f x) z₁ ∧ z = c * z₁

def ClassSumReal (D : D7) : Prop :=
  ∀ V : HSp D, GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → ∀ K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)),
    GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Formalism.IndefR.Links.IsMeasDef V K μ 𝓕 →
    ∀ (I : Type) [Fintype I] (y : I → Formalism.IndefR.Bridge.Gf V),
      Formalism.IndefR.Bridge.IsReps (Formalism.IndefR.Bridge.ratF V) (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) y →
    ∀ z : I → GA D V, (∀ i, (finHom V).rangeRestrict (z i) = y i) →
    ∀ ν : Measure (GinfC V), ν.IsHaarMeasure → ν Set.univ = 1 →
    ∀ Φ : GA D V → ℂ, IsContAut V Φ → (∀ κ ∈ Formalism.IndefR.Lev.levA V K, ∀ h, Φ (h * κ) = Φ h) →
      ∫ h in 𝓕, Φ h ∂μ = ∑ i, ((Nat.card (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.classGroupAt V K (y i)) : ℂ))⁻¹ * ∫ x : GinfC V, Φ (z i * x) ∂ν

theorem SplitPt.sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b := by
  have h : ∀ a, p.e * p.sec a = p.sec a := fun a => by rw [← p.sec_pr, p.pr_sec]
  have h2 := p.sec_pr (p.sec a * p.sec b)
  rwa [map_mul, p.pr_sec, p.pr_sec, ← mul_assoc, h] at h2

theorem SplitPt.sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  rw [← map_one p.pr, p.sec_pr, mul_one]

def SplitPt.idele (p : SplitPt D k) : kˣ →* (AE D)ˣ :=
  Units.map
    { toFun := fun a => 1 + p.sec (a - 1)
      map_one' := by rw [sub_self, map_zero, add_zero]
      map_mul' := fun a b => by
        rw [show a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) by ring, map_add, map_add, p.sec_mul]
        ring }

theorem SplitPt.idele_val (p : SplitPt D k) (a : kˣ) : (p.idele a : AE D) = 1 - p.e + p.sec a := by
  change 1 + p.sec (a - 1) = _
  rw [map_sub, p.sec_one]
  ring

theorem SplitPt.pr_idele (p : SplitPt D k) (a : kˣ) : p.pr (p.idele a) = a := by
  change p.pr (1 + p.sec (a - 1)) = _
  rw [map_add, map_one, p.pr_sec, add_sub_cancel]

def IsGlueConst (p : ι → SplitPt D k) (q : Unif k) (I : List ι) (N : ℕ) {r : ℕ} (μ : Fin r → ((AE D)ˣ →* Circle)) (c : ℂ) : Prop :=
  ∃ (a : ℤ) (m : Fin r → ℤ), c = (I.map fun i => ((resCard k : ℂ) ^ N - 1) * ((√(resCard k : ℝ) : ℝ) : ℂ) ^ a *
    ∏ j, ((μ j ((p i).idele (Units.mk0 _ q.ne_zero)) ^ m j : Circle) : ℂ)).prod

theorem IsGlueConst.norm {q : Unif k} {I : List ι} {N r : ℕ} {μ : Fin r → ((AE D)ˣ →* Circle)} {c : ℂ}
    (h : IsGlueConst p q I N μ c) :
    ∃ a : ℤ, ‖c‖ = (‖(resCard k : ℂ) ^ N - 1‖ * √(resCard k : ℝ) ^ a) ^ I.length := by
  obtain ⟨a, m, rfl⟩ := h
  refine ⟨a, ?_⟩
  induction I with
  | nil => simp
  | cons i I ih =>
    rw [List.map_cons, List.prod_cons, norm_mul, ih, List.length_cons, pow_succ', norm_mul, norm_mul, norm_prod]
    simp only [Circle.norm_coe, Finset.prod_const_one, mul_one, norm_zpow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]

theorem IsGlueConst.ne_zero {q : Unif k} {I : List ι} {N r : ℕ} {μ : Fin r → ((AE D)ˣ →* Circle)} {c : ℂ}
    (h : IsGlueConst p q I N μ c) (hN : 0 < N) : c ≠ 0 := by
  obtain ⟨a, ha⟩ := h.norm
  have h1 : 1 < resCard k := Finite.one_lt_card
  have h2 : (resCard k : ℂ) ^ N - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (Nat.one_lt_pow hN.ne' h1).ne'
  have h3 : 0 < √(resCard k : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast one_pos.trans h1)
  rw [← norm_pos_iff, ha]
  exact pow_pos (mul_pos (norm_pos_iff.2 h2) (zpow_pos h3 a)) _

variable (k) in

def sgnRes (s : ℤˣ) : 𝓀[k]ˣ := Units.map (Int.castRingHom 𝓀[k]).toMonoidHom s

theorem sgnRes_eq (s : ℤˣ) : sgnRes k s = 1 ∨ sgnRes k s = -1 := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (Units.ext (by simp [sgnRes]))

def ValueDoubleExact (D : D7) : Prop :=
  ∃ s : ℤˣ, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (χ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ i) 1), (∀ i, (p i).IsChar ψ (χ i)) →
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
      (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (Λ : DblLat B J B') (P : Pl D → Prop)
      (a : PairDat p B.A B.V₀ n') (b : MidDat p J.W₀ n) (a' : PairDat p B'.A B'.V₀ n''), DblShape s₁ s₂ Λ P q a b a' →
      ∀ I : List ι, I.Nodup → (∀ i, i ∈ I) → ∃ c c' : ℂ, c ≠ 0 ∧ c' ≠ 0 ∧
        IsGlueConst p q I (Fintype.card n) ![s₁.χV, s₁.χW, s₂.χV, s₂.χW] c ∧
        IsGlueConst p q I (Fintype.card n) ![s₁.χV, s₁.χW, s₂.χV, s₂.χW] c' ∧
        ∀ Ξ₁ Ξ₂, Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ P Ξ₁ → Vac ψ J.W₀ B'.V₀ Λ.M₁ Λ.M₂ P Ξ₂ →
        (∃ Ξ₁', OverAll ψ a.α₀ b.β Λ.M₀ Λ.M₁ (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) I Ξ₁ Ξ₁') ∧
        (∃ Ξ₂', OverAll ψ b.β a'.α₀ Λ.M₁ Λ.M₂ (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) I Ξ₂ Ξ₂') ∧
        ∀ Ξ₁' Ξ₂',
          OverAll ψ a.α₀ b.β Λ.M₀ Λ.M₁ (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) I Ξ₁ Ξ₁' →
          OverAll ψ b.β a'.α₀ Λ.M₁ Λ.M₂ (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) I Ξ₂ Ξ₂' →
          ∀ φ, a.Ram φ →
            hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ =
              c • hand0 s₁ s₂ l vL (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun _ => sgnRes k s) I φ) Ξ₁' Ξ₂' ∧
            hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ =
              c' • a'.sAll q (fun i => resChar (χ i) (hχ i) q) (fun _ => sgnRes k s) I (hand0 s₁ s₂ l vL φ Ξ₁' Ξ₂') ∧
            a'.Ram (hand0 s₁ s₂ l vL φ Ξ₁' Ξ₂') ∧ a'.Ram (hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂)

def ValueLastExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D)
    (B : BesLev D 0) (t : Last ψ T B) (o : OrthDec B.V B.A B.L), (∀ x, o.emb (x, 1) = embA B.d B.o x) →
    ∀ (a : PairDat p B.A B.V n') (b : MidDat p t.J.W n) (L₁ : Lat B.V) (L₂ : Lat t.J.W) (L₃ : Lat T),
      Function.Injective (fun i => (p i).v) → IsSelfDualC B.V L₁ → IsSelfDualC t.J.W L₂ → IsSelfDualC T L₃ →
      (∀ i, (p i).UnitAA ∧ ExtUnramAt D (p i).v ∧ UnrAt t.s (p i).v ∧ CharUnramAt D t.χS (p i).v ∧
        CharUnramAt D t.χT (p i).v ∧ IsSumFrame o B.ζ (a.α i) (a.α₀ i) ∧
        (a.α₀ i).IsLat L₁ (gluedS q 1 (a.P i).ker (a.P i).vec) ∧ (b.β i).IsLat L₂ (b.Q i).lat) →
      ∀ I : List ι, I.Nodup → (∀ i, i ∈ I) → ∃ c : ℂ, c ≠ 0 ∧ IsGlueConst p q I (Fintype.card n) ![t.s.χV, t.s.χW] c ∧
        ∀ Φ₁ Φ₂, Vac ψ B.V t.J.W L₁ L₂ (fun v => ∃ i, v = (p i).v) Φ₁ →
        Vac ψ t.J.W T L₂ L₃ (fun v => ∃ i, v = (p i).v) Φ₂ →
        (∃ Φ₁', OverAll ψ a.α₀ b.β L₁ L₂
          (fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (b.Q i))) I Φ₁ Φ₁') ∧
        ∀ Φ₁', OverAll ψ a.α₀ b.β L₁ L₂
            (fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (b.Q i))) I Φ₁ Φ₁' →
          ∀ φ, a.Ram φ → ∀ F, IsContAut T F →
            t.Q φ Φ₁ Φ₂ F = c * t.Q (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun _ => 1) I φ) Φ₁' Φ₂ F

theorem ValueDoubleExact.valueDouble (h : ValueDoubleExact D) : ValueDouble D := by
  obtain ⟨s, h⟩ := h
  intro k _ _ _ _ ι p q ψ χ hχ hp
  refine ⟨fun _ => sgnRes k s, fun _ => sgnRes_eq s, ?_⟩
  intro n n' n'' _ _ _ _ _ _ σ B J B' s₁ s₂ l vL Λ P a b a' hS I hI hI'
  obtain ⟨c, c', -, -, -, -, h'⟩ := h k ι p q ψ χ hχ hp n n' n'' σ B J B' s₁ s₂ l vL Λ P a b a' hS I hI hI'
  exact ⟨c, c', h'⟩

theorem ValueLastExact.valueLast (h : ValueLastExact D) : ValueLast D := by
  intro k _ _ _ _ ι p q χ hχ n n' _ _ _ _ ψ T B t o ho a b L₁ L₂ L₃ h1 h2 h3 h4 h5 I hI hI'
  obtain ⟨c, -, -, h'⟩ := h k ι p q χ hχ n n' ψ T B t o ho a b L₁ L₂ L₃ h1 h2 h3 h4 h5 I hI hI'
  exact ⟨c, h'⟩

def UnitLaw {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (s : Step ψ V V₀ W W₀ ρ σ) (dV : HypDec V V₀ ρ)
    (dW : HypDec W W₀ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀)
    (P : Pl D → Prop) : Prop :=
  ∀ Φ, Vac ψ V W LV LW P Φ → ∀ u' : UX D ρ, (∀ i j, (u'.1.1 - 1) i j ∈ idOff D P) →
    IsLatVac (heisO ψ V₀ W₀) (latO V₀ W₀ (LV₀ : Set _) (LW₀ : Set _) P)
      (fun w => flatFun ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 x y Φ w u') ∧
    ∀ u : UX D ρ, MxAt P (u.1.1 - 1) → ∀ w,
      (InK V LV P (dV.levi u.1) → flatFun ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 x y Φ w (u * u') =
        flatFun ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 x y Φ w u') ∧
      (¬ InK V LV P (dV.levi u.1) → flatFun ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 x y Φ w (u * u') = 0)

def FlatUnit (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop),
    (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W)
      (LW₀ : Lat J.W₀), (∀ v, P v → GoodBF ψ B J LV LV₀ LW LW₀ v) →
      UnitLaw s B.d J.d (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ)) LV LV₀ LW LW₀ P) ∧
    ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V)
      (LW₀ : Lat B.V₀), (∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v) →
      UnitLaw s J.d B.d (xLast B.d (vecB B.o B.ζ)) 0 LV LV₀ LW LW₀ P

example {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) (Φ w) :
    flatFB s Φ w = ∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Φ w u ∂s.vU.ν := rfl

example (q : Unif k) (i : ι) : IsGlueConst p q [i] 1 ![] ((resCard k : ℂ) - 1) := ⟨0, ![], by simp⟩

example (q : Unif k) (I : List ι) : ¬ IsGlueConst p q I 1 ![] 0 := fun h => h.ne_zero one_pos rfl

end GlobalTheory.FinPl

end
