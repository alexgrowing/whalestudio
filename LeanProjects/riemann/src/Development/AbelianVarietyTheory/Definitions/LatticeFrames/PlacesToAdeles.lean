import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.FinPl

variable {D : D7}

section Ops

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def formAt (β : Frame p S n) (P : Pair k n) (φ₀ : GA D S → ℂ) : Form k n (GA D S → ℂ) :=
  fun P₁ => β.rep (Classical.epsilon fun g : GL n k => g • P = P₁) φ₀

def sOp (β : Frame p S n) (P : Pair k n) (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (φ₀ : GA D S → ℂ) : GA D S → ℂ :=
  dia ε (FFStar q χ (formAt β P φ₀)) P

def diaAt (β : Frame p S n) (P : Pair k n) (s : 𝓀[k]ˣ) (φ₀ : GA D S → ℂ) : GA D S → ℂ := dia s (formAt β P φ₀) P

def Frame.IsLatMoved (β : Frame p S n) (g : GA D S) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)) : Prop :=
  ∀ x : n → k, x ∈ Λ ↔ mt S g⁻¹ *ᵥ (fun i => p.sec ((β.b *ᵥ x) i)) ∈ latV S L (· = p.v)

end Ops

def UnrAt {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (s : Step ψ V V₀ W W₀ ρ σ) (v : Pl D) : Prop :=
  CharUnramAt D s.χV v ∧ CharUnramAt D s.χW v

def FlatLaws (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop),
    (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J), IsFlatBF s P (flatBF s)) ∧
    ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), IsFlatFB s P (flatFB s)

def OneCosetBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V)
    (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v →
    ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f →
      Vac ψ B.V₀ J.W₀ LV₀ LW₀ (· = v) (𝔉 f) ∧
      ∀ h ∈ grpAt J.W (· = v), 𝔉 (s.om (1, h) f) ≠ 0 →
        ∃ r ∈ jacGrp J.d, r ∈ grpAt J.W (· = v) ∧ ∃ κ, InK J.W LW (· = v) κ ∧ h = r * κ

def OrbitSplit (D : D7) : Prop :=
  ∀ (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (v : Pl D), Tame D v → IsSelfDualC B.V₀ L₀ → SplitCore B L₀ v →
    ∀ γ ∈ grpAt B.V₀ (· = v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = v) →
        mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = v)) →
      ∃ a ∈ grpAt B.A (· = v), ∃ κ, InK B.V₀ L₀ (· = v) κ ∧ γ = B.o.emb (a, 1) * κ

def OrbitGlued (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n)
    (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P →
    ∀ γ ∈ grpAt B.V₀ (· = p.v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) →
        mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) →
      (∃ a ∈ grpAt B.A (· = p.v), ∃ κ, InK B.V₀ L₀ (· = p.v) κ ∧ γ = B.o.emb (a, 1) * κ) ∨
      ∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsLattice k),
        β₀.IsLatMoved γ L₀ (lastKer Λ) ∨ β₀.IsLatMoved γ L₀ (lastPair q Λ).lat

def SourceGlued (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ₀ : AddChar k Circle)
    (hχ : HasConductor χ₀ 1) (χ : AddChar 𝓀[k] ℂ), χ = resChar χ₀ hχ q →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ →
    CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    CharUnramAt D χS p.v → CharUnramAt D χT p.v →
    ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ →
    ∀ (P P₁ : Pair k n') (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsLattice k],
      (∃ c : ℂ, ∀ (LS : Lat S) (LT : Lat T) (f₀ Ξ : WO S T → ℂ) (Ξ' : Pair k n → WO S T → ℂ),
        Over ψ α₀ β LS LT f₀ (latInd (gluedS q 1 P.ker P.vec) Λ) Ξ →
        (∀ Q ∈ withLat Λ, Over ψ α₀ β LS LT f₀ (tensCol (phiOne P₁ Q) (charInd χ Q)) (Ξ' Q)) →
        ∀ φ, IsRam α φ → liftA o om vA (φ P) Ξ = c • ∑ Q ∈ withLat Λ, liftA o om vA (FFStar q χ φ P₁) (Ξ' Q)) ∧
      ∀ (LS : Lat S) (LT : Lat T) (f₀ Ξ : WO S T → ℂ) (a : (n → k) → ℂ),
        (Over ψ α₀ β LS LT f₀ (tensCol (latInd P.lat Λ) a) Ξ ∨ Over ψ α₀ β LS LT f₀ (tensCol (latInd P.ker Λ) a) Ξ) →
        ∀ φ, IsRam α φ → liftA o om vA (φ P) Ξ = 0

def Contraction (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ →
    ∃ ε : k, (ε = 1 ∨ ε = -1) ∧
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
      (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
      (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'')
      (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ →
      ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀)
        (f₁ Ξ₁ Ξ₁' : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ Ξ₂' : WO J.W₀ B'.V₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (Ψ₂ : Matrix n'' n k → ℂ)
        (a a' b b' : (n → k) → ℂ), a ∈ SB (n → k) → a' ∈ SB (n → k) → b ∈ SB (n → k) → b' ∈ SB (n → k) →
        Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ₁ → Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a') Ξ₁' →
        Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ₂ → Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b') Ξ₂' →
        ∀ φ, IsContAut B.A φ →
          (∫ η, (∫ y, a' y * (χ (ε * (η ⬝ᵥ y)) : ℂ) ∂μ) * b' η ∂μ) • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ =
            (∫ η, (∫ y, a y * (χ (ε * (η ⬝ᵥ y)) : ℂ) ∂μ) * b η ∂μ) • hand0 s₁ s₂ l vL φ Ξ₁' Ξ₂'

def VertexGlued (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ →
    ∃ ε : 𝓀[k]ˣ, (ε = 1 ∨ ε = -1) ∧
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
      (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), UnrAt s₁ p.v → UnrAt s₂ p.v →
      ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'')
        (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ →
      ∀ (P P₁ : Pair k n') (Q : Pair k n),
        (∀ R : Pair k n'', ∃ c : ℂ, ∀ (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀)
          (f₁ Ξ₁ Ξ₁' : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ Ξ₂' : WO J.W₀ B'.V₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Ξ₁ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P₁ Q) (vecInd Q.lat)) Ξ₁' →
          Over ψ β γ₀ L₂' L₃ f₂ (latInd Q.lat (gluedS q 1 R.ker R.vec)) Ξ₂ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow (phiOne Q R) (dualInd Q.lat)) Ξ₂' →
          ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ =
            c • hand0 s₁ s₂ l vL (dia ε (FFStar q (resChar χ hχ q) φ) P₁) Ξ₁' Ξ₂') ∧
        ∀ (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k] (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀)
          (f₁ Ξ₁ : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ : WO J.W₀ B'.V₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Ξ₁ →
          (Over ψ β γ₀ L₂' L₃ f₂ (latInd Q.lat (lastKer Λ)) Ξ₂ ∨ Over ψ β γ₀ L₂' L₃ f₂ (latInd Q.lat (lastPair q Λ).lat) Ξ₂) →
          ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = 0

def Commutation (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (q : Unif k) (χ₀ : AddChar k Circle)
    (hχ : HasConductor χ₀ 1) (χ : AddChar 𝓀[k] ℂ), χ = resChar χ₀ hχ q → ∀ (ε : 𝓀[k]ˣ) (ψ : AddChar (AF D.host.F) ℂ)
    (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
    (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), UnrAt s₁ p.v → UnrAt s₂ p.v →
    ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'')
      (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ →
    ∀ (P : Pair k n') (Q : Pair k n) (R : Pair k n''), ∃ c : ℂ, c ≠ 0 ∧
      ∀ (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀) (f₁ Ξ₁ : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ : WO J.W₀ B'.V₀ → ℂ),
        Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P Q) (vecInd Q.lat)) Ξ₁ →
        Over ψ β γ₀ L₂' L₃ f₂ (tensRow (phiOne Q R) (dualInd Q.lat)) Ξ₂ →
        ∀ φ₀, RamAt α P φ₀ → RamAt γ R (hand0 s₁ s₂ l vL φ₀ Ξ₁ Ξ₂) ∧
          (∀ s, hand0 s₁ s₂ l vL (diaAt α P s φ₀) Ξ₁ Ξ₂ = diaAt γ R s (hand0 s₁ s₂ l vL φ₀ Ξ₁ Ξ₂)) ∧
          hand0 s₁ s₂ l vL (sOp α P q χ ε φ₀) Ξ₁ Ξ₂ = c • sOp γ R q χ ε (hand0 s₁ s₂ l vL φ₀ Ξ₁ Ξ₂)

def LastGlued (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ₀ : AddChar k Circle)
    (hχ : HasConductor χ₀ 1) (χ : AddChar 𝓀[k] ℂ), χ = resChar χ₀ hχ q →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D) (B : BesLev D 0) (t : Last ψ T B), UnrAt t.s p.v →
    CharUnramAt D t.χS p.v → CharUnramAt D t.χT p.v → ExtUnramAt D p.v →
    ∀ o : OrthDec B.V B.A B.L, (∀ a, o.emb (a, 1) = embA B.d B.o a) →
    ∀ (α : Frame p B.A n') (α₀ : Frame p B.V (n' ⊕ Fin 1)) (β : Frame p t.J.W n), IsSumFrame o B.ζ α α₀ →
    ∀ (P P₁ : Pair k n') (Q : Pair k n), ∃ c : ℂ,
      ∀ (L₁ : Lat B.V) (L₂ L₂' : Lat t.J.W) (L₃ : Lat T) (f₁ Φ₁ Φ₁' : WO B.V t.J.W → ℂ) (Φ₂ : WO t.J.W T → ℂ),
        Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Φ₁ →
        Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P₁ Q) (charInd χ Q)) Φ₁' →
        IsSelfDualC t.J.W L₂' → IsSelfDualC T L₃ → β.IsLat L₂' Q.lat → Vac ψ t.J.W T L₂' L₃ (· = p.v) Φ₂ →
        ∀ φ, IsRam α φ → ∀ F, IsContAut T F → t.Q (φ P) Φ₁ Φ₂ F = c * t.Q (FFStar q χ φ P₁) Φ₁' Φ₂ F

def RamBijective (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ₀ : AddChar k Circle)
    (hχ : HasConductor χ₀ 1) (χ : AddChar 𝓀[k] ℂ), χ = resChar χ₀ hχ q → ∀ (ε : 𝓀[k]ˣ) (S : HSp D)
    (β : Frame p S n) (P : Pair k n),
      Set.BijOn (sOp β P q χ ε) {φ₀ | RamAt β P φ₀} {φ₀ | RamAt β P φ₀} ∧
      (∀ φ, IsRam β φ → IsRam β (dia ε (FFStar q χ φ)) ∧ sOp β P q χ ε (φ P) = dia ε (FFStar q χ φ) P) ∧
      ∃ c c' : GL n k →₀ ℂ, (∀ φ₀, sOp β P q χ ε φ₀ = c.sum fun g a => a • β.rep g φ₀) ∧
        ∀ φ₀, RamAt β P φ₀ → sOp β P q χ ε (c'.sum fun g a => a • β.rep g φ₀) = φ₀ ∧
          RamAt β P (c'.sum fun g a => a • β.rep g φ₀)

def OverBasic (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ),
    IsStdChar D ψ (-1) → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T),
    IsSelfDualC S LS → IsSelfDualC T LT → ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ →
      (∀ Ψ ∈ SB (Matrix n n' k), ∃! f, Over ψ α β LS LT f₀ Ψ f) ∧
      (∀ Ψ f, Over ψ α β LS LT f₀ Ψ f → IsThetaFunO ψ S T f ∧
        ∀ (MS : Lat S) (MT : Lat T) (P : Pl D → Prop), ¬ P p.v → Vac ψ S T MS MT P f₀ → Vac ψ S T MS MT P f) ∧
      (p.UnitAA → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT →
        Over ψ α β LS LT f₀ (latInd ΛS ΛT) f₀)

def PlacesToAdeles (D : D7) : Prop :=
  ∀ (S : HSp D) (L : Lat S) (P : Pl D → Prop), IsSelfDualC S L →
    ∀ R : Subgroup (GA D S), ∀ h : GA D S,
      (∀ v, P v → ∃ hv ∈ grpAt S (· = v), ∃ h' ∈ grpOff S (· = v), h = hv * h' ∧
        ∃ r ∈ R, r ∈ grpAt S (· = v) ∧ ∃ κ, InK S L (· = v) κ ∧ hv = r * κ) →
      ∃ r ∈ R, r ∈ grpAt S P ∧ ∃ g ∈ grpOff S P, ∃ κ, InK S L P κ ∧ h = r * g * κ

end GlobalTheory.FinPl

end
