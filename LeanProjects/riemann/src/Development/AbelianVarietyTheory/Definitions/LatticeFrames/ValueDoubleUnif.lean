import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

def mono4 {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (a : (AE D)ˣ) (e : Fin 4 → ℤ) : ℂ :=
  chrPow s₁.χV a (e 0) * chrPow s₁.χW a (e 1) * chrPow s₂.χV a (e 2) * chrPow s₂.χW a (e 3)

def LinExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k)
    (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    ∃ lS lT : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧ (CharUnramAt D χS p.v → IsUnram lT) ∧
      (lS q.unit : ℂ) = (((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2) : ℝ) : ℂ) * chrPow χT (p.idele q.unit) (-1) ∧
      (lT q.unit : ℂ) = (((resCard k : ℝ) ^ ((S.rank : ℝ) / 2) : ℝ) : ℂ) * chrPow χS (p.idele q.unit) 1 ∧
      ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (α : Frame p S n') (β : Frame p T n) (LS : Lat S)
        (LT : Lat T) (f₀ : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ) (f : WO S T → ℂ), Over ψ α β LS LT f₀ Ψ f →
        ∀ (g : GL n' k) (h : GL n k), Over ψ α β LS LT f₀ (fun x => (lS (Matrix.GeneralLinearGroup.det g) : ℂ) *
          (lT (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ ((h⁻¹ : GL n k).val * x * g.val)) (om (α.gl g, β.gl h) f)

def SourceExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1), ∃ (r : ℝ) (e : ℤ), 0 < r ∧
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ →
    CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    CharUnramAt D χS p.v → CharUnramAt D χT p.v →
    ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ →
    ∀ (P : Pair k n') (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsLattice k] (LS : Lat S) (LT : Lat T) (f₀ Ξ : WO S T → ℂ)
      (Ξ' : Pair k n → WO S T → ℂ), Over ψ α₀ β LS LT f₀ (latInd (gluedS q 1 P.ker P.vec) Λ) Ξ →
      (∀ Q ∈ withLat Λ, Over ψ α₀ β LS LT f₀ (tensCol (phiOne P Q) (charInd (resChar χ hχ q) Q)) (Ξ' Q)) →
      ∀ φ, IsRam α φ → liftA o om vA (φ P) Ξ =
        ((r : ℂ) * chrPow χT (p.idele q.unit) e) • ∑ Q ∈ withLat Λ, liftA o om vA (FFStar q (resChar χ hχ q) φ P) (Ξ' Q)

def VertexExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ →
    ∃ ε : 𝓀[k]ˣ, (ε = 1 ∨ ε = -1) ∧
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''],
      ∃ (r : ℝ) (e : ℤ), 0 < r ∧ ∀ (P : Pair k n') (Q : Pair k n) (R : Pair k n'')
        (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
        (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), UnrAt s₁ p.v → UnrAt s₂ p.v →
      ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'')
        (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ →
      ∀ (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀)
          (f₁ Ξ₁ Ξ₁' : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ Ξ₂' : WO J.W₀ B'.V₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Ξ₁ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P Q) (vecInd Q.lat)) Ξ₁' →
          Over ψ β γ₀ L₂' L₃ f₂ (latInd Q.lat (gluedS q 1 R.ker R.vec)) Ξ₂ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow (phiOne Q R) (dualInd Q.lat)) Ξ₂' →
          ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ =
            ((r : ℂ) * chrPow s₁.χW (p.idele q.unit) e) •
              hand0 s₁ s₂ l vL (dia ε (FFStar q (resChar χ hχ q) φ) P) Ξ₁' Ξ₂'

def CommExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ →
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''],
    ∃ (r : ℝ) (e : Fin 4 → ℤ), 0 < r ∧
    ∀ (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
    (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), UnrAt s₁ p.v → UnrAt s₂ p.v →
    ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'')
      (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ →
    ∀ (P : Pair k n') (Q : Pair k n) (R : Pair k n'')
      (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀) (f₁ Ξ₁ : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ : WO J.W₀ B'.V₀ → ℂ),
        Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P Q) (vecInd Q.lat)) Ξ₁ →
        Over ψ β γ₀ L₂' L₃ f₂ (tensRow (phiOne Q R) (dualInd Q.lat)) Ξ₂ →
        ∀ φ₀, RamAt α P φ₀ → ∀ ε : 𝓀[k]ˣ, hand0 s₁ s₂ l vL (sOp α P q (resChar χ hχ q) ε φ₀) Ξ₁ Ξ₂ =
          ((r : ℂ) * mono4 s₁ s₂ (p.idele q.unit) e) • sOp γ R q (resChar χ hχ q) ε (hand0 s₁ s₂ l vL φ₀ Ξ₁ Ξ₂)

def LastExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1), ∃ (r : ℝ) (e : ℤ), 0 < r ∧ ∀ (P : Pair k n') (Q : Pair k n)
    (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D) (B : BesLev D 0) (t : Last ψ T B), UnrAt t.s p.v →
    CharUnramAt D t.χS p.v → CharUnramAt D t.χT p.v → ExtUnramAt D p.v →
    ∀ o : OrthDec B.V B.A B.L, (∀ a, o.emb (a, 1) = embA B.d B.o a) →
    ∀ (α : Frame p B.A n') (α₀ : Frame p B.V (n' ⊕ Fin 1)) (β : Frame p t.J.W n), IsSumFrame o B.ζ α α₀ →
      ∀ (L₁ : Lat B.V) (L₂ L₂' : Lat t.J.W) (L₃ : Lat T) (f₁ Φ₁ Φ₁' : WO B.V t.J.W → ℂ) (Φ₂ : WO t.J.W T → ℂ),
        Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Φ₁ →
        Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P Q) (charInd (resChar χ hχ q) Q)) Φ₁' →
        IsSelfDualC t.J.W L₂' → IsSelfDualC T L₃ → β.IsLat L₂' Q.lat → Vac ψ t.J.W T L₂' L₃ (· = p.v) Φ₂ →
        ∀ φ, IsRam α φ → ∀ F, IsContAut T F →
          t.Q (φ P) Φ₁ Φ₂ F = (r : ℂ) * chrPow t.s.χW (p.idele q.unit) e * t.Q (FFStar q (resChar χ hχ q) φ P) Φ₁' Φ₂ F

def ValueDoubleUnif (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (χ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ i) 1), (∀ i, (p i).IsChar ψ (χ i)) → ∃ ε : ι → 𝓀[k]ˣ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''],
      ∃ (r r' : ι → ℝ) (e : ι → ℤ) (e' : ι → Fin 4 → ℤ), (∀ i, 0 < r i ∧ 0 < r' i) ∧
    ∀ (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (Λ : DblLat B J B') (P : Pl D → Prop)
      (a : PairDat p B.A B.V₀ n') (b : MidDat p J.W₀ n) (a' : PairDat p B'.A B'.V₀ n''), DblShape s₁ s₂ Λ P q a b a' →
      ∀ I : List ι, I.Nodup → (∀ i, i ∈ I) →
        ∀ Ξ₁ Ξ₂, Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ P Ξ₁ → Vac ψ J.W₀ B'.V₀ Λ.M₁ Λ.M₂ P Ξ₂ → ∀ Ξ₁' Ξ₂',
          OverAll ψ a.α₀ b.β Λ.M₀ Λ.M₁ (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) I Ξ₁ Ξ₁' →
          OverAll ψ b.β a'.α₀ Λ.M₁ Λ.M₂ (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) I Ξ₂ Ξ₂' →
          ∀ φ, a.Ram φ →
            hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ = (I.map fun i => (r i : ℂ) * chrPow s₁.χW ((p i).idele q.unit) (e i)).prod •
              hand0 s₁ s₂ l vL (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I φ) Ξ₁' Ξ₂' ∧
            hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ = (I.map fun i => (r' i : ℂ) * mono4 s₁ s₂ ((p i).idele q.unit) (e' i)).prod •
              a'.sAll q (fun i => resChar (χ i) (hχ i) q) ε I (hand0 s₁ s₂ l vL φ Ξ₁' Ξ₂')

def ValueLastUnif (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'], ∃ (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D)
    (B : BesLev D 0) (t : Last ψ T B) (o : OrthDec B.V B.A B.L), (∀ x, o.emb (x, 1) = embA B.d B.o x) →
    ∀ (a : PairDat p B.A B.V n') (b : MidDat p t.J.W n) (L₁ : Lat B.V) (L₂ : Lat t.J.W) (L₃ : Lat T),
      Function.Injective (fun i => (p i).v) → IsSelfDualC B.V L₁ → IsSelfDualC t.J.W L₂ → IsSelfDualC T L₃ →
      (∀ i, (p i).UnitAA ∧ ExtUnramAt D (p i).v ∧ UnrAt t.s (p i).v ∧ CharUnramAt D t.χS (p i).v ∧
        CharUnramAt D t.χT (p i).v ∧ IsSumFrame o B.ζ (a.α i) (a.α₀ i) ∧
        (a.α₀ i).IsLat L₁ (gluedS q 1 (a.P i).ker (a.P i).vec) ∧ (b.β i).IsLat L₂ (b.Q i).lat) →
      ∀ I : List ι, I.Nodup → (∀ i, i ∈ I) →
        ∀ Φ₁ Φ₂, Vac ψ B.V t.J.W L₁ L₂ (fun v => ∃ i, v = (p i).v) Φ₁ →
        Vac ψ t.J.W T L₂ L₃ (fun v => ∃ i, v = (p i).v) Φ₂ →
        ∀ Φ₁', OverAll ψ a.α₀ b.β L₁ L₂
            (fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (b.Q i))) I Φ₁ Φ₁' →
          ∀ φ, a.Ram φ → ∀ F, IsContAut T F →
            t.Q φ Φ₁ Φ₂ F = (I.map fun i => (r i : ℂ) * chrPow t.s.χW ((p i).idele q.unit) (e i)).prod *
              t.Q (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun _ => 1) I φ) Φ₁' Φ₂ F

def CollapseBoth : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ G₂ R J : Subgroup G),
    IsClosed (G₁ : Set G) → IsClosed (G₂ : Set G) → IsClosed (R : Set G) → (∀ x ∈ G₁, ∀ y ∈ G₂, x * y = y * x) →
    IsHomeomorph (fun x : G₁ × G₂ => (x.1 : G) * x.2) → (∀ r ∈ R, ∃ x ∈ R ⊓ G₁, ∃ y ∈ R ⊓ G₂, r = x * y) →
    J ≤ G₂ → IsCompact (J : Set G) → IsOpen ((J.subgroupOf G₂ : Subgroup G₂) : Set G₂) →
    ∀ (μG : Measure G) (μR : Measure R) (μ₁ : Measure G₁) (ν₁ : Measure (R.subgroupOf G₁)), μG.IsHaarMeasure →
      μR.IsHaarMeasure → μR.IsMulRightInvariant → μ₁.IsHaarMeasure → ν₁.IsHaarMeasure →
      ∃ c : ℝ, 0 < c ∧ ∀ f : G → ℂ, (∀ g, ∀ j ∈ J, f (g * j) = f g) → (∀ r ∈ R ⊓ G₂, ∀ g, f (r * g) = f g) →
        (∀ g, f g ≠ 0 → ∃ r ∈ R, ∃ x ∈ G₁, ∃ j ∈ J, g = r * x * j) →
        ∀ z₁ : ℂ, IsQuotIntL1 ν₁ μ₁ (fun x : G₁ => f x) z₁ ↔ IsQuotIntL1 μR μG f (c * z₁)

def HandInv (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ),
    IsThetaFunO ψ B.V J.W Φ₁ → IsThetaFunO ψ J.W B'.V Φ₂ → ∀ φ, IsContAut B.A φ → ∀ g h₁ h₂,
      (∀ r ∈ jacGrp J.d, Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g (r * h₁) h₂ = Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) ∧
      ∀ G, IsContAut B'.V G → ∀ r ∈ besGrp B'.d B'.o,
        B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (r * h₂)) (rTrans (r * h₂) G) =
          B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) (rTrans h₂ G)

end GlobalTheory.FinPl

end
