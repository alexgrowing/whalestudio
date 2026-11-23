import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

section One
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def IsOne (Φ : SB (Matrix Y Y' k)) : Prop := Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1

def Place.IsCombAt (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    (c : WO S T →₀ ℂ) (Ξ : Matrix Y Y' k → ℂ) : Prop :=
  (∀ u ∈ c.support, IsHalf (p.e + cA D p.e) u) ∧
    ∀ Tm, p.IsModel ψ FS FT Tm → ∀ Φ₀ Φ, IsOne Φ₀ → Φ.1 = Ξ → Tm Φ = comb ψ S T c (Tm Φ₀)

def ofSplit (q : GlobalTheory.FinPl.SplitPt D k) : Place D k := ⟨q.e, q.split, q.pr, q.sec, q.pr_sec, q.sec_pr, q.cont_pr, q.cont_sec⟩

structure Dbl (p : Place D k) {σ : ℕ} (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (n₀ n₁ n₂ : Type)
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c : ℕ) where

  s : k
  s_ne : s ≠ 0

  F₀ : Frame k B.A.rank n₀
  F₁ : Frame k J.W₀.rank n₁
  F₂ : Frame k B'.A.rank n₂

  G₀ : Frame k B.V.rank (n₀ ⊕ Fin (c + 1 + 1 + 1))
  G₁ : Frame k J.W.rank (n₁ ⊕ Fin (c + 1 + 1))
  G₂ : Frame k B'.V.rank (n₂ ⊕ Fin (c + 1))
  bes : p.IsBesFrame B s F₀ G₀
  jac : p.IsJacFrame J s (p.hz B) F₁ G₁
  bes' : p.IsBesFrame B' (s * p.xi) F₂ G₂

end One

def LastLoc (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk →
  ∀ (ρ : ℕ) (B : BesLev D ρ) (S X T L'' : HSp D) (o'' : OrthDec X T L'') (τ : Matrix (Fin B.L.rank) (Fin L''.rank) D.host.E),
    L''.rank = 1 → τᴴ * (B.L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram →
  ∀ (s : k) (z₀ : Fin L''.rank → k), s ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * s)) • (fun i => p.pr (B.ζ i)) →
  ∀ (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z]
    (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FT : Frame k T.rank Z)
    (FX : Frame k X.rank (Z ⊕ Unit)), p.IsCoreFrame B s FA F₀ →
    FX.β = fromCols (o''.iA.map p.pr * FT.β) (Matrix.of fun r _ => (o''.iB.map p.pr *ᵥ z₀) r) →
  ∀ T₁ T₂, p.IsModel ψ F₀ FS T₁ → p.IsModel ψ FS FT T₂ →
    ∃ Λ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] (WO B.A S → WO S X → ℂ), p.IsBiModel ψ FA FS FX Λ ∧
      ∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k),
        (∀ q, Ξ.1 q = Ψ₂.1 q.2.toRows₁ *
          hat ψk ν (-1) (fun y => Ψ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) (q.2 (Sum.inr ()))) ∧
        ∀ u, (o''.boxT S (T₂ Ψ₂) fun w => T₁ Ψ₁ ((B.o.resS S).symm
          (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L S ((rat τ : Mx D B.L.rank L''.rank) * w)))) = Λ Ξ u

def GSupp1 (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s) (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J), p.IsComp s₁.χV⁻¹ (S.μ (j + 1)) →
  ∀ T₁, p.IsModel ψ F.G₀ F.G₁ T₁ → ∀ Φ₁, Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) →
  ∀ h, SuppAt p.e J.W h → flatBF s₁ (s₁.om (1, h) (T₁ Φ₁)) ≠ 0 →
    ∃ r ∈ jacGrp J.d, SuppAt p.e J.W r ∧ ∃ u uk, p.IsLoc F.G₁ u uk ∧ uk ∈ ((S.T t).lev (j + 1) (c + 1 + 1) (by omega)).J ∧ h = r * u

def GSupp2 (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s) (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank),
    p.IsComp s₂.χV⁻¹ (S.μ (j + 1 + 1)) →
  ∀ T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂, Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) →
    Φ₂.1 = (S.T t).Phi (j + 1) (c + 1) (by omega) →
  ∀ h, SuppAt p.e B'.V h → GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ Φ₁)) (flatFB s₂ (s₂.om (1, h) (T₂ Φ₂))) ≠ 0 →
    ∃ r ∈ besGrp B'.d B'.o, SuppAt p.e B'.V r ∧
      ∃ u uk, p.IsLoc F.G₂ u uk ∧ uk ∈ ((S.T t).lev (j + 1 + 1) (c + 1) (by omega)).J ∧ h = r * u

def GVal (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (p : Place D k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (c₁ : WO B.A J.W₀ →₀ ℂ) (c₂ : WO J.W₀ B'.A →₀ ℂ),
    p.IsCombAt ψ F.F₀ F.F₁ c₁ ((S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1) →
    p.IsCombAt ψ F.F₁ F.F₂ c₂ ((S.T t).entry S.ψ ν (j + 1) c H 1 1) →
  ∀ T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂,
    Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) → Φ₂.1 = (S.T t).Phi (j + 1) (c + 1) (by omega) → IsOne O₁ → IsOne O₂ →
    GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ Φ₁)) (flatFB s₂ (T₂ Φ₂)) =
      C • biComb ψ B.A J.W₀ B'.A c₁ c₂ (GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ O₁)) (flatFB s₂ (T₂ O₂)))

def GLast (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (p : Place D k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.IsChar ψ S.ψ →
  ∀ (ρ : ℕ) (B : BesLev D ρ) (W X T L'' : HSp D) (o'' : OrthDec X T L'') (τ : Matrix (Fin B.L.rank) (Fin L''.rank) D.host.E),
    L''.rank = 1 → τᴴ * (B.L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram →
  ∀ (a : k) (z₀ : Fin L''.rank → k), a ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * a)) • (fun i => p.pr (B.ζ i)) →
  ∀ (FA : Frame k B.A.rank (XIx (Fin κ) t s)) (F₀ : Frame k B.V₀.rank (XIx (Fin κ) t s ⊕ Unit)) (FS : Frame k W.rank (XIx (Fin κ) t (s + 1)))
    (FT : Frame k T.rank (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2))) (FX : Frame k X.rank (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit)),
    p.IsCoreFrame B a FA F₀ → FX.β = fromCols (o''.iA.map p.pr * FT.β) (Matrix.of fun r _ => (o''.iB.map p.pr *ᵥ z₀) r) →
  ∀ (c₁ : WO B.A W →₀ ℂ) (c₂ : WO W X →₀ ℂ), p.IsCombAt ψ FA FS c₁ (fun x₀ => (S.T t).Psi 1 x₀ (S.y0 t)) →
    p.IsCombAt ψ FS FX c₂ ((S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t))) →
  ∀ T₁ T₂, p.IsModel ψ F₀ FS T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₁ Φ₂ O₁ O₂,
    (∀ x, Φ₁.1 x = (S.T t).Psi 1 x.toCols₁ fun r => x r (Sum.inr ())) → (∀ x, Φ₂.1 x = (S.T t).PhiTop (fromCols x 0)) →
    IsOne O₁ → IsOne O₂ →
    (fun u => o''.boxT W (T₂ Φ₂) fun w => T₁ Φ₁ ((B.o.resS W).symm
        (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L W ((rat τ : Mx D B.L.rank L''.rank) * w)))) =
      biComb ψ B.A W X c₁ c₂ fun u => o''.boxT W (T₂ O₂) fun w => T₁ O₁ ((B.o.resS W).symm
        (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L W ((rat τ : Mx D B.L.rank L''.rank) * w)))

open Classical in

def GCore1 (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (p : Place D k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s) (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J) (C₀ : Frame k B.V₀.rank (XIx (Fin κ) t j ⊕ Unit)), p.IsCoreFrame B (F.s * (S.ϖ : k) ^ (σ + 1)) F.F₀ C₀ →
  ∀ T₁, p.IsModel ψ F.G₀ F.G₁ T₁ → ∃ T₀, p.IsModel ψ C₀ F.F₁ T₀ ∧ ∀ Φ₁ Ψ, Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) →
    (∀ x, Ψ.1 x = (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 x.toCols₁ * if ∀ r, x r (Sum.inr ()) ∈ 𝒪[k] then 1 else 0) →
    flatBF s₁ (T₁ Φ₁) = T₀ Ψ

open Classical in

def GCore2 (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (p : Place D k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s) (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t (j + 1 + 1)) c)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (C₂ : Frame k B'.V₀.rank (XIx (Fin κ) t (j + 1 + 1) ⊕ Unit)),
    p.IsCoreFrame B' (F.s * p.xi * (S.ϖ : k) ^ (σ + 1)) F.F₂ C₂ →
  ∀ T₂, p.IsModel ψ F.G₁ F.G₂ T₂ → ∃ T₀, p.IsModel ψ F.F₁ C₂ T₀ ∧ ∀ Φ₂ Ψ, Φ₂.1 = (S.T t).Phi (j + 1) (c + 1) (by omega) →
    (∀ x, Ψ.1 x = (S.T t).entry S.ψ ν (j + 1) c H 1 1 x.toRows₁ * if ∀ r, x (Sum.inr ()) r ∈ 𝒪[k] then 1 else 0) →
    flatFB s₂ (T₂ Φ₂) = T₀ Ψ

variable {D : D7} {u : D.what₂.Word}

def MovedTo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (g : GA D V) (β : GL (Fin V.rank) (Lev.EAf D))
    (M : Matrix (Fin V.rank) (Fin V.rank) k) : Prop :=
  ∀ b : Matrix (Fin V.rank) (Fin V.rank) (AE D), b.map (toEAf D) = β.val → (mt V g * b).map p.π = M

structure GAt (d : Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E)
    (PP : Formalism.L2.DIV.Pl D.host.E) where

  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]

  ν : Measure k
  unitVol : IsUnitVol ν

  q : GlobalTheory.FinPl.SplitPt D k
  idem : Formalism.L2.NTheta.IsIdemAt q.e PP
  unit : q.UnitAA

  s : ℕ
  hs : s + 1 + 1 = D.R.m

  S : SymData k s D.R.k
  char : (ofSplit q).IsChar d.c.ψ S.ψ
  mu : ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (d.c.chS j)⁻¹ (S.μ j)

  FX : ∀ j, j ≤ s + 1 → Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  FY : ∀ j c, j + c = s + 1 → Frame k (d.st j).V.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c)

  sc : ℕ → k
  sc_unit : ∀ j, valuation k (sc j) = 1
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit q).xi
  hz_unit : ∀ j ρ h, valuation k ((ofSplit q).hz (d.B j ρ h)) = 1
  bes : ∀ j ρ h c (hc : j + c = s + 1), (ofSplit q).IsBesFrame (d.B j ρ h) (sc j) (FX j (by omega)) (FY j c hc)
  jac : ∀ j ρ h c (hc : j + 1 + c = s + 1), (ofSplit q).IsJacFrame ((d.jac j ρ h).lev (d.x (j + 1)).vol) (sc j)
    ((ofSplit q).hz (d.B j ρ h)) (FX (j + 1) (by omega)) (FY (j + 1) c hc)

  z₀ : Fin d.Lz.rank → k
  last : FM.β = fromCols ((d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  tau : ∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * sc s)) • fun i => (ofSplit q).pr ((d.bes s 0 h).ζ i)
  latX : ∀ j hj (y : XIx (Fin D.R.k) (Fin D.R.t) j → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FX j hj).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X j) (d.x j).L (· = q.v)
  latM : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (d.x (s + 1 + 1)).L (· = q.v)
  frame : ∀ j c (hc : j + c = s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) j ≃ Fin (d.st j).V.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) (d.st j).V (d.t j) (d.st j).β
      (((FY j c hc).β * ((S.T (Fin D.R.t)).bas j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i))
  frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' 1 d.top.β (FT.β.submatrix id e.symm)

  cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  cg_mid : ∀ j c (H : j + 1 + c = s), (ofSplit q).IsCombAt d.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
    ((S.T (Fin D.R.t)).entry S.ψ ν j c H 1 1)
  cg_pen : (ofSplit q).IsCombAt d.c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
    fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
  cg_top : (ofSplit q).IsCombAt d.c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))

attribute [instance] GAt.fld GAt.val GAt.top GAt.loc GAt.mea GAt.bor

variable {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

def GAt.Red {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1

structure PinGBy (G : ∀ PP : d.c.Pg, GAt d τ PP.1) (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) : Prop where
  line : d.Lz.rank = 1
  norm : ∀ j h, (τ j h)ᴴ * ((d.bes j 0 h).L.gram * τ j h) = (-(D.host.xi0 * star D.host.xi0)) • d.Lz.gram
  grp : ∀ g : ∀ PP : d.c.Pg, GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1), g ∈ d.c.P.H ↔ ∀ PP, ∃ x, (G PP).Red x (g PP)
  chr : ∀ (g : d.c.P.H) (x : ∀ PP, (G PP).S.P.J), (∀ PP, (G PP).Red (x PP) (g.1 PP)) →
    d.c.P.chi g = ∏ PP, (G PP).S.P.lam (x PP)
  supp : ∀ j, ∀ w ∈ (cG j).support, GlobalTheory.FinPl.MxAt (· ∈ d.c.S) w
  prod : ∀ j, j < D.R.m → ∀ f, IsThetaFunO d.c.ψ _ _ f → comb d.c.ψ _ _ (cG j) f =
    d.c.Pg.attach.toList.foldr (fun PP f' => comb d.c.ψ _ _ ((G PP).cg j) f') f

variable (d τ) in

def PinG (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) : Prop := ∃ G, PinGBy (d := d) (τ := τ) G cG

def GAt.Vec {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP) : Prop :=
  (∀ j c (H : j + c = G.s) P, ∃ Tm, (ofSplit G.q).IsModel d.c.ψ (G.FY j (c + 1) (by omega)) (G.FY (j + 1) c (by omega)) Tm ∧
    ∀ Φ, Φ.1 = (G.S.T (Fin D.R.t)).Phi j c H → (d.p j).ω (d.t j, d.t (j + 1)) ((d.p j).pt P) = Tm Φ) ∧
  ∀ h P, ∃ Tm, (ofSplit G.q).IsModel d.c.ψ (G.FY (G.s + 1) 0 rfl) G.FT Tm ∧
    ∀ Φ, Φ.1 = (G.S.T (Fin D.R.t)).PhiTop → (d.pT G.s h).ω (d.t (G.s + 1), 1) ((d.pT G.s h).pt P) = Tm Φ

def GAt.Lev {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP) : Prop :=
  ∀ j c (hc : j + c = G.s + 1) x xk, (ofSplit G.q).IsLoc (G.FY j c hc) x xk → xk ∈ ((G.S.T (Fin D.R.t)).lev j c hc).J →
    (d.t j)⁻¹ * x * d.t j ∈ d.lev j

end GlobalTheory.LocMod
end
