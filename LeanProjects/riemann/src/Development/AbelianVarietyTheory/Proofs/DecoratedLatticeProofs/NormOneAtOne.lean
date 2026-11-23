import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel

namespace GlobalTheory.Core.Mi

variable {D : D7}

structure SBes.FrameAt {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) (μ lam : D.host.E) : Prop where
  ne : μ ≠ 0
  sign : lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)
  e : B.d.e = GlobalTheory.Core.SBesEx.eM X h μ lam
  e' : B.d.e' = GlobalTheory.Core.SBesEx.e'M X h μ lam
  z : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY X h (X.zu u)

def SBes.FrameTied {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) : Prop :=
  ∃ μ lam, B.FrameAt μ lam

namespace LatMatch

def NormOneAt (v : GlobalTheory.FinPl.Pl D) (c : AE D) : Prop := c * cA D c = 1 ∧ c - 1 ∈ idAt D (· = v)

def CenAt (S : HSp D) (v : GlobalTheory.FinPl.Pl D) (a : GA D S) : Prop := a ∈ grpAt S (· = v) ∧ a ∈ Subgroup.center (GA D S)

def SMoves (S : HSp D) (c : AE D) (g : GA D S) (L M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV S L (· = v) ↔ c • (Formalism.L2.Theta.mt S g *ᵥ y) ∈ latV S M (· = v))

def LastAt (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S)
    (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ i : Fin ρ, i.1 + 1 = ρ → ∀ s ∈ idAt D (· = v),
    (∀ a : AE D, a ∈ idAt D (· = v) → a • ratV z ∈ latV S₀ M (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) ↔
      ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1

def coreLat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) : Lat S₀ :=
  L.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))

theorem mem_coreLat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (x : Fin S₀.rank → D.host.E) :
    x ∈ coreLat d L ↔ d.i₀ *ᵥ x ∈ L := Iff.rfl

abbrev latS (D : D7) : Lat (D.sp.Y 0) := Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0

abbrev lat0 {u : D.what₂.Word} (F : Formalism.L2.Forms.Forms0 D u) : Lat (D.sp.X 0) :=
  F.cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E
    (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))

def LineAt {S : HSp D} (z : Fin S.rank → D.host.E) (μ : D.host.E) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV z ∈ latV S M (· = v) ↔ incA D μ * a ∈ intAt D (· = v)

def SplitsAt {S A L : HSp D} (o : OrthDec S A L) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV S M (· = v) ↔ o.jA *ᵥ (o.pA *ᵥ y) ∈ latV S M (· = v) ∧ o.jB *ᵥ (o.pB *ᵥ y) ∈ latV S M (· = v))

def TraceAt {S A L : HSp D} (o : OrthDec S A L) (g : GA D A) (N : Lat A) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin A.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV A N (· = v) ↔ o.jA *ᵥ (Formalism.L2.Theta.mt A g *ᵥ y) ∈ latV S M (· = v))

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def atW (p : SplitPt D k) {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin m) (Fin n) k :=
  x.map fun a => p.pr (incA D a)

def WShape (p : SplitPt D k) {S S₀ A Ln : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln)
    (ζ : Fin Ln.rank → D.host.E) (L : Lat S) (α α' : Fin ρ → k) (γ : k) (g : GA D A) (N : Lat A) : Prop :=
  ∀ (x x' : Fin ρ → k) (t : k) (y : Fin A.rank → k),
    (fun r => p.sec ((atW p d.e *ᵥ x + atW p d.e' *ᵥ x' + t • (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A g).map p.pr *ᵥ y)) r)) ∈ latV S L (· = p.v) ↔
      (∀ a, α a * x a ∈ 𝒪[k]) ∧ (∀ a, α' a * x' a ∈ 𝒪[k]) ∧ γ * t ∈ 𝒪[k] ∧ (fun r => p.sec (y r)) ∈ latV A N (· = p.v)

def GluedW {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1))
    (M : Lat S) (q : GlobalTheory.LatPair.Unif k) (m : k) (P : GlobalTheory.LatPair.Pair k n) : Prop :=
  ∀ x : n ⊕ Fin 1 → k, (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV S M (· = p.v) ↔
    Sum.elim (fun a => x (Sum.inl a)) (fun j => m * x (Sum.inr j)) ∈ GlobalTheory.LatPair.gluedS q 1 P.ker P.vec

end Split

theorem normOneAt_one (v : GlobalTheory.FinPl.Pl D) : NormOneAt v (1 : AE D) := ⟨by simp, by simp⟩

theorem sMoves_one {S : HSp D} (g : GA D S) (L M : Lat S) (v : GlobalTheory.FinPl.Pl D) : SMoves S 1 g L M v ↔ Moves S g L M (· = v) := by
  simp only [SMoves, Moves, one_smul]

end LatMatch

end GlobalTheory.Core.Mi

end
