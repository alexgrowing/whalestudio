import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GrowthWeightBounds.DescentOffTorusOfFrame
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.AllLeavesMono
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

open PositivityTheory.Rg.BcB.Desc PositivityTheory.AutomorphicGaloisHodgeTate.D

namespace PositivityTheory.Rg.BcB.F.FrE.FrameLocalData

attribute [local instance] borelG borelF borelA borelH GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Loc0Ok (π : CuspSub E n) (μ : HChar E) (Sec : Set (Pl E)) (d₀ : LocData E n)
    (τ : ∀ w : Pl E, SmIrr (GLw n w)) : Prop where
  hSec : IsSection Sec
  ok₀ : d₀.Ok
  T₀ : d₀.T = ∅
  Bad₀ : d₀.Bad = ∅
  μloc : ∀ w, d₀.μ w = μ.loc w
  unif : ∀ w, IsUnifAt (d₀.ϖ w) ∧ IsUnifV E w (d₀.ϖ w : w.adicCompletion E)
  S₀ : ∀ w ∈ d₀.S₀, w ∈ Sec ∧ IsSplitAt w
  good : ∀ w ∈ Sec, w ∉ d₀.S₀ → w ∉ d₀.Bad → (∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w
  K'_lev : ∀ w ∈ d₀.S₀, IsLevel (MonoidHom.id _) (KL n w) ((d₀.K' w).subgroupOf (UL n w))
  hτ : ∀ w, π.IsLocComp w (τ w)
  τ_fix : ∀ w ∈ d₀.S₀, ∃ y ∈ fixed (τ w).ρ (d₀.K' w), y ≠ 0

def WeightExD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : CuspSub E n, Hyp π → ∀ φ : E →+* ℂ, ∃ lam : DomWeight n, π.HasInfChar φ (infOfWeight lam)

def Loc0DEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : CuspSub E n, Hyp π → ∀ μ : HChar E, (∀ w : Pl E, ¬ IsSplitAt w → μ.UnrAt w) → (∀ᶠ w : Pl E in cofinite, μ.UnrAt w) →
    (∀ w : Pl E, IsOpen ((μ.loc w).ker : Set (w.adicCompletion E)ˣ)) →
    ∃ (Sec : Set (Pl E)) (d₀ : LocData E n) (τ : ∀ w : Pl E, SmIrr (GLw n w)), Loc0Ok π μ Sec d₀ τ

def ChainExD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : CuspSub E n, Hyp π → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ lam : InfinitePlace E → DomWeight n,
  (∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))) →
    ∃ (C : Chain μ e lam) (i₀ : C.ι), C.a i₀ = n ∧ C.c i₀ ≠ 0 ∧ ∀ i, i ≠ i₀ → 0 < C.a i ∧ C.a i < n

def ArchExD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : CuspSub E n, Hyp π → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ lam : InfinitePlace E → DomWeight n,
  (∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))) → ∀ (C : Chain μ e lam) (i₀ : C.ι) (a₀ : C.a i₀ = n),
  ∃ A : Arch E (C.a i₀) (n - C.a i₀) (C.l₁ i₀) (C.l₂ i₀) (C.μG (C.a i₀)) (C.μG (n - C.a i₀)) (C.νC (C.a i₀))
      (C.νC (n - C.a i₀)),
    A.Ma = (fun v => lefE _ (C.l₁ i₀ v).w) ∧ (∀ v, HEq (A.Ta v) (lefT _ (C.l₁ i₀ v).w)) ∧
    GrowthPiAt A.D (C.μG (C.a i₀)) (C.μG (n - C.a i₀)) (a₀.symm ▸ π)

def ArchExD' : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : CuspSub E n, Hyp π → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ lam : InfinitePlace E → DomWeight n,
  (∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))) → ∀ (C : Chain μ e lam) (i₀ : C.ι), C.a i₀ = n →
  ∀ D : Dom E (C.a i₀) (n - C.a i₀), (∀ F : H E (C.a i₀) (n - C.a i₀) → ℂ, Continuous F → HasCompactSupport F →
    ∫ x, F x ∂D.μ = ∫ x₁, ∫ x₂, F (x₁, x₂) ∂(C.μG (n - C.a i₀)) ∂(C.μG (C.a i₀))) →
  ∃ A : Arch E (C.a i₀) (n - C.a i₀) (C.l₁ i₀) (C.l₂ i₀) (C.μG (C.a i₀)) (C.μG (n - C.a i₀)) (C.νC (C.a i₀))
      (C.νC (n - C.a i₀)),
    A.D = D ∧ A.Ma = (fun v => lefE _ (C.l₁ i₀ v).w) ∧ ∀ v, HEq (A.Ta v) (lefT _ (C.l₁ i₀ v).w)

def LFixD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : CuspSub E n, Hyp π → ∀ (μ : HChar E) (Sec : Set (Pl E)) (d₀ : LocData E n) (τ : ∀ w : Pl E, SmIrr (GLw n w)),
    Loc0Ok π μ Sec d₀ τ → ∀ (a : ℕ) (ha : a = n),
    ∃ ψ ∈ (ha.symm ▸ π : CuspSub E a).V, ψ ≠ 0 ∧ ∀ k ∈ lev₁ Sec d₀ a, finRep E _ k ψ = ψ

end PositivityTheory.Rg.BcB.F.FrE.FrameLocalData

end
