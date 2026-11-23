import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FGLeaf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GammaZetaNablaCancel

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def GoodL : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n a : ℕ) (ha : a ≤ n)
  (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ (Sec : Set (Pl E)), IsSection Sec → ∀ d : LocData E n, d.Ok → (↑d.P : Set (Pl E)) ⊆ Sec → (∀ w, d.μ w = μ.loc w) →
  (∀ w, IsUnifV E w (d.ϖ w : w.adicCompletion E)) → (∀ w ∈ Sec, w ∉ d.S₀ → w ∉ d.Bad → μ.UnrAt w) →
  ∀ (σ : ∀ w : Pl E, SmIrr (UL n w)), (∀ w ∈ Sec, IsCompU π w (σ w) ∧ fixed (σ w).ρ (d.KU w) ≠ ⊥) →
  ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight (n - a)) (μ₁ : Measure (GA E a))
    (μ₂ : Measure (GA E (n - a))) (μa : Measure (PositivityTheory.RgTw.G a)) (μb : Measure (PositivityTheory.RgTw.G (n - a)))
    (A : Arch E a (n - a) l₁ l₂ μ₁ μ₂ μa μb) (s₁ : Tr E a) (s₂ : Tr E (n - a)) (Pa : Pre E a) (Pb : Pre E (n - a)) (D : Pre E n),
  Ctx μ s₁ s₂ Pa Pb D → IsLev (d.lev a) → IsLev (d.lev₂ a) →
  ∀ (I : Type) (G : I × (∀ w : d.P, d.kap w) → H E a (n - a) → ℂ), G ≠ 0 →
  (∀ j, G j ∈ pairSpace s₁.space s₂.space) → (∀ j, OfLev Sec (d.lev a) (d.lev₂ a) (G j)) →
  (∀ w ∈ Sec, d.Good w → ∀ (k : ℕ) (intersection_update_fsHerm_neg_one : Bool),
    convF A.ν (fm Sec d.P (A.blk (∀ w : d.P, d.kap w)) (Equiv.refl _) (d.hL a ha w k intersection_update_fsHerm_neg_one)) G =
      twTr (σ w).ρ (KL n w) (KL n w) (d.hU w k) LinearMap.id • G) →
  ∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w

def WeightL : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ (lam : InfinitePlace E → DomWeight n), (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ (a b : ℕ)
    (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b),
  (∀ v, (infOfWeight (l₁ v)).map (· + (b : ℂ) * (e v : ℂ) / 2) + (infOfWeight (l₂ v)).map (· + (a : ℂ) * (e v : ℂ) / 2) =
    infOfWeight (lam v)) →
  ∀ (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
  (∀ τ, HasInfCharGL s₁.space τ (mOf (fun v => PositivityTheory.RgBcC.infOf (l₁ v).w) τ)) →
  (∀ τ, HasInfCharGL s₂.space τ (mOf (fun v => PositivityTheory.RgBcC.infOf (l₂ v).w) τ)) →
  (∃ G ∈ pairSpace s₁.space s₂.space, G ≠ 0) → ∀ τ lam', HasWeightAt π τ lam' → ∑ j, D.m j τ = infOfWeight lam'

def GoodLOf : Prop := ReadSplit → FmOne → ActHecke → LocOk → ConjFix → USat → CtHecke → GoodL

def WeightLOf : Prop := InfTree → gamma_zeta_nabla_cancel.RegDom → JoinInf → TreeInf → WeightJoin → WeightL

end PositivityTheory.Rg.BcB.F.FG

end
