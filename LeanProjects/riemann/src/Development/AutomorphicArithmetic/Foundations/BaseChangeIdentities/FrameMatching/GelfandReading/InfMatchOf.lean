import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdjKer0
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataExOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ActHecke
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GammaZetaNablaCancel

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF PositivityTheory.Rg.BcB.F.borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.BaseChangeIdentities.GelfandReading

def ChiOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (Pl E))
  (K : ∀ w : Pl E, Subgroup (GLw n w)) (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (G : GenIn π S T K W) (Q : Prop),
  G.c G.a₀ G.i₀ = 1 →
  (∀ (s : G.ι) (χ : Rd.ChAlg (fun x => G.g x s) (star ((G.β s).op ^ G.m) * (G.β s).op ^ G.m) →⋆ₐ[ℂ] ℂ),
    (∀ y, ‖χ y‖ ≤ ‖(y : (G.B s).Hb →L[ℂ] (G.B s).Hb)‖) →
    (∀ x, χ ⟨(G.g x s).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)⟩ = G.c x G.i₀) →
    χ ⟨star ((G.β s).op ^ G.m) * (G.β s).op ^ G.m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0 → Q) →
  GRead (H := G.H) G.gen G.βop G.m G.v Q

def PowNe : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (t : PT B) (m : ℕ) (A : Type)
  (F : A × B.κ → H E B.a B.b → ℂ) (U U' : Subgroup (Hf E B.a B.b)), t.Ok → IsOpen (U : Set (Hf E B.a B.b)) →
  IsOpen (U' : Set (Hf E B.a B.b)) → (∀ i, ∀ u ∈ U, ∀ x, F i (x * finH u) = F i x) →
  (∀ x y, ∀ u ∈ U', ∀ h, t.ψ x y (u * h) = t.ψ x y h) →
  convF B.ν (mulF B.ν (t.adj'.pw m).ψ (t.pw m).ψ) F ≠ 0 → (convF B.ν t.ψ)^[m + 1] F ≠ 0

def PowNeOf : Prop := BlockOperatorsProductAdjoint → BlockWordOperators → Tail.ConvMul → PowNe

def InfMatch : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (χ χ' : InfinitePlace E → Inf a),
  (∀ v s m, 1 ≤ m → 0 < a → GlobalTheory.Dec.gelfVal (χ v s) m = GlobalTheory.Dec.gelfVal (χ' v s) m) → mOf χ = mOf χ'

def InfMatchOf : Prop := gamma_zeta_nabla_cancel.GelfInj → InfMatch

def FmLev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w) (L : LM κ B.a B.b), IsSection S → L.Ok P →
  ∃ U : Subgroup (Hf E B.a B.b), IsOpen (U : Set (Hf E B.a B.b)) ∧ ∀ x y, ∀ u ∈ U, ∀ h, fm S P B e L x y (u * h) = fm S P B e L x y h

def FmLevOf : Prop := FinConv → FmLev

def DerVal : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (μa : Measure (PositivityTheory.RgTw.G a)) (μb : Measure (PositivityTheory.RgTw.G b))
  (A : Arch E a b l₁ l₂ μ₁ μ₂ μa μb) (κ : Type) [Fintype κ] (ψ ψ' : Matrix κ κ (Hf E a b → ℂ)) (r r' : ℝ) (v : InfinitePlace E)
  (s : Bool) (k : ℕ) (χa : InfinitePlace E → Inf a) (χb : InfinitePlace E → Inf b),
  (A.pt (fun v' => if v' = v then [(s, k)] else []) (fun _ => []) ψ r).val χa χb =
      GlobalTheory.Dec.gelfVal (χa v s) k * (A.pt (fun _ => []) (fun _ => []) ψ' r').val χa χb ∧
    (A.pt (fun _ => []) (fun v' => if v' = v then [(s, k)] else []) ψ r).val χa χb =
      GlobalTheory.Dec.gelfVal (χb v s) k * (A.pt (fun _ => []) (fun _ => []) ψ' r').val χa χb

def BetaInv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n), ∀ w ∈ d.P, ∀ x y,
  ∀ u ∈ d.lev a w, ∀ g, (d.betaL a ha).m w x y (u * g) = (d.betaL a ha).m w x y g ∧
    (d.betaL a ha).m w x y (g * u) = (d.betaL a ha).m w x y g

def BetaInvOf : Prop := (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) → BetaInv

def LocT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n) (μ : HChar E) (s₁ : Tr E a) (s₂ : Tr E (n - a))
  (Pa : Pre E a) (Pb : Pre E (n - a)) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D → ∀ w ∈ d.T, ∀ (m : ℕ) (G : d.kap w → H E a (n - a) → ℂ),
  1 ≤ m → Module.finrank ℂ ↥(fixed (pairAt Pa Pb w) (I2 a (n - a) w)) ≤ m →
  (∀ y, G y ∈ pairSpace s₁.space s₂.space ∧ G y ∈ fixed (pairRt a (n - a) w) (d.lev a w)) →
  (locM w ((d.betaL a ha).m w))^[m] G ≠ 0 →
  ∃ (s : Finset (Fin (n / 2))) (h : LocData.admitted n a s) (ξa : Fin a → ℂˣ) (ξb : Fin (n - a) → ℂˣ), JEig Pa Pb w (d.ϖ w) ξa ξb ∧
    ((d.c w).sum fun x t => t * (-qh w) ^ (-vRes n a (lOf x) s) * ev2 w ξa ξb (restr x _ h.2.1) (restr x _ h.2.2)) ≠ 0

def LocTOf : Prop := LocPow → ReadT → LocT

def LocS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n) (μ : HChar E) (s₁ : Tr E a) (s₂ : Tr E (n - a))
  (Pa : Pre E a) (Pb : Pre E (n - a)) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D → ∀ w ∈ d.S₀, d.μ w = μ.loc w →
  ∀ (m : ℕ) (G : d.kap w → H E a (n - a) → ℂ) (P : SmIrr (GLw n w)),
  (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) → IsEmpty (τ.ρ.Equiv P.ρ) →
    ∀ y ∈ fixed τ.ρ (d.K' w), hk τ.ρ (d.K' w) (d.e w) y = 0) →
  Module.finrank ℂ ↥(fixed (prodAt D w) (d.K' w)) < m →
  (∀ y, G y ∈ pairSpace s₁.space s₂.space ∧ G y ∈ fixed (pairRt a (n - a) w) (d.lev a w)) →
  (locM w ((d.betaL a ha).m w))^[m] G ≠ 0 → GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w)

def LocSOf : Prop := LocPow → ReadS → LocS

def CjUniq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (w : Pl E) (s : w.adicCompletion E →+* w.adicCompletion E)
  (ϖ : w.adicCompletion E) (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) →
  IsUnramInv ϖ s q → s = cj w

def LevGood : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ), a + b = n → ∀ (μ : HChar E) (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b)
  (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D → ∀ (w : Pl E) (G : H E a b → ℂ), μ.UnrAt w → G ∈ pairSpace s₁.space s₂.space → G ≠ 0 →
  G ∈ fixed (pairRt a b w) (K2 a b w) → GlobalTheory.LGrp.IsSpherical (prodAt D w) (GlobalTheory.LFun.KGL w n)

def LevGoodOf : Prop := ReadLev → LevGood

def LevConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (μ : HChar E) (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b)
  (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D → ∀ (w u : Pl E) (K : Subgroup (GLw n u)) (L : Subgroup (GLw a w × GLw b w)) (G : H E a b → ℂ),
  IsOpen (K : Set (GLw n u)) → IsCompact (K : Set (GLw n u)) →
  (∀ m X, blk h u m X ∈ K → μ.loc u (GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) = 1 ∧
    ∃ m' ∈ L, embW a u m.1 = embT a w m'.1 ∧ embW b u m.2 = embT b w m'.2) →
  G ∈ pairSpace s₁.space s₂.space → G ≠ 0 → HasLev G → G ∈ fixed (pairRtT a b w) L → GlobalTheory.LGrp.IsSpherical (prodAt D u) K

def LevConjOf : Prop := ReadLev → LevConj

end UpperTheory.BaseChangeIdentities.GelfandReading

end
