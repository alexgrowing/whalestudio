import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.CutTrDZero

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

abbrev borelG (n : ℕ) : MeasurableSpace (G n) := borel _

abbrev borelF (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : MeasurableSpace (Hf E a b) := borel _

attribute [local instance] borelG borelF borelH

structure Block (E : Type) [Field E] [NumberField E] [IsCMField E] : Type 1 where
  a : ℕ
  b : ℕ
  D : Dom E a b
  Ma : Mods E a
  Mb : Mods E b
  κ : Type
  [ft : Fintype κ]
  μa : Measure (G a)
  μb : Measure (G b)
  ν : Measure (Hf E a b)
  ha : μa.IsHaarMeasure
  hb : μb.IsHaarMeasure
  hν : ν.IsHaarMeasure
  hν' : ν.IsMulRightInvariant
  compat : Compat D μa μb ν
  c : ℝ
  c_nonneg : 0 ≤ c
  ca : ∀ g h : GA E a, logSize (g * h) ≤ logSize g + logSize h + c
  cb : ∀ g h : GA E b, logSize (g * h) ≤ logSize g + logSize h + c

attribute [instance] Block.ft

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hsComplete {a b : ℕ} {ι : Type} [Fintype ι] (D : Dom E a b) : CompleteSpace (Hs (ι := ι) D) := inferInstance

namespace Block

variable (B : Block E)

abbrev I : Type := Io B.Ma B.Mb B.κ

abbrev Hb : Type := Hs (ι := B.I) B.D

instance : Fintype B.I := inferInstance

instance : NormedAddCommGroup B.Hb := inferInstance

instance : InnerProductSpace ℂ B.Hb := inferInstance

instance : CompleteSpace B.Hb := hsComplete B.D

def opOf (Φ : Matrix B.I B.I (H E B.a B.b → ℂ)) : B.Hb →L[ℂ] B.Hb := if h : ∃ T, IsROp B.D Φ T then h.choose else 0

end Block

structure PT (B : Block E) where
  ka : Kers B.Ma
  kb : Kers B.Mb
  va : InfinitePlace E → Inf B.a → ℂ
  vb : InfinitePlace E → Inf B.b → ℂ
  T : ℝ
  ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)
  r : ℝ

def adjVal {n : ℕ} (μ : Measure (G n)) {M : Mods E n} (k : Kers M) (val : InfinitePlace E → Inf n → ℂ) (T : ℝ) :
    InfinitePlace E → Inf n → ℂ := fun v =>
  if h : ∃ val₁, IsMult μ (M v) (adjK k v) val₁ T ∧ ∀ χ, IsHerm χ → val₁ χ = starRingEnd ℂ (val v χ) then h.choose else 0

namespace PT

variable {B : Block E}

structure Ok (t : PT B) : Prop where
  T : 0 ≤ t.T
  r : 0 ≤ t.r
  ka : IsMults B.μa t.ka t.va t.T
  kb : IsMults B.μb t.kb t.vb t.T
  ψ : IsFinM t.ψ
  size : ∀ x y h, t.ψ x y h ≠ 0 → logSize (finGL E B.a h.1) ≤ t.r ∧ logSize (finGL E B.b h.2) ≤ t.r

def Φ (t : PT B) : Matrix B.I B.I (H E B.a B.b → ℂ) := tens t.ka t.kb t.ψ

def op (t : PT B) : B.Hb →L[ℂ] B.Hb := B.opOf t.Φ

def mul (t t' : PT B) : PT B :=
  ⟨convK B.μa t.ka t'.ka, convK B.μb t.kb t'.kb, t.va * t'.va, t.vb * t'.vb, t.T + t'.T, mulF B.ν t.ψ t'.ψ, t.r + t'.r + B.c⟩

def adj (t : PT B) : PT B :=
  ⟨adjK t.ka, adjK t.kb, adjVal B.μa t.ka t.va t.T, adjVal B.μb t.kb t.vb t.T, t.T, adjF t.ψ, t.r⟩

def val (t : PT B) (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) : ℂ := valA t.va χa * valA t.vb χb

end PT

abbrev BGen (B : Block E) : Type := ℂ ⊕ PT B

namespace BGen

variable {B : Block E}

def Ok : BGen B → Prop := Sum.elim (fun _ => True) PT.Ok

def op : BGen B → (B.Hb →L[ℂ] B.Hb) := Sum.elim (fun c => c • 1) PT.op

def adj : BGen B → BGen B := Sum.map (starRingEnd ℂ) PT.adj

def sc (w : List (BGen B)) : ℂ := (w.map (Sum.elim id fun _ => 1)).prod

def wd (w : List (BGen B)) (t₀ : PT B) : PT B := w.foldr (fun g t => Sum.elim (fun _ => t) (fun s => s.mul t) g) t₀

end BGen

def BlockOperatorsProductAdjoint : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (t t' : PT B), t.Ok → t'.Ok →
  IsTestM t.Φ ∧ IsROp B.D t.Φ t.op ∧ (t.mul t').Ok ∧ (t.mul t').op = t.op * t'.op ∧ t.adj.Ok ∧ t.adj.op = ContinuousLinearMap.adjoint t.op ∧
    (∀ χa χb, (t.mul t').val χa χb = t.val χa χb * t'.val χa χb) ∧
    ∀ χa χb, (∀ v, IsHerm (χa v)) → (∀ v, IsHerm (χb v)) → t.adj.val χa χb = starRingEnd ℂ (t.val χa χb)

def BlockPureTensorsCommute : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (t t' : PT B), t.Ok → t'.Ok →
  mulF B.ν t.ψ t'.ψ = mulF B.ν t'.ψ t.ψ → Commute t.op t'.op

def BlockWordOperators : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (w : List (BGen B)) (t₀ : PT B) (R : ℝ),
  (∀ g ∈ w, g.Ok) → t₀.Ok → 0 ≤ R → (∀ s, Sum.inr s ∈ w → s.T ≤ R ∧ s.r + B.c ≤ R) →
  (BGen.wd w t₀).Ok ∧ (w.map BGen.op).prod * t₀.op = BGen.sc w • (BGen.wd w t₀).op ∧
    (BGen.wd w t₀).T ≤ t₀.T + w.length * R ∧ (BGen.wd w t₀).r ≤ t₀.r + w.length * R ∧
    (∀ g : BGen B, g.Ok → g.adj.Ok ∧ g.adj.op = ContinuousLinearMap.adjoint g.op) ∧
    ∀ χa χb, (BGen.wd w t₀).val χa χb = (w.map (Sum.elim (fun _ => 1) fun s => s.val χa χb)).prod * t₀.val χa χb

def BlockLinearCombinations : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι J : Type) [Fintype ι]
  (s : Finset J) (c : J → ℂ) (Φ : J → Matrix ι ι (H E a b → ℂ)) (T : J → (Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D)),
  (∀ j ∈ s, IsTestM (Φ j) ∧ IsROp D (Φ j) (T j)) →
  IsTestM (∑ j ∈ s, c j • Φ j) ∧ IsROp D (∑ j ∈ s, c j • Φ j) (∑ j ∈ s, c j • T j)

def BlockProductLevels : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E)
  (ψ ψ' ψ'' : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)), IsFinM ψ → IsFinM ψ' → IsFinM ψ'' →
  (∀ u, (∀ x y h, ψ x y (u * h) = ψ x y h) → ∀ x y h, mulF B.ν ψ ψ' x y (u * h) = mulF B.ν ψ ψ' x y h) ∧
  (∀ u, (∀ x y h, ψ' x y (h * u) = ψ' x y h) → ∀ x y h, mulF B.ν ψ ψ' x y (h * u) = mulF B.ν ψ ψ' x y h) ∧
  mulF B.ν (mulF B.ν ψ ψ') ψ'' = mulF B.ν ψ (mulF B.ν ψ' ψ'') ∧ adjF (mulF B.ν ψ ψ') = mulF B.ν (adjF ψ') (adjF ψ)

def wdVal {A Γ : Type} [Monoid A] [Star A] (gen : Γ → A) (w : List (Γ × Bool)) : A :=
  (w.map fun p => if p.2 then star (gen p.1) else gen p.1).prod

def AdjWords : Prop := ∀ (A Γ : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (gen : Γ → A),
  ∀ a ∈ StarAlgebra.adjoin ℂ (Set.range gen), ∃ (J : Type) (_ : Fintype J) (c : J → ℂ) (w : J → List (Γ × Bool)) (L : ℕ),
    (∀ j, (w j).length ≤ L) ∧ a = ∑ j, c j • wdVal gen (w j) ∧
      ∀ k : ℕ, a ^ k = ∑ f : Fin k → J, (∏ i, c (f i)) • wdVal gen (List.ofFn fun i => w (f i)).flatten

def BlockEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (Ma : Mods E a)
  (Mb : Mods E b) (κ : Type) [Fintype κ] (μa : Measure (G a)) (μb : Measure (G b)), μa.IsHaarMeasure → μb.IsHaarMeasure →
  ∃ ν ha hb hν hν' hc c h0 ca cb, (⟨a, b, D, Ma, Mb, κ, μa, μb, ν, ha, hb, hν, hν', hc, c, h0, ca, cb⟩ : Block E).c = c

end PositivityTheory.Rg.BcB.F

end
