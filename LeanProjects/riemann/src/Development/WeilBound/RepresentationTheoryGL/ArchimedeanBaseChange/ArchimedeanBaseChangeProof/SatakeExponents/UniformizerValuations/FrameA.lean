import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.GlobalComplexCoefficients

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

abbrev borelA (E : Type) [Field E] [NumberField E] (n : ℕ) : MeasurableSpace (GA E n) := borel _

attribute [local instance] borelG borelF borelA

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Chain (μ : HChar E) (e : InfinitePlace E → ℤ) (lam : InfinitePlace E → DomWeight n) : Type 1 where
  ι : Type
  [ft : Fintype ι]
  [ne : Nonempty ι]
  a : ι → ℕ
  l₁ : ∀ i, InfinitePlace E → DomWeight (a i)
  l₂ : ∀ i, InfinitePlace E → DomWeight (n - a i)
  le : ∀ i, a i ≤ n
  inf : ∀ i v, (infOfWeight (l₁ i v)).map (· + ((n - a i : ℕ) : ℂ) * (e v : ℂ) / 2) +
    (infOfWeight (l₂ i v)).map (· + (a i : ℂ) * (e v : ℂ) / 2) = infOfWeight (lam v)
  μG : ∀ a, Measure (GA E a)
  hG : ∀ a, (μG a).IsHaarMeasure
  νC : ∀ a, Measure (G a)
  hC : ∀ a, (νC a).IsHaarMeasure
  c : ι → ℂ
  eq : ∀ S : Set (Pl E), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → GlobalTheory.BCT.IsTest (KL n) K' f →
    ∀ (u₁ : ∀ a, GL (Fin a) E) (u₂ : ∀ a, GL (Fin (n - a)) E), (∀ a, IsTransl (u₁ a) ∧ IsTransl (u₂ a)) →
    ∀ (φ₁ φ₂ : ∀ a (w : Pl E), GLw a w × GLw (n - a) w → ℂ),
    (∀ a ≤ n, IsTestP (φ₁ a) ∧ IsTestP (φ₂ a) ∧ IsTestP (seen (φ₁ a) (φ₂ a)) ∧
      ∀ w ∈ S, Match n a (n - a) w (μ.loc w) (f w) (seen (φ₁ a) (φ₂ a) w)) →
    (∀ i, ∃ w ∈ S, RegAt2 (a i) (n - a i) w (seen (φ₁ (a i)) (φ₂ (a i)) w)) →
    ∀ (val : ι → InfinitePlace E → ℂ) (ψ : ∀ i, InfinitePlace E → GL (Fin (a i)) ℂ × GL (Fin (n - a i)) ℂ → ℂ),
    (∀ i v, LefAt (νC (a i)) (νC (n - a i)) (l₁ i v) (l₂ i v) (val i v) (ψ i v)) → ∀ z : ℂ, (∀ i, ∏ v, val i v = z) →
    z * geomU S lam f = ∑ i, c i *
      ellSum2 (μG (a i)) (μG (n - a i)) (adel S (u₁ (a i)) (u₂ (a i)) (ψ i) (φ₁ (a i)) (φ₂ (a i)))

attribute [instance] Chain.ft Chain.ne

structure Arch (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a)
    (l₂ : InfinitePlace E → DomWeight b) (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (μa : Measure (G a))
    (μb : Measure (G b)) : Type 1 where
  D : Dom E a b
  Ma : Mods E a
  Mb : Mods E b
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
  growth : ∀ (κ : Type) [Fintype κ], GrowthAt (⟨a, b, D, Ma, Mb, κ, μa, μb, ν, ha, hb, hν, hν', compat, c, c_nonneg, ca, cb⟩ : Block E) μ₁ μ₂
  Ta : Ops Ma
  Tb : Ops Mb
  vca : ∀ v k val T, IsMult μa (Ma v) k val T → VeryCusp (phiOf (Ma v) (Ta v) k)
  vcb : ∀ v k val T, IsMult μb (Mb v) k val T → VeryCusp (phiOf (Mb v) (Tb v) k)
  lef : ∀ v k k' val val' T, IsMult μa (Ma v) k val T → IsMult μb (Mb v) k' val' T →
    LefAt μa μb (l₁ v) (l₂ v) (val (infOf (l₁ v).w) * val' (infOf (l₂ v).w))
      fun y => phiOf (Ma v) (Ta v) k y.1 * phiOf (Mb v) (Tb v) k' y.2
  bump : ℝ → ℝ
  T : ℝ
  T_nonneg : 0 ≤ T
  isBump : IsBump bump T
  ka : List (Bool × ℕ) → Kers Ma
  kb : List (Bool × ℕ) → Kers Mb
  kera : ∀ w v, IsKer μa (Ma v) w bump (ka w v)
  kerb : ∀ w v, IsKer μb (Mb v) w bump (kb w v)
  one : (∏ v, coshT bump (cas (infOf (l₁ v).w))) * ∏ v, coshT bump (cas (infOf (l₂ v).w)) = 1

namespace Arch

variable {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b} {μ₁ : Measure (GA E a)}
  {μ₂ : Measure (GA E b)} {μa : Measure (G a)} {μb : Measure (G b)} (A : Arch E a b l₁ l₂ μ₁ μ₂ μa μb)

abbrev blk (κ : Type) [Fintype κ] : Block E :=
  ⟨a, b, A.D, A.Ma, A.Mb, κ, μa, μb, A.ν, A.ha, A.hb, A.hν, A.hν', A.compat, A.c, A.c_nonneg, A.ca, A.cb⟩

def valW {m : ℕ} (w : List (Bool × ℕ)) (χ : Inf m) : ℂ := zVal w χ * coshT A.bump (cas χ)

def χa (_ : Arch E a b l₁ l₂ μ₁ μ₂ μa μb) : InfinitePlace E → Inf a := fun v => infOf (l₁ v).w

def χb (_ : Arch E a b l₁ l₂ μ₁ μ₂ μa μb) : InfinitePlace E → Inf b := fun v => infOf (l₂ v).w

def pt {κ : Type} [Fintype κ] (wa wb : InfinitePlace E → List (Bool × ℕ)) (ψ : Matrix κ κ (Hf E a b → ℂ)) (r : ℝ) :
    PT (A.blk κ) :=
  ⟨fun v => A.ka (wa v) v, fun v => A.kb (wb v) v, fun v => A.valW (wa v), fun v => A.valW (wb v), A.T, ψ, r⟩

end Arch

def sizeOf {a b : ℕ} {κ : Type} (ψ : Matrix κ κ (Hf E a b → ℂ)) : ℝ :=
  if h : ∃ r, 0 ≤ r ∧ ∀ x y g, ψ x y g ≠ 0 → logSize (finGL E a g.1) ≤ r ∧ logSize (finGL E b g.2) ≤ r then h.choose else 0

def ChainEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ lam : InfinitePlace E → DomWeight n, Nonempty (Chain μ e lam)

def ArchEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ)
  (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b))
  (μa : Measure (G a)) (μb : Measure (G b)), μ₁.IsHaarMeasure → μ₂.IsHaarMeasure → μa.IsHaarMeasure → μb.IsHaarMeasure →
  Nonempty (Arch E a b l₁ l₂ μ₁ μ₂ μa μb)

end PositivityTheory.Rg.BcB.F

end
