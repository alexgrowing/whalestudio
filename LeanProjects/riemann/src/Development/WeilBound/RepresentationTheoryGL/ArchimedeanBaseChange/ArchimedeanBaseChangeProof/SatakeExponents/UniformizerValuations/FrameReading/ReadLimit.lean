import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GlobalTheory
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue

noncomputable section

set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def gOps {B : Block E} {Γ : Type} (g : Γ → BGen B) : Set (B.Hb →L[ℂ] B.Hb) := Set.range fun x => (g x).op

abbrev ChAlg {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) :=
  StarAlgebra.adjoin ℂ (gOps g ∪ {X})

def InfLim : Prop := ∀ (n : ℕ) (x : ℕ → Fin n → ℂ) (t : ℕ → ℂ),
  (∀ m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (x k) m) atTop (𝓝 (t m))) → ∃ y : Fin n → ℂ, ∀ m, GlobalTheory.Dec.gelfVal y m = t m

def OpDet : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
  (Φ Φ' : Matrix ι ι (H E a b → ℂ)) (T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (f : ι → H E a b → ℂ),
  IsTestM Φ → IsTestM Φ' → IsROp D Φ T → IsROp D Φ' T → (∀ i, Continuous (f i)) → LeftInv f →
  PositivityTheory.Rg.BcB.E.conv D.μ Φ f = PositivityTheory.Rg.BcB.E.conv D.μ Φ' f

def FinType {B : Block E} (t₀ t : PT B) : Prop := t.ka = t₀.ka ∧ t.kb = t₀.kb ∧ t.va = t₀.va ∧ t.vb = t₀.vb ∧ t.T = t₀.T

def ArchType {B : Block E} (t₀ t : PT B) : Prop := t.ψ = t₀.ψ

structure BlockOut (B : Block E) {Γ : Type} (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (jX : ℕ)
    (χ : ChAlg g X →⋆ₐ[ℂ] ℂ) (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (W₁ : Submodule ℂ (Kinf E B.a → ℂ)) (W₂ : Submodule ℂ (Kinf E B.b → ℂ))
    (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω₁ Ω₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) where
  s₁ : Tr E B.a
  s₂ : Tr E B.b
  F : B.I → H E B.a B.b → ℂ
  χa : InfinitePlace E → Inf B.a
  χb : InfinitePlace E → Inf B.b
  good₁ : s₁.Good
  good₂ : s₂.Good
  untw₁ : s₁.Untw
  untw₂ : s₂.Untw
  leaves₁ : s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₁ M, ∃ W' ∈ Ω₁ M, HasType K' W' V)
  leaves₂ : s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₂ M, ∃ W' ∈ Ω₂ M, HasType K' W' V)
  inf₁ : ∀ τ, HasInfCharGL s₁.space τ (mOf χa τ)
  inf₂ : ∀ τ, HasInfCharGL s₂.space τ (mOf χb τ)
  herm : (∀ v, IsHerm (χa v)) ∧ ∀ v, IsHerm (χb v)
  ne : F ≠ 0
  mem : ∀ i, F i ∈ pairSpace s₁.space s₂.space
  type : ∀ i, TypeH K₁ K₂ W₁ W₂ (F i)
  eigFin : ∀ (x : Γ) (t : PT B), g x = Sum.inr t → FinType t₀ t →
    (letI : MeasurableSpace (Hf E B.a B.b) := PositivityTheory.Rg.BcB.F.borelF E B.a B.b; convF B.ν t.ψ F) = (χ ⟨(g x).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)⟩ /
      χ ⟨(g a₀).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a₀, rfl⟩)⟩) • F
  eigArch : ∀ (x : Γ) (t : PT B), g x = Sum.inr t → ArchType t₀ t →
    χ ⟨(g x).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)⟩ = t.val χa χb
  eigX :
    (letI : MeasurableSpace (Hf E B.a B.b) := PositivityTheory.Rg.BcB.F.borelF E B.a B.b; convF B.ν tX.ψ F) =
      (χ ⟨X, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ /
        χ ⟨(g a₀).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a₀, rfl⟩)⟩ ^ jX) • F

def ReadLimit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
  ∃ (Wf₁ : ∀ a b : ℕ, Mods E a → Mods E b → Submodule ℂ (Kinf E a → ℂ))
    (Wf₂ : ∀ a b : ℕ, Mods E a → Mods E b → Submodule ℂ (Kinf E b → ℂ))
    (Ωf₁ Ωf₂ : ∀ a b : ℕ, Mods E a → Mods E b → ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (Θf₁ Θf₂ : ∀ a b : ℕ, Mods E a → Mods E b → Subgroup (GL (Fin a) (Af E)) → Subgroup (GL (Fin b) (Af E)) → ∀ M : ℕ,
      Set (Subgroup (GL (Fin M) (Af E)))),
  (∀ a b Ma Mb, FiniteDimensional ℂ (Wf₁ a b Ma Mb) ∧ FiniteDimensional ℂ (Wf₂ a b Ma Mb) ∧
    KTypes E (Ωf₁ a b Ma Mb) ∧ KTypes E (Ωf₂ a b Ma Mb) ∧ (∀ M, (Ωf₁ a b Ma Mb M).Nonempty ∧ (Ωf₂ a b Ma Mb M).Nonempty) ∧
    Wf₁ a b Ma Mb ≠ ⊥ ∧ Wf₂ a b Ma Mb ≠ ⊥) ∧
  (∀ a b Ma Mb (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))), IsOpen (K₁ : Set (GL (Fin a) (Af E))) →
    IsOpen (K₂ : Set (GL (Fin b) (Af E))) → Levels E (Θf₁ a b Ma Mb K₁ K₂) ∧ Levels E (Θf₂ a b Ma Mb K₁ K₂)) ∧
  ∀ (B : Block E) (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E))),
  IsOpen (K₁ : Set (GL (Fin B.a) (Af E))) → IsCompact (K₁ : Set (GL (Fin B.a) (Af E))) →
  IsOpen (K₂ : Set (GL (Fin B.b) (Af E))) → IsCompact (K₂ : Set (GL (Fin B.b) (Af E))) →
  ∀ (Γ : Type) [Countable Γ] (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (bump : ℝ → ℝ) (cK : ℂ)
    (der : InfinitePlace E → Bool → ℕ → Γ × Γ) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (jX : ℕ) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ),
    0 < B.a + B.b →
    (∀ x, (g x).Ok) → tX.Ok → X = tX.op → (∀ χa' χb', tX.val χa' χb' = t₀.val χa' χb' ^ jX) → g a₀ = Sum.inr t₀ → IsBump bump t₀.T →
    (∀ x (t : PT B), g x = Sum.inr t → FinType t₀ t ∨ ArchType t₀ t) →
    (∀ v, IsKer B.μa (B.Ma v) [] bump (t₀.ka v)) → (∀ v, IsKer B.μb (B.Mb v) [] bump (t₀.kb v)) →
    cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1 →
    (∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0) →
    (∀ v s m, 1 ≤ m → 0 < B.a → ∃ ta : PT B, g (der v s m).1 = Sum.inr ta ∧
      ArchType t₀ ta ∧ ta.kb = t₀.kb ∧ IsKer B.μa (B.Ma v) [(s, m)] bump (ta.ka v) ∧ (∀ v', v' ≠ v → ta.ka v' = t₀.ka v')) →
    (∀ v s m, 1 ≤ m → 0 < B.b → ∃ tb : PT B, g (der v s m).2 = Sum.inr tb ∧
      ArchType t₀ tb ∧ tb.ka = t₀.ka ∧ IsKer B.μb (B.Mb v) [(s, m)] bump (tb.kb v) ∧ (∀ v', v' ≠ v → tb.kb v' = t₀.kb v')) →
    (∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op)) →
    (∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) → IsSelfAdjoint X →
    (∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) →
    χ ⟨(g a₀).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a₀, rfl⟩)⟩ ≠ 0 →
    (∀ (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b),
      (∀ v s m, 1 ≤ m → 0 < B.a → GlobalTheory.Dec.gelfVal (χa v s) m =
        χ ⟨(g (der v s m).1).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨_, rfl⟩)⟩ /
          χ ⟨(g a₀).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a₀, rfl⟩)⟩) →
      (∀ v s m, 1 ≤ m → 0 < B.b → GlobalTheory.Dec.gelfVal (χb v s) m =
        χ ⟨(g (der v s m).2).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨_, rfl⟩)⟩ /
          χ ⟨(g a₀).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a₀, rfl⟩)⟩) →
      RealSym (mOf χa) ∧ RealSym (mOf χb) ∧ ∀ τ, GapM (mOf χa τ) ∧ GapM (mOf χb τ)) →
    Nonempty (BlockOut B g a₀ t₀ X tX jX χ K₁ K₂ (Wf₁ B.a B.b B.Ma B.Mb) (Wf₂ B.a B.b B.Ma B.Mb)
      (Θf₁ B.a B.b B.Ma B.Mb K₁ K₂) (Θf₂ B.a B.b B.Ma B.Mb K₁ K₂) (Ωf₁ B.a B.b B.Ma B.Mb) (Ωf₂ B.a B.b B.Ma B.Mb))

end PositivityTheory.Rg.BcB.F.Rd

end
