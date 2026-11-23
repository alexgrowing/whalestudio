import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

def genE {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (y : Γ) : ChAlg g X :=
  ⟨(g y).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨y, rfl⟩)⟩

def XE {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) : ChAlg g X :=
  ⟨X, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩

def ConvMulSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type)
  [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)), IsTestM Φ₁ → IsTestM Φ₂ → ∀ f : ι → H E a b → ℂ,
  (∀ i, Continuous (f i)) →
  PositivityTheory.Rg.BcB.E.conv D.μ (mulM D.μ Φ₁ Φ₂) f = PositivityTheory.Rg.BcB.E.conv D.μ Φ₁ (PositivityTheory.Rg.BcB.E.conv D.μ Φ₂ f)

def FinSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E)
  (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E))),
  IsOpen (K₁ : Set (GL (Fin B.a) (Af E))) → IsCompact (K₁ : Set (GL (Fin B.a) (Af E))) →
  IsOpen (K₂ : Set (GL (Fin B.b) (Af E))) → IsCompact (K₂ : Set (GL (Fin B.b) (Af E))) →
  ∀ (cK : ℂ) (ψ₀ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)),
  cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1 →
  (∀ x y h, ψ₀ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0) →
  (∀ (A : Type) (f : A × B.κ → H E B.a B.b → ℂ), (∀ i, ∀ u ∈ K₁.prod K₂, ∀ x, f i (x * finH u) = f i x) →
    convF B.ν ψ₀ f = f ∧ ∀ ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), IsFinM ψ → convF B.ν (mulF B.ν ψ ψ₀) f = convF B.ν ψ f) ∧
  ∀ ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), IsFinM ψ →
    ∀ x y, ∀ u ∈ K₁.prod K₂, ∀ h, mulF B.ν ψ ψ₀ x y (h * u) = mulF B.ν ψ ψ₀ x y h

def RealiseSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (Γ : Type) [Countable Γ]
  (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ),
  (∀ x, (g x).Ok) → tX.Ok → X = tX.op → g a₀ = Sum.inr t₀ →
  (∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op)) →
  (∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) → IsSelfAdjoint X →
  (∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) → χ (genE g X a₀) ≠ 0 →
  ∃ (M : ℕ) (s : ℕ → ChAlg g X → ℂ) (f : ℕ → B.I → H E B.a B.b → ℂ),
    (∀ y, Tendsto (fun k => s k (genE g X y)) atTop (𝓝 (χ (genE g X y)))) ∧
    Tendsto (fun k => s k (XE g X)) atTop (𝓝 (χ (XE g X))) ∧
    ∀ k, s k (genE g X a₀) ≠ 0 ∧ (∀ i, Continuous (f k i)) ∧ f k ≠ 0 ∧ LeftInv (f k) ∧ WL2 B.D M (f k) ∧
      PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ (f k) = s k (genE g X a₀) • f k ∧
      (∀ y (t : PT B), g y = Sum.inr t → PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ t.Φ t₀.Φ) (f k) =
        (s k (genE g X y) * s k (genE g X a₀)) • f k) ∧
      PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ tX.Φ t₀.Φ) (f k) = (s k (XE g X) * s k (genE g X a₀)) • f k

end PositivityTheory.Rg.BcB.F.Rd.B

end
