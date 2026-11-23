import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.EqVolSDOf

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

def Rescale : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (t : E), cc t = t →
    (∀ τ ∈ X.Ψ, 0 < (τ t).re) →
    ∃ Y : Data E r, Y.Ψ = X.Ψ ∧ Y.p0 = X.p0 ∧ Y.Gm = t • X.Gm ∧ Y.Γ = X.Γ ∧
      (∀ Γ Γ', SameOrbits X Γ Γ' → SameOrbits Y Γ Γ') ∧
      ∀ x FF, IsOrth X x → IsFundSet X x FF →
        ∃ y FF', IsOrth Y y ∧ IsFundSet Y y FF' ∧ muF Y y FF' = muF X x FF

def LevelIdeal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)) (𝔪 𝔪' : Ideal (𝓞 E)) (M A : ℕ)
    (γ : Matrix (Fin N) (Fin N) E), IsLat Λ → 0 < M → 𝔪' * 𝔪 = Ideal.span {(M : 𝓞 E)} → (∀ x ∈ Λ, γ *ᵥ x ∈ Λ) →
    (((∀ x ∈ 𝔪 • Λ, ∃ e ∈ Λ, γ *ᵥ x = x + M • e) ∧ ∀ x ∈ Λ, ∃ e ∈ Λ, γ *ᵥ x = x + A • e) ↔
      ∀ x ∈ Λ, γ *ᵥ x - x ∈ (𝔪' ⊓ Ideal.span {(A : 𝓞 E)}) • Λ)

def EqVolTr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (r : ℕ) (X X' : Data E r) (L L' : Submodule (𝓞 E) (Fin r → E)) (𝔞 : Ideal (𝓞 E)) (ξ ξ' : E),
    X.Ψ = X'.Ψ → X.p0 = X'.p0 → 3 ≤ r → 0 < X.p0 → X.p0 < r → IsLat L → IsLat L' →
    cc ξ = -ξ → cc ξ' = -ξ' → (∀ τ ∈ X.Ψ, 0 < (τ ξ).im * (τ ξ').im) → SDTrace ξ X.Gm L → SDTrace ξ' X'.Gm L' →
    𝔞 ≠ ⊥ → Neat (IsCMField.complexConj E) 𝔞 →
    SameOrbits X X.Γ (levelGrp (ccH E) X.Gm L 𝔞) → SameOrbits X' X'.Γ (levelGrp (ccH E) X'.Gm L' 𝔞) →
    ∀ (x : Frame X.Ψ r) (x' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))),
      IsOrth X x → IsOrth X' x' → IsFundSet X x FF → IsFundSet X' x' FF' → muF X x FF = muF X' x' FF'

theorem neat_mono {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {c : E ≃ₐ[F] E}
    {𝔞 𝔟 : Ideal (𝓞 E)} (h : 𝔞 ≤ 𝔟) (hb : Neat c 𝔟) : Neat c 𝔞 := fun z h1 h2 => hb z h1 (h h2)

end PositivityTheory.EqVol
