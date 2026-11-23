import Formalism.WachLatticeTwists.HodgeTateChains.ProductEqXiPowerSmulOne

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Matrix

def StatWActU : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC OC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [CommRing OC] [Algebra ℤ_[ℓ] AA] [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (GK : Type) [Group GK] (inc : Gg →* GK)
    (r : ℕ) (ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ x : As) (M0 h0 : ℕ)
    (W : HypW' ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0) (ϑ : AA →+* OC)
    (A : Matrix (Fin r) (Fin r) AA) (g : Gg) (gA : AA →+* AA) (τ : OC →+* OC) (u : As),
    Function.Injective ι → (∀ c : ℤ_[ℓ], ι (algebraMap ℤ_[ℓ] AA c) = algebraMap ℤ_[ℓ] WC c) →
    A.map ι = (ι (jA x)) ^ M0 • W.Xx →
    (∀ a, ι (gA a) = act g (ι a)) → (∀ a, ϑ (gA a) = τ (ϑ a)) →
    τ (ϑ (jA x)) = ϑ (jA u) * ϑ (jA x) → (∀ y : OC, ϑ (jA x) * y = 0 → y = 0) →
    (A.map ϑ).map τ * (((ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA)).map ϑ)
      = ((u ^ M0 • W.Gm g).map jA).map ϑ * A.map ϑ

def StatWAct : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC OC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [CommRing OC] [Algebra ℤ_[ℓ] AA] [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (GK : Type) [Group GK] (inc : Gg →* GK)
    (r : ℕ) (ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ x : As) (M0 h0 : ℕ)
    (W : HypW' ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0) (ϑ : AA →+* OC)
    (A : Matrix (Fin r) (Fin r) AA) (g : Gg) (gA : AA →+* AA) (τ : OC →+* OC),
    Function.Injective ι → (∀ c : ℤ_[ℓ], ι (algebraMap ℤ_[ℓ] AA c) = algebraMap ℤ_[ℓ] WC c) →
    A.map ι = (ι (jA x)) ^ M0 • W.Xx →
    (∀ a, ι (gA a) = act g (ι a)) → (∀ a, ϑ (gA a) = τ (ϑ a)) →
    τ (ϑ (jA x)) = ϑ (jA x) → (∀ y : OC, ϑ (jA x) * y = 0 → y = 0) →
    (A.map ϑ).map τ * (((ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA)).map ϑ)
      = ((W.Gm g).map jA).map ϑ * A.map ϑ

def StatXNzd : Prop :=
  ∀ (ℓ : ℕ) (OC : Type) [CommRing OC] (y c : OC) (k : ℕ), 1 ≤ k → y ^ k * c = (ℓ : OC) →
    (∀ a : OC, (ℓ : OC) * a = 0 → a = 0) → ∀ a : OC, y * a = 0 → a = 0

def StatWChain : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC OC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [CommRing OC] [Algebra ℤ_[ℓ] AA] [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (GK : Type) [Group GK] (inc : Gg →* GK)
    (r : ℕ) (ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ x : As) (M0 h0 : ℕ)
    (W : HypW' ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0) (ϑ : AA →+* OC) (c : OC)
    (γ : Gg) (σ : As →+* As) (gA : AA →+* AA) (τ : OC →+* OC) (z ϖ ϖ' : OC) (s : ℕ),
    LemmaAProp ι φ r → Function.Injective ι → φ (ι (jA x)) = ι (jA x * jA ξ) →
    (∀ a : WC, ι (jA ξ) * a = 0 → a = 0) →
    (ϑ (jA x)) ^ (ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1)) * c = (ℓ : OC) →
    (∀ c : ℤ_[ℓ], ι (algebraMap ℤ_[ℓ] AA c) = algebraMap ℤ_[ℓ] WC c) →
    (∀ g (c : ℤ_[ℓ]), act g (algebraMap ℤ_[ℓ] WC c) = algebraMap ℤ_[ℓ] WC c) →
    Function.Injective jA → (∀ a, act γ (ι (jA a)) = ι (jA (σ a))) →
    (∀ a, σ a - a ∈ Ideal.span {(ℓ : As), πs}) →
    (∀ a ∈ Ideal.span {(ℓ : As), πs}, σ a - a ∈ (Ideal.span {(ℓ : As), πs}) ^ 2) →
    ϑ (jA πs) = ϖ' → ϖ' ∣ (ℓ : OC) → z ∣ (ℓ : OC) → ϖ ∣ (ℓ : OC) →
    z * ϖ ∣ ϖ' ^ (ℓ ^ (s + n0 ℓ (M0 + h0))) →
    (∀ a, ι (gA a) = act (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1))) (ι a)) → (∀ a, ϑ (gA a) = τ (ϑ a)) →
    τ (ϑ (jA x)) = ϑ (jA x) → (∀ a : OC, (ℓ : OC) * a = 0 → a = 0) →
    ∃ (A : Matrix (Fin r) (Fin r) AA) (Y' : Matrix (Fin r) (Fin r) OC),
      A.map ι = (ι (jA x)) ^ M0 • W.Xx ∧
      A.map ϑ * Y' = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) ∧
      Y' * A.map ϑ = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) ∧
      (A.map ϑ).map τ * (((ρ (inc (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1)))) :
          Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA)).map ϑ)
        = ((W.Gm (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1)))).map jA).map ϑ * A.map ϑ ∧
      ∀ i j, z * ϖ ∣ (((W.Gm (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1)))).map jA).map ϑ - 1) i j

def StatWD : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC OC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [CommRing OC] [Algebra ℤ_[ℓ] AA] [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (GK : Type) [Group GK] (inc : Gg →* GK)
    (r : ℕ) (ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ x : As) (M0 h0 : ℕ)
    (W : HypW' ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0) (ϑ : AA →+* OC) (c : OC)
    (γ : Gg) (σ : As →+* As) (actA : Gg →* (AA ≃+* AA)) (actO : Gg →* (OC ≃+* OC)) (z ϖ ϖ' : OC) (s : ℕ),
    LemmaAProp ι φ r → Function.Injective ι → φ (ι (jA x)) = ι (jA x * jA ξ) →
    (∀ a : WC, ι (jA ξ) * a = 0 → a = 0) →
    (ϑ (jA x)) ^ (ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1)) * c = (ℓ : OC) →
    (∀ c : ℤ_[ℓ], ι (algebraMap ℤ_[ℓ] AA c) = algebraMap ℤ_[ℓ] WC c) →
    (∀ g (c : ℤ_[ℓ]), act g (algebraMap ℤ_[ℓ] WC c) = algebraMap ℤ_[ℓ] WC c) →
    Function.Injective jA → (∀ a, act γ (ι (jA a)) = ι (jA (σ a))) →
    (∀ a, σ a - a ∈ Ideal.span {(ℓ : As), πs}) →
    (∀ a ∈ Ideal.span {(ℓ : As), πs}, σ a - a ∈ (Ideal.span {(ℓ : As), πs}) ^ 2) →
    ϑ (jA πs) = ϖ' → ϖ' ∣ (ℓ : OC) → z ∣ (ℓ : OC) → ϖ ∣ (ℓ : OC) →
    z * ϖ ∣ ϖ' ^ (ℓ ^ (s + n0 ℓ (M0 + h0))) →
    (∀ g a, ι (actA g a) = act g (ι a)) → (∀ g a, ϑ (actA g a) = actO g (ϑ a)) →
    actO (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1))) (ϑ (jA x)) = ϑ (jA x) →
    (∀ a : OC, (ℓ : OC) * a = 0 → a = 0) →
    (∀ h ∈ H, ∀ a : As, act h (ι (jA a)) = ι (jA a)) →
    (∀ g, ∃ u : As, act g (ι (jA x)) = ι (jA (u * x))) →
    ∃ (A : Matrix (Fin r) (Fin r) AA) (Y' : Matrix (Fin r) (Fin r) OC),
      A.map ι = (ι (jA x)) ^ M0 • W.Xx ∧
      A.map ϑ * Y' = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) ∧
      Y' * A.map ϑ = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) ∧
      (∀ h ∈ H, (A.map ϑ).map (actO h) *
        (((ρ (inc h) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA)).map ϑ) = A.map ϑ) ∧
      (∀ g, ∃ V : Matrix (Fin r) (Fin r) As, (A.map ϑ).map (actO g) *
        (((ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA)).map ϑ)
          = (V.map jA).map ϑ * A.map ϑ) ∧
      (∀ E : Matrix (Fin r) (Fin r) ℤ_[ℓ],
        (∀ g : GK, E * (ρ g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) = ρ g * E) →
        ∃ E' : Matrix (Fin r) (Fin r) As,
          A.map ϑ * (Eᵀ.map (algebraMap ℤ_[ℓ] AA)).map ϑ = (E'.map jA).map ϑ * A.map ϑ) ∧
      (A.map ϑ).map (actO (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1)))) *
          (((ρ (inc (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1)))) :
            Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA)).map ϑ)
        = ((W.Gm (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1)))).map jA).map ϑ * A.map ϑ ∧
      ∀ i j, z * ϖ ∣ (((W.Gm (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1)))).map jA).map ϑ - 1) i j

def HypW'.W3pi {ℓ : ℕ} [Fact ℓ.Prime] {As AA WC : Type} [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] {jA : As →+* AA} {ι : AA →+* WC} {φ : WC →+* WC}
    {Gg : Type} [Group Gg] {H : Subgroup Gg} {act : Gg →* (WC ≃+* WC)}
    {GK : Type} [Group GK] {inc : Gg →* GK}
    {r : ℕ} {ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ} {πs ξ : As} {M0 h0 : ℕ}
    (W : HypW' ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0) : Prop :=
  ∀ g i j, (W.Gm g - 1) i j ∈ Ideal.span {πs}

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
