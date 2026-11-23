import Formalism.WachLatticeTwists.WachProductBases.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Formalism.CoboundaryTransfers

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

structure NSES {S : HidaSetting O A} {ι : Type} {pr : Equiv.Perm ι} {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : NData S ι pr D₀) (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) where
  ι : NHom W₀ W₁
  π : NHom W₁ W₂
  ι_inj : ∀ i, Function.Injective (ι.f i)
  exact : ∀ i x, π.f i x = 0 ↔ ∃ x₀, ι.f i x₀ = x
  surj : ∀ i, Function.Surjective (π.f i)

def InLattice {S : HidaSetting O A} {ι : Type} {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D]
    [Module A D] [Module O D] [IsScalarTower O A D] (W : NData S ι pr D) : Prop :=
  (∀ i, (W.N i).FG) ∧
  (∀ (i : ι) (a : ℕ) (d : D), ∃ k : ℕ, ∃ n ∈ W.N i, ∃ d' : D,
    S.π ^ k • d = n + (S.ℓ : A) ^ a • d') ∧
  (∀ (i : ι) (d : D), (S.ℓ : A) • d ∈ W.N i → d ∈ W.N i) ∧
  (∀ (i : ι) (d : D), (∃ k : ℕ, S.π ^ k • ((S.ℓ : A) • d) ∈ W.N i) → ∃ k : ℕ, S.π ^ k • d ∈ W.N i)

def LatticeSequenceExactUpToPrimePower {S : HidaSetting O A} {ι : Type} {pr : Equiv.Perm ι} {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    {W₀ : NData S ι pr D₀} {W₁ : NData S ι pr D₁} {W₂ : NData S ι pr D₂}
    (E : NSES W₀ W₁ W₂) : Prop :=
  (∃ a : ℕ, ∀ i, E.π.Kills i ((S.ℓ : A) ^ a)) ∧
  (∀ i x, E.ι.f i x ∈ W₁.N i → ∃ k : ℕ, (S.ℓ : A) ^ k • x ∈ W₀.N i)

def WachProductBasisTheorem : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type) [Finite ι]
    (pr : Equiv.Perm ι) (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : NData S ι pr D₀) (W₁ : NData S ι pr D₁) (W₂ : NData S ι pr D₂) (E : NSES W₀ W₁ W₂)
    (M h : ι → ℕ) (M₀ h₀ H : ℕ),
    S.Rad → S.Decomp →
    W₀.P2 → W₁.P2 → W₂.P2 → W₀.P5 M h → W₁.P5 M h → W₂.P5 M h →
    InLattice W₀ → InLattice W₁ → InLattice W₂ → LatticeSequenceExactUpToPrimePower E →
    (∀ i, M i ≤ M₀) → (∀ i, h i ≤ h₀) → (∀ i, M i + h i ≤ H) →

    (∀ i, E.π.Kills i (S.X ^ H)) ∧

    (∀ (π' w : A) (e s' : ℕ), S.s = 1 → e * s' = S.ℓ - 1 → π' = w * S.π ^ s' →
      ∀ i, E.π.Kills i (π' ^ ⌈((e * H : ℕ) : ℚ) / ((S.ℓ - 1 : ℕ) : ℚ)⌉₊)) ∧

    (∀ (π' w : A) (e s' : ℕ) (Δ : Type) [Group Δ] [Fintype Δ]
      (ρ₁ : ι → Δ →* Module.End O D₁) (ρ₂ : ι → Δ →* Module.End O D₂),
      S.s = 1 → e * s' = S.ℓ - 1 → π' = w * S.π ^ s' → IsUnit ((Fintype.card Δ : ℕ) : O) →
      (∀ i d, ∀ x ∈ W₁.N i, ρ₁ i d x ∈ W₁.N i) →
      (∀ i d x, E.π.f i (ρ₁ i d x) = ρ₂ i d (E.π.f i x)) →
      (∀ i d x, ρ₂ i d (π' • x) = π' • ρ₂ i d x) →
      ∀ i, ∀ n ∈ W₂.N i, (∀ d, ρ₂ i d n = n) → ∃ n₁ ∈ W₁.N i, (∀ d, ρ₁ i d n₁ = n₁) ∧
        E.π.f i n₁ = π' ^ ⌈((e * H : ℕ) : ℚ) / ((S.ℓ - 1 : ℕ) : ℚ)⌉₊ • n) ∧

    (∀ i x, E.ι.f i x ∈ W₁.N i → x ∈ W₀.N i) ∧

    ∃ (V₀ : WachMod S.base M₀ (ι → D₀)) (V₁ : WachMod S.base M₀ (ι → D₁))
      (V₂ : WachMod S.base M₀ (ι → D₂)) (Sq : SES V₀ V₁ V₂),
      V₀.N = Submodule.pi Set.univ W₀.N ∧ V₁.N = Submodule.pi Set.univ W₁.N ∧
      V₂.N = Submodule.pi Set.univ W₂.N ∧
      (∀ x i, V₀.φ x i = W₀.φ i (x (pr i))) ∧ (∀ x i, V₀.γ x i = W₀.γ i (x i)) ∧
      (∀ x i, V₁.φ x i = W₁.φ i (x (pr i))) ∧ (∀ x i, V₁.γ x i = W₁.γ i (x i)) ∧
      (∀ x i, V₂.φ x i = W₂.φ i (x (pr i))) ∧ (∀ x i, V₂.γ x i = W₂.γ i (x i)) ∧
      (∀ x i, Sq.ι.f x i = E.ι.f i (x i)) ∧ (∀ x i, Sq.π.f x i = E.π.f i (x i)) ∧
      Sq.Surj ∧
      (∀ n ∈ V₂.N, ∃ n₁ ∈ V₁.N, Sq.π.f n₁ = S.X ^ H • n) ∧
      (∃ e : ℕ, CokerKilled Sq e) ∧
      V₀.HeightLower h₀ ∧ V₁.HeightLower h₀ ∧ V₂.HeightLower h₀

end Formalism.RepresentationBoundsCohomology.N1
