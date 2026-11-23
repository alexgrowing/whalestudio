import Formalism.WachLatticeTwists.DenseTopActions.Statement
import Formalism.WachLatticeTwists.SandwichH1Classes.HypothesisWGivesUnitCongruence

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JW

open Matrix Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
open scoped TensorProduct

section named

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
  {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {W : NData S ι pr D} {ℓ : ℕ} [Fact ℓ.Prime] {As AA WC : Type} [CommRing As] [CommRing AA] [CommRing WC]
  [Algebra ℤ_[ℓ] WC] {jS : As →+* (ι → A)} {jA : As →+* AA} {io : AA →+* WC} {φ : WC →+* WC}
  {Gg : Type} [Group Gg] {H : Subgroup Gg} {act : Gg →* (WC ≃+* WC)} {r : ℕ}
  {ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]}

def FunctOn (C : Cmp W jS jA io φ H act ρ) (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) : Prop :=
  ∀ E ∈ En, ∀ x, InN W x → ∃ y, InN W y ∧ C.cmp y = C.cmp x ᵥ* E.map (algebraMap ℤ_[ℓ] WC)

def OLin (C : Cmp W jS jA io φ H act ρ) (EO : O → Matrix (Fin r) (Fin r) ℤ_[ℓ]) : Prop :=
  ∀ (o : O) (x : ι → D), C.cmp ((fun _ => algebraMap O A o : ι → A) • x)
    = C.cmp x ᵥ* (EO o).map (algebraMap ℤ_[ℓ] WC)

def EnO (C : Cmp W jS jA io φ H act ρ) : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ]) :=
  {E | ∃ o : O, ∀ x, C.cmp ((fun _ => algebraMap O A o : ι → A) • x)
    = C.cmp x ᵥ* E.map (algebraMap ℤ_[ℓ] WC)}

end named

def StatJWc : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A)
    (ι : Type) [Finite ι] (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] (W : NData S ι pr D) (As AA WC : Type) [CommRing As] [CommRing AA]
    [CommRing WC] [Algebra ℤ_[ℓ] WC] (jS : As →+* (ι → A)) (φs : As →+* As) (jA : As →+* AA)
    (io : AA →+* WC) (φ : WC →+* WC) (Gg : Type) [Group Gg] (H : Subgroup Gg)
    (act : Gg →* (WC ≃+* WC)) (r : ℕ) (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]) (πs : As)
    (C : Cmp W jS jA io φ H act ρ) (b : Fin r → ι → D) (M h : ι → ℕ) (M0 h0 : ℕ)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])),
    (∀ i, jS πs i = S.π) → (∀ a i, jS (φs a) i = S.φ (jS a (pr i))) → GenO O jS → BasisN W jS b →
    W.P5 M h → (∀ i, M i ≤ M0) → (∀ i, h i ≤ h0) →
    ComparisonMatrixInvertible C b → GammaTrivialModUniformizers C πs → FunctOn C En →
    ∃ Y : HypWc ℓ As AA WC jA io φ Gg H act r ρ En πs (xiOf S.ℓ S.s πs) M0 h0, Y.Xx = xMat C b ∧
      ∀ g i j, ∃ t, (Y.Gm g - 1) i j = πs * t

def StatFunctO : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A)
    (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] (W : NData S ι pr D) (As AA WC : Type) [CommRing As] [CommRing AA]
    [CommRing WC] [Algebra ℤ_[ℓ] WC] (jS : As →+* (ι → A)) (jA : As →+* AA)
    (io : AA →+* WC) (φ : WC →+* WC) (Gg : Type) [Group Gg] (H : Subgroup Gg)
    (act : Gg →* (WC ≃+* WC)) (r : ℕ) (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (C : Cmp W jS jA io φ H act ρ), FunctOn C (EnO C)

def StatFunctEO : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A)
    (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] (W : NData S ι pr D) (As AA WC : Type) [CommRing As] [CommRing AA]
    [CommRing WC] [Algebra ℤ_[ℓ] WC] (jS : As →+* (ι → A)) (jA : As →+* AA)
    (io : AA →+* WC) (φ : WC →+* WC) (Gg : Type) [Group Gg] (H : Subgroup Gg)
    (act : Gg →* (WC ≃+* WC)) (r : ℕ) (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (C : Cmp W jS jA io φ H act ρ) (EO : O → Matrix (Fin r) (Fin r) ℤ_[ℓ]),
    OLin C EO → Set.range EO ⊆ EnO C ∧ FunctOn C (Set.range EO)

def StatJWcTop : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Algebra ℤ_[ℓ] O]
    (S : HidaSetting O A)
    (ι : Type) [Finite ι] (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] (W : NData S ι pr D) (As AA WC : Type) [CommRing As] [CommRing AA]
    [CommRing WC] [Algebra ℤ_[ℓ] WC] [Algebra ℤ_[ℓ] As] (jS : As →+* (ι → A)) (φs : As →+* As)
    (jA : As →+* AA) (io : AA →+* WC) (φ : WC →+* WC) (Gg : Type) [Group Gg]
    (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC)) (r : ℕ) (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (πs : As) (C : Cmp W jS jA io φ H act ρ) (M h : ι → ℕ) (M0 h0 : ℕ)
    (κ : Type) [Fintype κ] (e : Module.Basis κ ℤ_[ℓ] O) (Ψ : TensorProduct ℤ_[ℓ] As O ≃+ (ι → A))
    (r₀ : ℕ) (c : ι → Fin r₀ → D) (eq : κ × Fin r₀ ≃ Fin r) (EO : O → Matrix (Fin r) (Fin r) ℤ_[ℓ]),
    (∀ i, jS πs i = S.π) → (∀ a i, jS (φs a) i = S.φ (jS a (pr i))) →
    (∀ a o, Ψ (a ⊗ₜ o) = jS a * fun _ => algebraMap O A o) →
    (∀ i m, c i m ∈ W.N i) →
    (∀ i, ∀ x ∈ W.N i, ∃ a : Fin r₀ → A, x = ∑ m, a m • c i m) →
    (∀ i (a : Fin r₀ → A), ∑ m, a m • c i m = 0 → a = 0) →
    W.P5 M h → (∀ i, M i ≤ M0) → (∀ i, h i ≤ h0) → GammaTrivialModUniformizers C πs →
    ComparisonMatrixInvertible C (fun k i => e (eq.symm k).1 • c i (eq.symm k).2) → OLin C EO →
    ∃ Y : HypWc ℓ As AA WC jA io φ Gg H act r ρ (Set.range EO) πs (xiOf S.ℓ S.s πs) M0 h0,
      Y.Xx = xMat C (fun k i => e (eq.symm k).1 • c i (eq.symm k).2) ∧
      ∀ g i j, ∃ t, (Y.Gm g - 1) i j = πs * t

def StatJWcTopDense : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Algebra ℤ_[ℓ] O]
    (S : HidaSetting O A)
    (ι : Type) [Finite ι] (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] (W : NData S ι pr D) (As AA WC : Type) [CommRing As] [CommRing AA]
    [CommRing WC] [Algebra ℤ_[ℓ] WC] [Algebra ℤ_[ℓ] As] (jS : As →+* (ι → A)) (φs : As →+* As)
    (jA : As →+* AA) (io : AA →+* WC) (φ : WC →+* WC) (Gg : Type) [Group Gg] [TopologicalSpace Gg]
    (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC)) (r : ℕ) (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (πs : As) (C : Cmp W jS jA io φ H act ρ) (g₀ : Gg) (M h : ι → ℕ) (M0 h0 : ℕ)
    (κ : Type) [Fintype κ] (e : Module.Basis κ ℤ_[ℓ] O) (Ψ : TensorProduct ℤ_[ℓ] As O ≃+ (ι → A))
    (r₀ : ℕ) (c : ι → Fin r₀ → D) (eq : κ × Fin r₀ ≃ Fin r),
    (∀ i, jS πs i = S.π) → (∀ a i, jS (φs a) i = S.φ (jS a (pr i))) →
    (∀ a o, Ψ (a ⊗ₜ o) = jS a * fun _ => algebraMap O A o) →
    (∀ i m, c i m ∈ W.N i) →
    (∀ i, ∀ x ∈ W.N i, ∃ a : Fin r₀ → A, x = ∑ m, a m • c i m) →
    (∀ i (a : Fin r₀ → A), ∑ m, a m • c i m = 0 → a = 0) →
    W.P5 M h → (∀ i, M i ≤ M0) → (∀ i, h i ≤ h0) → W.P2 →
    (∀ x, C.cmp (Gam W x) = galT act ρ g₀ (C.cmp x)) →
    (∀ g g', ρ (g * g') = ρ g' * ρ g) →
    (∀ g (c : ℤ_[ℓ]), act g (algebraMap ℤ_[ℓ] WC c) = algebraMap ℤ_[ℓ] WC c) →
    Dense (Submonoid.closure ((H : Set Gg) ∪ {g₀}) : Set Gg) → IsClosed {g | TrivAt C πs g} →
    ComparisonMatrixInvertible C (fun k i => e (eq.symm k).1 • c i (eq.symm k).2) →
    ∃ Y : HypWc ℓ As AA WC jA io φ Gg H act r ρ (EnO C) πs (xiOf S.ℓ S.s πs) M0 h0,
      Y.Xx = xMat C (fun k i => e (eq.symm k).1 • c i (eq.symm k).2) ∧
      ∀ g i j, ∃ t, (Y.Gm g - 1) i j = πs * t

end Formalism.RepresentationBoundsCohomology.JW
