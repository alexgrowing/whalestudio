import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

def twSecs {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules} (S : Subobject P) :
    Set Γ(GlobalTheory.twistZ P H n, ⊤) :=
  Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤)

def twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ) : Set Γ(GlobalTheory.twistZ P H n, ⊤) :=
  ((Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) • ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) :
    Set Γ(GlobalTheory.twistZ P H n, ⊤))

structure OpSeq {X : Scheme.{0}} (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (d : ℕ) : Prop where
  coherent : ∀ e, IsCoherent (M e)
  comm : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)
  gen : ∀ e, d ≤ e → ∀ U : X.affineOpens,
    Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤

def GradedNoeth : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (k : ℕ) (M : ℕ → Type)
    [∀ e, AddCommGroup (M e)] [∀ e, Module R (M e)] [∀ e, Module.Finite R (M e)]
    (T : Fin k → ∀ e, M e →ₗ[R] M (e + 1)),
    (∀ i j e x, T j (e + 1) (T i e x) = T i (e + 1) (T j e x)) →
    ∀ d : ℕ, (∀ e, d ≤ e → ⨆ i, LinearMap.range (T i e) = ⊤) →
    ∀ L : ∀ e, Submodule R (M e), (∀ i e, (L e).map (T i e) ≤ L (e + 1)) →
    ∃ d' : ℕ, ∀ e, d' ≤ e → ⨆ i, (L e).map (T i e) = L (e + 1)

def UniformVanishing : Prop :=
  ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ), OpSeq k M T d →
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M e) H n) q)

def UniformGen : Prop :=
  ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ), OpSeq k M T d →
    ∃ n₁ : ℤ, ∀ n, n₁ ≤ n → ∀ e, d ≤ e →
      Submodule.span Γ(X, ⊤)
        (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (T i e)).app ⊤)) = ⊤

end GlobalTheory.CompanionTheory.GE
