import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.Block5c

def FinTF : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ξ : Representation ℂ Γ W),
  Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) →
  ∀ f : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) → (Function.support (fun q : G ⧸ K => f q.out)).Finite →
  ∀ M : Submodule ℂ (G → W), (∀ φ, φ ∈ M ↔ (∀ γ : Γ, ∀ g, φ ((γ : G) * g) = ξ γ (φ g)) ∧ ∀ k ∈ K, ∀ g, φ (g * k) = φ g) →
  ∀ T : M →ₗ[ℂ] M, (∀ φ : M, ∀ g, (T φ : G → W) g = ∑ᶠ h : G ⧸ K, f h.out • (φ : G → W) (g * h.out)) →
  LinearMap.trace ℂ M T = ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
    (1 / (Nat.card (GlobalTheory.LKLoc.locPart Γ K q.out) : ℂ)) * ∑ᶠ γ : Γ, f (q.out⁻¹ * γ * q.out) * LinearMap.trace ℂ W (ξ γ)

def FinTFOrb : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ξ : Representation ℂ Γ W),
  Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) →
  ∀ f : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) → (Function.support (fun q : G ⧸ K => f q.out)).Finite →
  ∀ R : Set Γ, (∀ γ : Γ, ∃! ρ, ρ ∈ R ∧ IsConj γ ρ) →
  ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
    (1 / (Nat.card (GlobalTheory.LKLoc.locPart Γ K q.out) : ℂ)) * ∑ᶠ γ : Γ, f (q.out⁻¹ * γ * q.out) * LinearMap.trace ℂ W (ξ γ)
  = ∑ᶠ ρ ∈ R, LinearMap.trace ℂ W (ξ ρ) *
      ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {(ρ : G)} ⊓ Γ : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {(ρ : G)} ⊓ Γ) K q.out) : ℂ)) * f (q.out⁻¹ * ρ * q.out)

def CuspOrbZero : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (f : GL ι K → ℂ), IsLocallyConstant f → HasCompactSupport f →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) →
  ∀ γ : GL ι K, (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∀ (K0 K1 : Subgroup (GL ι K)), IsOpen (K0 : Set (GL ι K)) → IsCompact (K0 : Set (GL ι K)) →
    IsOpen (K1 : Set (GL ι K)) → IsCompact (K1 : Set (GL ι K)) →
    (∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) →
    GlobalTheory.LKLoc.twOrbU (MonoidHom.id (GL ι K)) K0 γ (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓ K1) f = 0

def IwahoriRegularSeparable : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ),
  ValuativeRel.valuation k (ϖ : k) = ValuativeRel.uniformizer k →
  ∀ ν : Fin N → ℤ, StrictAnti ν → ∀ x ∈ GlobalTheory.SmGL.iwahori k (Fin N), ∀ y ∈ GlobalTheory.SmGL.iwahori k (Fin N),
    let g := x * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * y
    (g : Matrix (Fin N) (Fin N) k).charpoly.Separable ∧ (g : Matrix (Fin N) (Fin N) k).charpoly.Splits

def CoefCusp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsCuspidal π →
  ∀ (v : V), ∀ l ∈ smoothPart π.dual,
  ∀ f : GL (Fin N) k → ℂ, (∀ g, f g = if ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det = 1 then l (π g v) else 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  ∃ K0 : Subgroup (GL (Fin N) k), IsOpen (K0 : Set (GL (Fin N) k)) ∧ IsCompact (K0 : Set (GL (Fin N) k)) ∧
    (∀ x ∈ K0, ∀ y ∈ K0, ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → k) → GL (Fin N) k,
      (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL (Fin N) k, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0)

def TypeCusp : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (J : Subgroup (GL ι K)), IsOpen (J : Set (GL ι K)) → IsCompact (J : Set (GL ι K)) →
  ∀ χ : J →* ℂˣ, IsOpen (χ.ker : Set J) →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ h : GL ι K, ∃ X, ∃ hX : h⁻¹ * u X * h ∈ J, χ ⟨_, hX⟩ ≠ 1) →
  ∀ f : GL ι K → ℂ, (∀ g (hg : g ∈ J), f g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ)) → (∀ g, g ∉ J → f g = 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  (∀ x ∈ (χ.ker.map J.subtype), ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0)

def Top : Prop :=
  GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace ∧ FinTF ∧ FinTFOrb ∧ CuspOrbZero ∧ IwahoriRegularSeparable ∧ CoefCusp ∧ TypeCusp

end GlobalTheory.Block5c
