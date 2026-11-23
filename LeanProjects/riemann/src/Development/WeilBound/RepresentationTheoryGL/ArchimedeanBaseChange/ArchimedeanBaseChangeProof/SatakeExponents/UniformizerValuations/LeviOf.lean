import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcN.F2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def phi3 (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (x y : GLw n w) (m : GLw a w × GLw b w) : ℂ :=
  absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) *
    hint (intMat a b w) fun X => f (x⁻¹ * blk h w m (Multiplicative.toAdd X) * y)

def gconv {w : Pl E} (f₁ f₂ : GLw n w → ℂ) (y : GLw n w) : ℂ := hint (GlobalTheory.LFun.KGL w n) fun z => f₁ z * f₂ (z⁻¹ * y)

def mconv {w : Pl E} (u₁ u₂ : GLw a w × GLw b w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) fun m' => u₁ m' * u₂ (m'⁻¹ * m)

def leviOf (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) : Set (GLw a w × GLw b w) := {m | blk h w m 0 ∈ K'}

variable (E) in

def LocOpUniformizer : Prop :=
  ∀ (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) →
    K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') →
    ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') →
    (∀ f : GLw n w → ℂ, IsHk K' f → ∀ x ∈ X, ∀ y ∈ X,
      IsLocallyConstant (phi3 h w f x y) ∧ HasCompactSupport (phi3 h w f x y) ∧
      ∀ k₁ ∈ leviOf h w K', ∀ k₂ ∈ leviOf h w K', ∀ m, phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m) ∧
    (∀ f : GLw n w → ℂ, IsHk K' f → ∀ m, ct h w f m = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, phi3 h w f x x m) ∧
    (∀ f₁ f₂ : GLw n w → ℂ, IsHk K' f₁ → IsHk K' f₂ → ∀ x ∈ X, ∀ z ∈ X, ∀ m,
      phi3 h w (gconv f₁ f₂) x z m = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, mconv (phi3 h w f₁ x y) (phi3 h w f₂ y z) m) ∧
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GLw a w × GLw b w) W),
      ∀ (f : GLw n w → ℂ), IsHk K' f → ∀ u ∈ fixed (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K', ∀ x ∈ X,
        ∀ lw : W →ₗ[ℂ] ℂ, lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) =
          ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
            fun m => phi3 h w f x y m * lw (ρ m (u.1.1 y))

end PositivityTheory.Rg.BcN.F2
