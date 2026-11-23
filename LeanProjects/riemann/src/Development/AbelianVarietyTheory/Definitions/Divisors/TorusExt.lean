import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

open AlgebraicGeometry CategoryTheory Limits MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.LieHt

section Lat

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

def MuLe (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)) (ν : ℝ) : Prop :=
  ∀ W ≤ L, deg h W ≤ latRank K W * ν

def Full (L : Submodule (𝓞 K) (Fin m → K)) : Prop := L.FG ∧ Submodule.span K (L : Set (Fin m → K)) = ⊤

def lineLat (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) : Submodule (𝓞 K) (Fin m → K) :=
  L ⊓ (Submodule.span K {x}).restrictScalars (𝓞 K)

variable (K' : Type) [Field K'] [NumberField K'] [Algebra K K']

def latBC (L : Submodule (𝓞 K) (Fin m → K)) : Submodule (𝓞 K') (Fin m → K') :=
  Submodule.span (𝓞 K') ((fun v i => algebraMap K K' (v i)) '' (L : Set (Fin m → K)))

variable {K'} in

def IsBC (h : HermFam K (Fin m → K)) (h' : HermFam K' (Fin m → K')) : Prop :=
  ∀ (σ : K' →+* ℂ) (i j : Fin m),
    h'.form σ (Pi.single i 1) (Pi.single j 1) = h.form (σ.comp (algebraMap K K')) (Pi.single i 1) (Pi.single j 1)

def JetSys (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) (n : ℕ) (ν : ℝ)
    (β : ℕ → (K →+* ℂ) → ℝ) : Prop :=
  ∃ (r : ℕ) (hE : HermFam K (Fin r → K)) (E : Submodule (𝓞 K) (Fin r → K)) (Vf : ℕ → Submodule K (Fin r → K))
    (j : ℕ → (Fin r → K) →ₗ[K] K), Full E ∧ MuLe hE E ν ∧ deg hE E = r * ν ∧ Vf 0 = ⊤ ∧ ∀ i ≤ n,
      Vf (i + 1) = Vf i ⊓ LinearMap.ker (j i) ∧ (∃ v ∈ Vf i, j i v ≠ 0) ∧
      (∀ v ∈ E, v ∈ Vf i → ∀ a : K, a • x ∈ L → IsIntegral ℤ (a ^ i * j i v)) ∧
      ∀ (σ : K →+* ℂ) (q : ℕ) (v : Fin q → Fin r → K) (c : Fin q → ℂ), (∀ a, v a ∈ Vf i) →
        ‖∑ a, c a * σ (j i (v a))‖ ^ 2 ≤
          (β i σ * h.nrm σ x ^ i) ^ 2 * (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * hE.form σ (v a) (v b)).re

def TorusExt {r m' : ℕ} (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)) (ε : Fin r → Fin m → K)
    (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (h' : HermFam K (Fin m' → K)) (L' : Submodule (𝓞 K) (Fin m' → K)) (C : ℝ) : Prop :=
  Full L ∧ Full L' ∧ LinearIndependent K ε ∧ Function.Surjective q ∧ LinearMap.ker q = Submodule.span K (Set.range ε) ∧
    L ⊓ (LinearMap.ker q).restrictScalars (𝓞 K) = Submodule.span (𝓞 K) (Set.range ε) ∧ (∀ v ∈ L, q v ∈ L') ∧
    ∀ σ : K →+* ℂ, ((C : ℂ) • h.gram σ ε - 1).PosSemidef ∧
      ∀ (n : ℕ) (v : Fin n → Fin m → K), ((C : ℂ) • h.gram σ v - h'.gram σ (q ∘ v)).PosSemidef

end Lat

structure SemiFib (K : Type) [Field K] [NumberField K] : Type 1 where

  P₀ : Out.PolAV (Sp K)

  G : Over (Sp (𝓞 K))
  [grp : GrpObj G]
  semi : IsSemiAbelian G

  φ : P₀.A.left ⟶ G.left
  fib : IsGrpPullback P₀.A G (spMap (algebraMap (𝓞 K) K)) φ

  v : Fin P₀.g → (epsR K ⟶ P₀.A)
  basis : IsLieBasis v

attribute [instance] SemiFib.grp

namespace SemiFib

variable {K : Type} [Field K] [NumberField K] (F : SemiFib K)

def lieLat : Submodule (𝓞 K) (Fin F.P₀.g → K) := Submodule.span (𝓞 K)
  {c | ∃ u : epsR (𝓞 K) ⟶ F.G, IsTangent u ∧ ∃ w, IsVecOver (algebraMap (𝓞 K) K) F.φ u w ∧ IsLieComb c F.v w}

def IsUnif (s : K →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (W : Fin F.P₀.g → Fin g → ℂ) : Prop :=
  ∃ (Q : Out.PolAV (Sp ℂ)) (e : Q.g = g) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A))
    (u : HolUnif Q.A Q.L g) (χ : u.Λ → ℂ),
    IsPolFibre s F.P₀ Q ψ ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ ∀ i, IsVecOver s ψ (F.v i) (v' i) ∧ u.IsDiff (W i) (v' i)

def IsHerm (h : HermFam K (Fin F.P₀.g → K)) : Prop :=
  ∀ s : K →+* ℂ, ∃ (Λ : Submodule ℤ (Fin F.P₀.g → ℂ)) (Hm : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ)
    (W : Fin F.P₀.g → Fin F.P₀.g → ℂ), F.IsUnif s Λ Hm W ∧
      ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (W j) (W i)

def IsRho (ρ : (K →+* ℂ) → ℝ) : Prop :=
  ∀ s : K →+* ℂ, ∃ (Λ : Submodule ℤ (Fin F.P₀.g → ℂ)) (Hm : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ)
    (W : Fin F.P₀.g → Fin F.P₀.g → ℂ), F.IsUnif s Λ Hm W ∧
      IsLeast {t | ∃ z ∈ Λ, z ≠ 0 ∧ t = √(hermForm Hm z z).re} (ρ s)

def falt (h : HermFam K (Fin F.P₀.g → K)) : ℝ := -deg h F.lieLat

end SemiFib

def LieSlope : Prop := ∀ g : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g ≤ g →
  ∀ h, F.IsHerm h → Full F.lieLat ∧ MuLe h F.lieLat (C * Real.log (2 + max (F.falt h) 0))

def jetBd (g n i : ℕ) (ρ : ℝ) : ℝ :=
  √(Real.exp 1 * n * i) ^ i * √(Real.exp 1 * g.factorial) * max ((√Real.pi / 2 * ρ)⁻¹ ^ g) (√n ^ g)

def SecJets : Prop := ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (h : HermFam K (Fin F.P₀.g → K))
  (ρ : (K →+* ℂ) → ℝ), F.IsHerm h → F.IsRho ρ →
  ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (x : Fin F.P₀.g → K'), x ≠ 0 → ∀ n : ℕ, 2 ≤ n →
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra K' K'') (_ : Algebra K K'') (_ : IsScalarTower K K' K'')
      (h'' : HermFam K'' (Fin F.P₀.g → K'')), IsBC h h'' ∧
      JetSys h'' (latBC K'' F.lieLat) (fun i => algebraMap K' K'' (x i)) n
        (-F.falt h / 2 + (F.P₀.g : ℝ) / 4 * Real.log ((3 * n : ℕ) / (2 * Real.pi)))
        fun i σ => jetBd F.P₀.g (3 * n) i (ρ (σ.comp (algebraMap K K'')))

def SemiFib.ofGenFib {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))} (hP : IsSemiAbelian P.A)
    (F : GlobalTheory.CM.GenFib P) : SemiFib K := ⟨F.P₀, P.A, hP, F.φ, F.fib.2.1, F.v, F.basis⟩

example {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))} (hP : IsSemiAbelian P.A)
    (F : GlobalTheory.CM.GenFib P) : (SemiFib.ofGenFib hP F).lieLat = F.lieLat := rfl

end GlobalTheory.LieHt
end
