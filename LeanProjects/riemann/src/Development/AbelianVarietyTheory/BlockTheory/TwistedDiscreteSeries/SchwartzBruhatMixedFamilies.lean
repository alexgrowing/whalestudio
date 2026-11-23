import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7}

def IsRealParam {m n k : ℕ} (L : (Fin k → ℝ) →+ Mx D m n) : Prop :=
  Continuous L ∧ ∀ t, (L t).map (finPart D) = 0

structure IsSchwartzBruhat {m n : ℕ} (φ : Mx D m n → ℂ) : Prop where

  level : ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, φ (x + u) = φ x

  supp : ∃ K : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧
    ∀ x, φ x ≠ 0 → x.map (finPart D) ∈ K

  schwartz : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), IsRealParam L → Function.Injective L →
    ∀ x, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = φ (x + L t)

structure IsMixFamily (ψ : AddChar (AF D.host.F) ℂ) (S₀ T₀ : HSp D) {m n : ℕ} (Φ : Mx D m n → WO S₀ T₀ → ℂ) : Prop where

  theta : ∀ x, IsThetaFunO ψ S₀ T₀ (Φ x)

  schwartz : ∀ w₀, IsSchwartzBruhat fun x => Φ x w₀

  level : ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, Φ (x + u) = Φ x

  level₀ : ∃ U : AddSubgroup (WO S₀ T₀), IsOpen (U : Set (WO S₀ T₀)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, heisO ψ S₀ T₀ u (Φ x) = Φ x

  supp : ∃ K : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧
    ∀ x, Φ x ≠ 0 → x.map (finPart D) ∈ K

  smooth : ∀ (k l : ℕ) (L : (Fin k → ℝ) →+ Mx D m n) (M : (Fin l → ℝ) →+ WO S₀ T₀), IsRealParam L → IsRealParam M →
    ∀ x w₀, ContDiff ℝ ∞ fun p : (Fin k → ℝ) × (Fin l → ℝ) => Φ (x + L p.1) (w₀ + M p.2)

  decay : ∀ (k l : ℕ) (L : (Fin k → ℝ) →+ Mx D m n) (M : (Fin l → ℝ) →+ WO S₀ T₀), IsRealParam L →
    Function.Injective L → IsRealParam M → ∀ x w₀, ∀ (j N : ℕ) (R : ℝ), ∃ C : ℝ,
      ∀ p : (Fin k → ℝ) × (Fin l → ℝ), ‖p.2‖ ≤ R → ‖p.1‖ ^ N *
        ‖iteratedFDeriv ℝ j (fun q : (Fin k → ℝ) × (Fin l → ℝ) => Φ (x + L q.1) (w₀ + M q.2)) p‖ ≤ C

def IsRatSum {m n : ℕ} (φ : Mx D m n → ℂ) (c : ℂ) : Prop :=
  (Summable fun γ : Matrix (Fin m) (Fin n) D.host.E => ‖φ (rat γ)‖) ∧
    HasSum (fun γ : Matrix (Fin m) (Fin n) D.host.E => φ (rat γ)) c

def ExpansionS (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) : Prop :=
  (∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
    IsMixFamily ψ S₀ T (d.mixS T ψ μ 𝓕 f) ∧
    IsRatSum (fun x => d.mixS T ψ μ 𝓕 f x 0) (f 0) ∧
    (∀ x₁ x : Mx D T.rank ρ,
      d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x₁) f) x = d.mixS T ψ μ 𝓕 f (x + x₁)) ∧
    (∀ (w₁ : WO S₀ T) (x : Mx D T.rank ρ),
      d.mixS T ψ μ 𝓕 (heisO ψ S T (d.ext0 T w₁) f) x = heisO ψ S₀ T w₁ (d.mixS T ψ μ 𝓕 f x)) ∧
    (∀ y x : Mx D T.rank ρ,
      d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extY T y) f) x =
        ψ (symplO S T (d.extX T x) (d.extY T y)) • d.mixS T ψ μ 𝓕 f x)) ∧
  ∀ Φ : Mx D T.rank ρ → WO S₀ T → ℂ, IsMixFamily ψ S₀ T Φ →
    ∃! f : WO S T → ℂ, IsThetaFunO ψ S T f ∧ d.mixS T ψ μ 𝓕 f = Φ

def ExpansionT (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) : Prop :=
  (∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
    IsMixFamily ψ S T₀ (d.mixT S ψ μ 𝓕 f) ∧
    IsRatSum (fun y => d.mixT S ψ μ 𝓕 f y 0) (f 0) ∧
    (∀ y₁ y : Mx D S.rank ρ,
      d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incAdj S y₁) f) y = d.mixT S ψ μ 𝓕 f (y + y₁)) ∧
    (∀ (w₁ : WO S T₀) (y : Mx D S.rank ρ),
      d.mixT S ψ μ 𝓕 (heisO ψ S T (d.inc0 S w₁) f) y = heisO ψ S T₀ w₁ (d.mixT S ψ μ 𝓕 f y)) ∧
    (∀ (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ),
      d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incX S ξ) f) y =
        ψ (symplO S T (d.incAdj S y) (d.incX S ξ)) • d.mixT S ψ μ 𝓕 f y)) ∧
  ∀ Φ : Mx D S.rank ρ → WO S T₀ → ℂ, IsMixFamily ψ S T₀ Φ →
    ∃! f : WO S T → ℂ, IsThetaFunO ψ S T f ∧ d.mixT S ψ μ 𝓕 f = Φ

def MixExpansion (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
    (∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)),
      IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ExpansionS ψ d T μ 𝓕) ∧
    (∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)),
      IsCovolOne (ratMx D ρ S.rank) μ 𝓕 → ExpansionT ψ d S μ 𝓕)

theorem MixExpansion.std (h : MixExpansion D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)}
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) : ExpansionS ψ d T μ 𝓕 :=
  (h ψ hψ.1).1 S S₀ T ρ d μ 𝓕 hμ

end GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

end
