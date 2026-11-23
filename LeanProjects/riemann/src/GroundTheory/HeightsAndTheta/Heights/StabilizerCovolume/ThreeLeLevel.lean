import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.DataHodge
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.EqZeroOfIsIsoSub
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

section Herm

variable (Em : Type) [Field Em] [NumberField Em] [IsCMField Em]

def hermForm {N : ℕ} (H : Matrix (Fin N) (Fin N) Em) (x y : Fin N → Em) : Em :=
  ∑ a, ∑ b, IsCMField.complexConj Em (x a) * H a b * y b

def trForm {N : ℕ} (ξ : Em) (H : Matrix (Fin N) (Fin N) Em) (x y : Fin N → Em) : ℚ :=
  Algebra.trace ℚ Em (ξ * hermForm Em H x y)

def signMat (N j : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun a => if (a : ℕ) < j then 1 else -1

structure HermDatum (Ψ : Type) [Fintype Ψ] (N j : ℕ) where

  emb : Ψ → (Em →+* ℂ)
  emb_inj : Function.Injective emb

  cmType : ∀ σ : Em →+* ℂ, (∃ τ, emb τ = σ) ↔ ¬ ∃ τ, emb τ = (starRingEnd ℂ).comp σ

  H : Matrix (Fin N) (Fin N) Em
  herm : ∀ a b, IsCMField.complexConj Em (H a b) = H b a

  ξ : Em
  ξ_ne : ξ ≠ 0
  ξ_conj : IsCMField.complexConj Em ξ = -ξ

  L : Submodule (𝓞 Em) (Fin N → Em)
  fg : (L.restrictScalars ℤ).FG
  span : Submodule.span ℚ (L : Set (Fin N → Em)) = ⊤

  selfDual : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ m : ℤ, trForm Em ξ H x y = m

  signature : ∀ τ, ∃ P : Matrix (Fin N) (Fin N) ℂ, IsUnit P.det ∧
    Pᴴ * H.map (emb τ) * P = signMat N j

  level : ℕ
  three_le_level : 3 ≤ level

variable {Em} {Ψ : Type} [Fintype Ψ] {N j : ℕ}

def HermDatum.IsIso (A : HermDatum Em Ψ N j) (I : Submodule (𝓞 Em) (Fin N → Em)) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, hermForm Em A.H v w = 0

def HermDatum.IsSat (A : HermDatum Em Ψ N j) (I : Submodule (𝓞 Em) (Fin N → Em)) : Prop :=
  ∀ v ∈ A.L, ∀ n : ℤ, n ≠ 0 → n • v ∈ I → v ∈ I

def HermDatum.lieComp (A : HermDatum Em Ψ N j) (hj : j ≤ N) (P : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ)
    (v : Fin N → Em) (c : Fin (N - j)) : ℂ :=
  (Real.sqrt (2 * ‖A.emb τ A.ξ‖) : ℂ) * (P⁻¹ *ᵥ fun a => A.emb τ (v a)) (tailIdx hj c)

def HermDatum.gramLie (A : HermDatum Em Ψ N j) (hj : j ≤ N) (P : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ)
    {ρ : ℕ} (v : Fin ρ → Fin N → Em) : Matrix (Fin ρ) (Fin ρ) ℂ :=
  Matrix.of fun a b => ∑ c, starRingEnd ℂ (A.lieComp hj P τ (v a) c) * A.lieComp hj P τ (v b) c

open Classical in

def HermDatum.nz (A : HermDatum Em Ψ N j) (hj : j ≤ N) (per : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (I : Submodule (𝓞 Em) (Fin N → Em)) : ℝ :=
  if h : ∃ ρ v, IsNzFamily I ρ v then
    (∏ τ, (A.gramLie hj (per τ) τ h.choose_spec.choose).det.re) /
      ((Submodule.span (𝓞 Em) (Set.range h.choose_spec.choose)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ)
  else 1

end Herm

structure FullerData (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type)
    [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (Em : Type) [Field Em] [NumberField Em] [IsCMField Em]
    extends ComponentDataHodge II Ψ K ι Ω E where

  herm : HermDatum Em Ψ N j

  per : ((Σ k, ι k) → ℂ) → Ψ → Matrix (Fin N) (Fin N) ℂ
  per_witt : ∀ z ∈ mcPts (mCoordIdeal y) \ Bd, ∀ τ,
    (per z τ)ᴴ * herm.H.map (herm.emb τ) * per z τ = signMat N j
  per_torus : ∀ z, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → per (torusSmul c z) = per z

  nStrata : ℕ

  stratum : Fin nStrata → Set ((Σ k, ι k) → ℂ)
  stratum_sub : ∀ s, stratum s ⊆ Bd
  stratum_cover : ∀ z ∈ Bd, ∃ s, z ∈ stratum s
  stratum_torus : ∀ s, ∀ z ∈ stratum s, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ stratum s

  torLat : Fin nStrata → Submodule (𝓞 Em) (Fin N → Em)
  torLat_le : ∀ s, torLat s ≤ herm.L
  torLat_ne : ∀ s, torLat s ≠ ⊥
  torLat_iso : ∀ s, herm.IsIso (torLat s)
  torLat_sat : ∀ s, herm.IsSat (torLat s)

  nz_near : ∀ s, ∀ z₀ ∈ stratum s, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ z ∈ mcPts (mCoordIdeal y) \ Bd,
    ‖z - z₀‖ < δ → herm.nz (j_le.trans (Nat.sub_le _ _)) (per z) (torLat s) < ε

  mu : HodgeData toComponentData
  mu_F : ∀ τ, mu.F τ = F τ

  htLat : ℕ → ∀ τ, ChartBundle ℤ (segreCoord y) N (E τ)
  ht_away : ∀ p ∈ S, ∀ τ c, segreCoord y c ≠ 0 → ∀ e : E τ,
    (∃ m : ℕ, ((p : Ω) ^ m) • e ∈ (W τ).lat c) ↔ ∃ m : ℕ, ((p : Ω) ^ m) • e ∈ (htLat p τ).lat c

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def nz (z : (Σ k, ι k) → ℂ) (I : Submodule (𝓞 Em) (Fin D.N → Em)) : ℝ :=
  D.herm.nz (D.j_le.trans (Nat.sub_le _ _)) (D.per z) I

def cuspU (z : (Σ k, ι k) → ℂ) : ℝ :=
  max 0 (⨆ s, -Real.log (D.nz z (D.torLat s)))

end FullerData

end GroundTheory.Heights₂.Heights.NineStatements
