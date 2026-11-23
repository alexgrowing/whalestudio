import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBaseExtensionStatement
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.BiratJoin

theorem psum_homogeneous_int (σ : Type) [Fintype σ] (n : ℕ) :
    (psum σ ℤ n).IsHomogeneous n := by
  unfold psum
  apply IsHomogeneous.sum
  intro i _
  simpa using (isHomogeneous_X ℤ i).pow n

theorem ckRelations_descend : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {Sg : Type} {r s : Sg → ℕ} (p : ℕ), (p : O) ≠ 0 → ∀ (φ : Equiv.Perm Sg) {VL VO : Sg → Type} [∀ τ, AddCommGroup (VL τ)] [∀ τ, Module Ω (VL τ)] [∀ τ, AddCommGroup (VO τ)] [∀ τ, Module Ω (VO τ)] (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (VL τ)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (VO τ)), (∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ)) → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ (Lie' W' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (r τ) (VL τ)) (Om' OmHT' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (s τ) (VO τ)), (∀ τ, IsPull O x z (Lie τ) (Lie' τ) ∧ IsPull O x z (W τ) (W' τ) ∧ IsPull O x z (Om τ) (Om' τ) ∧ IsPull O x z (OmHT τ) (OmHT' τ)) → CkRelations O (joinCoord x z) d p φ Lie' W' Om' OmHT' → CkRelations O x d p φ Lie W Om OmHT := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hx Sg r s p hp φ VL VO _ _ _ _ Lie W Om OmHT hsame K' _ _ ι' _ z hxz hfn
    Lie' W' Om' OmHT' hpull hck
  unfold CkRelations
  intro k hk1 hk2 q L Q hQ
  obtain ⟨h, hA, hB⟩ := hck k hk1 hk2 q (fun j => pullDeg (L j)) Q hQ
  have hc : k - 1 ≤ d := by omega
  have hQ' : Q.IsHomogeneous (d - (k - 1)) := by
    have e : d - (k - 1) = d + 1 - k := by omega
    rw [e]
    exact hQ
  have TL := fun τ => GlobalTheory.T.same_generic_base_extension O Ω K ι x d hx (r τ) (VL τ) (Lie τ) (W τ) (hsame τ).1 K' ι' z hxz hfn
    (Lie' τ) (W' τ) (hpull τ).1 (hpull τ).2.1
  have TO := fun τ => GlobalTheory.T.same_generic_base_extension O Ω K ι x d hx (s τ) (VO τ) (Om τ) (OmHT τ) (hsame τ).2 K' ι' z hxz hfn
    (Om' τ) (OmHT' τ) (hpull τ).2.2.1 (hpull τ).2.2.2
  have hroot : ∀ τ, rootNum O (joinCoord x z) d (r τ) (Lie' τ) (MvPolynomial.psum (Fin (r τ)) ℤ (k - 1))
      (fun j => pullDeg (L j)) Q (p : O) =
      rootNum O x d (r τ) (Lie τ) (MvPolynomial.psum (Fin (r τ)) ℤ (k - 1)) L Q (p : O) := fun τ =>
    (TL τ).2 (k - 1) _ (MvPolynomial.psum_isSymmetric _ _ _) (psum_homogeneous_int _ _) hc q L Q hQ' _ hp
  refine ⟨h, fun τ => ?_, fun τ => ?_⟩
  · rw [← (TL τ).1 k hk1 hk2 q L Q hQ, ← (TO τ).1 k hk1 hk2 q L Q hQ, ← hroot τ]
    exact hA τ
  · rw [← hroot (φ τ)]
    exact hB τ

end GlobalTheory.CompanionTheory.Ar.Num.BiratJoin
