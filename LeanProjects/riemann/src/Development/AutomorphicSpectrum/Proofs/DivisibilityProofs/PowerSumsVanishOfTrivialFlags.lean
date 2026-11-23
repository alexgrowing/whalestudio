import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagFramePointDimensionStatement

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ZTop

theorem isFibreComp_variety {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {W : Ideal (MRing ι O)} (hW : IsFibreComp P W) :
    IsMultiProjPrime (specialIdeal W) ∧
      ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hmin, hrel⟩ := hW
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hmin
  refine PairNumberJoinLeft.verticalComponentFibre O ϖ hϖ K ι P d hP (C ϖ) 0
    (isWeightedHomogeneous_C _ _) (fun h => hϖ.ne_zero ?_) W hmin hrel
    (hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  exact Ideal.mem_bot.mp (hP.noTorsion ▸ Ideal.mem_comap.mpr h)

theorem cast_classNum {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ : Type} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) :
    ((classNum cls H Q W : ℤ) : ℝ) =
      genNum (IsLocalRing.ResidueField O) (specialIdeal W) cls (MvPolynomial.map (Int.castRingHom ℝ) H) Q := by
  unfold classNum genNum
  rw [MvPolynomial.support_map_of_injective _ (RingHom.injective_int (Int.castRingHom ℝ))]
  push_cast
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_map]
  rfl

theorem powerSumsVanish_of_trivFlagAt :
    NumericalSegre.Statement → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
      Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (N : ℕ) (x : Fin N → K → ℤ),
      (∀ W, IsFibreComp P W → TrivFlagAt W x) → PowerSumsVanish P d x := by
  intro hS O _ _ _ ϖ hϖ K _ _ ι _ P d hP N x hx W hW k hk Q hQ
  obtain ⟨Ω, _, _, y, w, hy, hflag⟩ := hx W hW
  obtain ⟨hprime, hdim⟩ := isFibreComp_variety hϖ hP hW
  have h := GlobalTheory.T.flag_frame_point_dimension hS (IsLocalRing.ResidueField O) Ω K ι y d (hy ▸ hprime) (hy ▸ hdim) N w x hflag
    k hk Q hQ
  have hmap : MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin N) ℤ k) = ∑ i, X i ^ k := by
    simp [psum]
  have h2 := cast_classNum x (psum (Fin N) ℤ k) Q W
  rw [hmap, ← hy, h] at h2
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.Num.ZTop
