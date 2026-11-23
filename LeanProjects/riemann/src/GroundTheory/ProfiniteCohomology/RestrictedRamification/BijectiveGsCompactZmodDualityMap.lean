import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInv
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocalDual
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseSwap
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S] [Nonempty S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (n : ℕ) [NeZero n] (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1) (hodd : Odd n ∨ IsTotallyComplex K.1)
  (h3 : Subsingleton (cohomology (gsRoots S n) 3))

include ℓ k hℓ hnk hS hμ in

theorem BaseDualityHypotheses.of_gs
    (h3Z : Subsingleton (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 3))
    (hfin1 : Finite (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1))
    (hfin2 : Finite (compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2))
    (hleft : ∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → x = 0)
    (hright : ∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
      (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → y = 0) :
    BaseDualityHypotheses (gsFinFamily S ιs) (gsRoots S n) (nsmul_gsRoots S n) (gsLocalInvRoots S ιs n)
      (gsCompactInv S ιs n hodd h3) where
  triv := gsRoots_ρ_apply_of_mem S n hμ
  nonempty_addEquiv := nonempty_addEquiv_gsRoots S n hμ
  loc_one v := (bijective_gsLocalPairing_one S ιs n hμ v).2
  loc_two v := bijective_gsLocalPairing_two S ιs n hμ v
  bijective_alt := bijective_gsCompactInv_of_mem S n ιs ℓ k hℓ hnk hS hμ hodd h3
  T_localToCompact := gsCompactInv_localToCompact S ιs n hodd h3
  three_zmod := h3Z
  three_D := h3
  finite_one := hfin1
  finite_two := hfin2
  ker_left := hleft
  ker_right := hright
  swap yc xc := congrArg (gsCompactInv S ιs n hodd h3)
    (compactCupRes_zmodMulPairingRight_swap (gsFinFamily S ιs) (gsRoots S n) (nsmul_gsRoots S n)
      (_root_.GroundTheory.ProfCoh.localToCompact_two_surjective S ιs n h3) yc xc)

include ℓ k hℓ hnk hS hμ in

theorem bijective_gs_compactZmodDualityMap
    (h3Z : Subsingleton (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 3))
    (hfin1 : Finite (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1))
    (hfin2 : Finite (compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2))
    (hleft : ∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → x = 0)
    (hright : ∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
      (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → y = 0)
    {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactZmodDualityMap (gsFinFamily S ιs) (gsRoots S n) (nsmul_gsRoots S n)
      (gsCompactInv S ιs n hodd h3) h) :=
  (BaseDualityHypotheses.of_gs S ιs n ℓ k hℓ hnk hS hμ hodd h3 h3Z hfin1 hfin2 hleft hright).bijective_compactZmodDualityMap h

end

end GroundTheory.ProfCoh
