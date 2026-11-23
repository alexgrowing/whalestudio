import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenFree
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  [Fintype S] {N : ℕ} [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hev : Even N)

def GsTauBijective (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) : Prop :=
  ∀ τ : compactCohomologyRes (mackeyFamily U (gsFinFamily S ιs))
      (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S N)) 3 →+ ZMod N,
    Function.Surjective τ → ∀ {r s : ℕ} (h : r + s = 3),
      Function.Bijective (compactZmodDualityMap (mackeyFamily U (gsFinFamily S ιs))
        (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S N)) (nsmul_gsRoots S N) τ h)

set_option maxHeartbeats 1000000 in
include hS hev in

theorem gsTauBijective_gsOpenSubgroup {L : FiniteSubfield} [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (hU : gsOpenSubgroup S hL ≤ W₀) : GsTauBijective S ιs (N := N) (gsOpenSubgroup S hL) := by
  intro τ hτ r s h
  have hTC := isTotallyComplex_of_gsOpenSubgroup_le S hS hev hL W₀ hW₀ hU
  let := fintypePlacesOver (L := L) S
  have : Nonempty (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
    nonempty_placesOver_of_natCast_mem S Nat.prime_two (mem_of_natCast_two_mem_of_even S hS hev)
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L.1), ((N : ℕ) : 𝓞 L.1) ∈ w.asIdeal → w ∈ placesOver S :=
    fun w hw => mem_placesOver_of_natCast_mem hS hw
  exact bijective_compactZmodDualityMap_gsOpenSubgroup_of_surjective S ιs hL N τ hτ _
    (gsLevelBijective_gsCompactInv (placesOver S) (gsMackeyEmbeddings hL ιs) hSL (Or.inr hTC)) h

end GroundTheory.ProfCoh
