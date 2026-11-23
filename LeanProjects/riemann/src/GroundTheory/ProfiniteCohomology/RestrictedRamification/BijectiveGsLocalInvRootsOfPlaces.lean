import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLevel
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFixed
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInputs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Local

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
include hnS

set_option maxHeartbeats 1600000 in

theorem bijective_gsRootsLocalMor_of_places (v : S) : Function.Bijective (gsRootsLocalMor S ιs n v).hom :=
  (exists_isPrimitiveRoot_maxUnramifiedOutside K S n (NeZero.ne n) hnS).elim fun _ hz =>
    Additive.ofMul.bijective.comp ((bijective_rootsOfUnityMapHom n
      ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom hz).comp Additive.toMul.bijective)

theorem bijective_gsLocalInvRoots_of_places (v : S) : Function.Bijective (gsLocalInvRoots S ιs n v) := by
  have e : ⇑(gsLocalInvRoots S ιs n v) =
      (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        (natCast_ne_zero_adicCompletion S n v)).tTop ∘ (cohomologyMap (gsRootsLocalMor S ιs n v) 2).hom :=
    funext (gsLocalInvRoots_eq S ιs n v)
  rw [e]
  exact (bijective_localDualityHypotheses_tTop S n v).comp
    (bijective_cohomologyMap_of_bijective _ (bijective_gsRootsLocalMor_of_places S ιs n hnS v) 2)

end Local

section P1

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

def GsPairingNondegenerate : Prop :=
  (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → x = 0) ∧
    (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
      (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → y = 0)

end P1

section Level

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (n ℓ k : ℕ) [NeZero n] (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

def GsPairingInput (n ℓ : ℕ) [NeZero n] : Prop :=
  ∀ (L : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 L.1))) [Fintype S']
    (ιs' : ∀ v : S', ℚ̄ →ₐ[L.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 L.1)).adicCompletion L.1)),
    (∀ v : HeightOneSpectrum (𝓞 L.1), ((ℓ : ℕ) : 𝓞 L.1) ∈ v.asIdeal → v ∈ S') →
    (∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ L.1) → ∀ (hodd' : Odd n ∨ IsTotallyComplex L.1)
    (h3' : Subsingleton (cohomology (gsRoots S' n) 3)), GsPairingNondegenerate S' ιs' n hodd' h3'

omit [Fintype S] [NeZero n] in
include hnk hS in

theorem natCast_not_mem_of_not_mem : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal :=
  fun v hv h => hv (mem_of_natCast_pow_mem S n ℓ k hnk hS v h)

set_option maxHeartbeats 3200000 in
include hℓ hnk hS in

theorem gsBaseBijective_of_le (hP : GsPairingInput n ℓ)
    (hcores : ∀ U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      Function.Surjective (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ n = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    {L : FiniteSubfield} [Fact (K ≤ L)] (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hUW : gsOpenSubgroup S hL ≤ W₀) :
    GsBaseBijective S ιs n (gsOpenSubgroup S hL) (gsCompactInv S ιs n hodd h3) := by
  have hnS := natCast_not_mem_of_not_mem S n ℓ k hnk hS
  have : Nonempty S := nonempty_of_natCast_mem S ℓ hℓ hS
  let := fintypePlacesOver (L := L) S
  have : Nonempty (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
    nonempty_placesOver_of_natCast_mem S hℓ hS
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L.1), ((ℓ : ℕ) : 𝓞 L.1) ∈ w.asIdeal → w ∈ placesOver S :=
    fun w hw => mem_placesOver_of_natCast_mem hS hw
  have hμL : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ L.1 :=
    rootsOfUnity_mem_of_gsOpenSubgroup_le S n hL W₀ hW₀ hUW (NeZero.ne n) hnS
  have hoddL : Odd n ∨ IsTotallyComplex L.1 := hodd.imp id fun h => by
    have := h
    exact isTotallyComplex_of_algebra K.1 L.1
  have h3L := subsingleton_gsRoots_three (placesOver S) n ℓ k hnk hSL hoddL
  have hPL := hP L (placesOver S) (gsMackeyEmbeddings hL ιs) hSL hμL hoddL h3L
  have hsurj : GsCoresSurjective S ιs n (gsOpenSubgroup S hL) (gsCompactInv S ιs n hodd h3) :=
    (surjective_gsCompactInv S n ιs hodd h3 fun v =>
      (bijective_gsLocalInvRoots_of_places S ιs n hnS v).2).comp (hcores _)
  intro r s h
  exact bijective_zmodCompactDualityMap_gsOpenSubgroup S ιs hL n _
    (gsCompactInv (placesOver S) (gsMackeyEmbeddings hL ιs) n hoddL h3L)
    ⟨bijective_gsCompactInv_of_mem (placesOver S) n (gsMackeyEmbeddings hL ιs) ℓ k hℓ hnk hSL hμL hoddL h3L,
      fun h => bijective_gs_compactZmodDualityMap (placesOver S) (gsMackeyEmbeddings hL ιs) n ℓ k hℓ hnk hSL hμL
        hoddL h3L (subsingleton_zmodRep_gs_three (placesOver S) n ℓ k hnk hSL hoddL)
        (finite_zmodRep_gs_one (placesOver S) n ℓ k hnk hSL)
        (finite_gsRoots_compact_two (placesOver S) n ℓ k hnk hSL (gsMackeyEmbeddings hL ιs)) hPL.1 hPL.2 h⟩ hsurj h

end Level

end

end GroundTheory.ProfCoh
