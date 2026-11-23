import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuadraticCharacterPrescribedPlaces
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPointLocalizationPrimeStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.UnitarySelfGeneration

theorem latagree_le (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X]
    (hξ : IsCptGen ξ) (T : Set (Cpt ξ)) (hT : ∀ p ∈ T, ∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T)
    (hn : ∀ p ∈ T, IsIntegrallyClosed (X.presheaf.stalk p.1)) (E : Type) [AddCommGroup E] [Module Ω E]
    (L L' : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (hL : L.IsVBOn T r V) (hL' : L'.IsVBOn T r V)
    (h1 : ∀ p ∈ T, ringKrullDim (X.presheaf.stalk p.1) = 1 → L p = L' p) (p : Cpt ξ) (hp : p ∈ T) :
    L' p ≤ L p := by
  obtain ⟨U, hU, b, hb, hbq⟩ := hL p hp
  obtain ⟨U', hU', b', hb', hbq'⟩ := hL' p hp
  obtain ⟨hfr, hno, hic⟩ := GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ hξ p
  haveI := hfr
  haveI := hno inferInstance
  haveI := hic (hn p hp)
  have key := GlobalTheory.CompanionTheory.HeightOneFrame.integral_of_integral_at_height_one (regAt ξ p) Ω E r b b'
    (hbq p hp hU).1 ?_ ?_
  · rw [(hbq' p hp hU').2, (hbq p hp hU).2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := key i
    rw [hc]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ (c k) (Submodule.subset_span ⟨k, rfl⟩)
  · intro P hP i
    obtain ⟨q, hqp, hq⟩ := GlobalTheory.T.exists_point_localization_prime X Ω ξ hξ p P.asIdeal P.isPrime
    have hqT := hT p hp q hqp
    have hle : regAt ξ p ≤ regAt ξ q := fun a ha =>
      (hq a).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by simpa using ha⟩
    letI : Algebra (regAt ξ p) (regAt ξ q) := (Subring.inclusion hle).toAlgebra
    haveI : IsLocalization.AtPrime (regAt ξ q) P.asIdeal := by
      refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
      · rintro ⟨s, hs⟩
        have hs0 : (s : Ω) ≠ 0 := fun h => hs (by
          have : s = 0 := Subtype.ext h
          rw [this]; exact P.asIdeal.zero_mem)
        have hi : (s : Ω)⁻¹ ∈ regAt ξ q := (hq _).2 ⟨s, hs, by rw [mul_inv_cancel₀ hs0]; exact one_mem _⟩
        exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hs0))
      · intro z
        obtain ⟨s, hs, hz⟩ := (hq z).1 z.2
        exact ⟨(⟨_, hz⟩, ⟨s, hs⟩), Subtype.ext (mul_comm _ _)⟩
      · intro x y hxy
        have : x = y := Subtype.ext (congrArg Subtype.val hxy :)
        exact ⟨1, by rw [this]⟩
    have hdim : ringKrullDim (X.presheaf.stalk q.1) = 1 := by
      have e : X.presheaf.stalk q.1 ≃+* regAt ξ q := RingEquiv.ofBijective (genMap ξ q).rangeRestrict
        ⟨fun x y h => hξ.inj q (congrArg Subtype.val h :), (genMap ξ q).rangeRestrict_surjective⟩
      rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal, hP]
      rfl
    have hmem : b' i ∈ L q := by
      rw [h1 q hqT hdim, (hbq' q hqT (hqp.mem_open U'.2 hU')).2]
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [(hbq q hqT (hqp.mem_open U.2 hU)).2, Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite P.asIdeal.primeCompl c
    choose d hd using hs
    refine ⟨s.1, d, s.2, ?_⟩
    rw [← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h2 : algebraMap (regAt ξ p) Ω (d k) = algebraMap (regAt ξ p) Ω s.1 * (c k : Ω) := by
      have := congrArg Subtype.val (hd k)
      rw [Algebra.smul_def] at this
      exact this
    rw [h2, mul_smul]
    rfl
  · intro i
    rw [hb, ← hb']
    exact Submodule.subset_span ⟨i, rfl⟩

theorem lattices_agree_of_height_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → ∀ (T : Set (Cpt ξ)), (∀ p ∈ T, ∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p ∈ T, IsIntegrallyClosed (X.presheaf.stalk p.1)) → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (L L' : Lat ξ E) (r : ℕ) (V : Submodule Ω E), L.IsVBOn T r V → L'.IsVBOn T r V → (∀ p ∈ T, ringKrullDim (X.presheaf.stalk p.1) = 1 → L p = L' p) → ∀ p ∈ T, L p = L' p := by
  intro X Ω _ ξ _ hξ T hT hn E _ _ L L' r V hL hL' h1 p hp
  exact le_antisymm
    (latagree_le X Ω ξ hξ T hT hn E L' L r V hL' hL (fun p hp h => (h1 p hp h).symm) p hp)
    (latagree_le X Ω ξ hξ T hT hn E L L' r V hL hL' h1 p hp)

end PositivityTheory.UnitarySelfGeneration
