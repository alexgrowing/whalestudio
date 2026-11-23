import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

open Cardinal in

private theorem UpperTheory.nonempty_embedding_complex (K : Type) [Field K] [CharZero K] [Countable K] :
    Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    have hK : #K ≤ 𝔠 := Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

private theorem UpperTheory.countable_of_essFiniteType_int (K : Type) [CommRing K] [Algebra.EssFiniteType ℤ K] :
    Countable K := by
  have hA : Countable (Algebra.EssFiniteType.subalgebra ℤ K) := by
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
      (inferInstance : Algebra.FiniteType ℤ (Algebra.EssFiniteType.subalgebra ℤ K))
    have : Countable (MvPolynomial (Fin n) ℤ) :=
      Cardinal.mk_le_aleph0_iff.1 (MvPolynomial.cardinalMk_le_max.trans (by simp))
    exact hf.countable
  exact Cardinal.mk_le_aleph0_iff.1
    ((IsLocalization.cardinalMk_le (Algebra.EssFiniteType.submonoid ℤ K)).trans Cardinal.mk_le_aleph0)

theorem UpperTheory.exists_complex_embedding_extension :
    ∀ (k K : Type) [Field k] [NumberField k] [Field K] (ψ : k →+* K) (σ : k →+* ℂ), Algebra.EssFiniteType ℤ K → ∃ j : K →+* ℂ, j.comp ψ = σ := by
  intro k K _ _ _ ψ σ h
  have : Countable K := UpperTheory.countable_of_essFiniteType_int K
  have : Countable k := ψ.injective.countable
  have : CharZero K := (RingHom.charZero_iff ψ.injective).1 inferInstance
  obtain ⟨j⟩ := UpperTheory.nonempty_embedding_complex K
  obtain ⟨e, he⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (j.comp ψ) σ
  exact ⟨e.toRingHom.comp j, RingHom.ext fun a => he a⟩
