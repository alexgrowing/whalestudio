import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem germ_isUnit_and_surj {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (y : X) (hy : y ∈ U) :
    (∀ a : Γ(X, U), IsUnit (X.presheaf.germ U y hy a) ↔ a ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
    ∀ g : X.presheaf.stalk y, ∃ b c : Γ(X, U), b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      g * X.presheaf.germ U y hy b = X.presheaf.germ U y hy c := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : U)
  have hl : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  refine ⟨fun a => ?_, fun g => ?_⟩
  · exact IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk y)
      (hU.primeIdealOf ⟨y, hy⟩).asIdeal a
  · obtain ⟨⟨c, ⟨b, hb⟩⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl g
    exact ⟨b, c, hb, h⟩

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

theorem genMap_germ {U : X.Opens} (p : Cpt ξ) (hp : p.1 ∈ U) (hg : genPt ξ ∈ U) (a : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp a) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg a) := by
  have h : X.presheaf.germ U p.1 hp ≫ X.presheaf.stalkSpecializes p.2 = X.presheaf.germ U (genPt ξ) hg :=
    TopCat.Presheaf.germ_stalkSpecializes _ _ _
  simp only [genMap, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← h]
  rfl

theorem genMap_stalkSpecializes (p q : Cpt ξ) (h : q.1 ⤳ p.1) (g : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes h).hom g) = genMap ξ p g := by
  have h2 : X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes q.2 =
      X.presheaf.stalkSpecializes p.2 := TopCat.Presheaf.stalkSpecializes_comp _ _ _
  simp only [genMap]
  rw [← h2]
  rfl

end GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_prime_generisation : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (I : Ideal (regAt ξ p)), I.IsPrime → ∃ q : Cpt ξ, q.1 ⤳ p.1 ∧ ∀ a : Ω, a ∈ regAt ξ q ↔ ∃ s : regAt ξ p, s ∉ I ∧ (s : Ω) * a ∈ regAt ξ p := by
  intro X Ω _ ξ hξ p I hI
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := p.1) (U := ⊤) trivial
  have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  let ρ : X.presheaf.stalk p.1 →+* regAt ξ p := (genMap ξ p).rangeRestrict
  have hρ : ∀ r, ((ρ r : regAt ξ p) : Ω) = genMap ξ p r := fun _ => rfl
  have hρs : Function.Surjective ρ := (genMap ξ p).rangeRestrict_surjective
  let J : Ideal (X.presheaf.stalk p.1) := I.comap ρ
  have hJ : J.IsPrime := Ideal.comap_isPrime ρ I
  let gp : Γ(X, U) →+* X.presheaf.stalk p.1 := (X.presheaf.germ U p.1 hpU).hom
  let Q0 : PrimeSpectrum Γ(X, U) := ⟨J.comap gp, Ideal.comap_isPrime gp J⟩
  have hspec : ∀ P Q : PrimeSpectrum Γ(X, U), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q := by
    intro P Q
    rw [PrimeSpectrum.le_iff_specializes]
    exact hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff
  have hqU : hU.fromSpec Q0 ∈ U := by
    have : hU.fromSpec Q0 ∈ Set.range hU.fromSpec := ⟨Q0, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hQ0 : hU.primeIdealOf ⟨_, hqU⟩ = Q0 :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  have hP := hU.fromSpec_primeIdealOf ⟨p.1, hpU⟩
  have hG := hU.fromSpec_primeIdealOf ⟨genPt ξ, hgU⟩
  obtain ⟨hPu, hPs⟩ := germ_isUnit_and_surj hU p.1 hpU
  obtain ⟨hGu, -⟩ := germ_isUnit_and_surj hU (genPt ξ) hgU
  obtain ⟨hQu, hQs⟩ := germ_isUnit_and_surj hU _ hqU
  rw [hQ0] at hQu hQs
  have hunitJ : ∀ r, IsUnit r → r ∉ J := fun r hr hrJ => hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ hrJ hr)

  have hGQ : hU.primeIdealOf ⟨genPt ξ, hgU⟩ ≤ Q0 := by
    intro a ha
    let φ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
    have hφ : Function.Bijective φ := hξ.bij
    have h0 : φ (X.presheaf.germ U (genPt ξ) hgU a) = 0 := by
      by_contra hne
      obtain ⟨d, hd⟩ := hφ.2 (φ (X.presheaf.germ U (genPt ξ) hgU a))⁻¹
      have h1 : X.presheaf.germ U (genPt ξ) hgU a * d = 1 := by
        apply hφ.1
        rw [map_mul, hd, map_one, mul_inv_cancel₀ hne]
      exact (not_not.mpr ha) ((hGu a).1 (IsUnit.of_mul_eq_one _ h1))
    have h2 : gp a = 0 := by
      apply hξ.inj p
      rw [map_zero, ← h0]
      exact genMap_germ ξ p hpU hgU a
    show gp a ∈ J
    rw [h2]
    exact J.zero_mem
  have hQP : Q0 ≤ hU.primeIdealOf ⟨p.1, hpU⟩ := by
    intro a ha
    by_contra hn
    exact hunitJ _ ((hPu a).2 hn) ha
  have hqp : hU.fromSpec Q0 ⤳ p.1 := by
    have := (hspec _ _).2 hQP
    rwa [hP] at this
  have hgq : genPt ξ ⤳ hU.fromSpec Q0 := by
    have := (hspec _ _).2 hGQ
    rwa [hG] at this
  let q : Cpt ξ := ⟨hU.fromSpec Q0, hgq⟩
  let σ : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1 := (X.presheaf.stalkSpecializes hqp).hom
  have hσ : ∀ g, genMap ξ q (σ g) = genMap ξ p g := genMap_stalkSpecializes ξ p q hqp
  have hσg : ∀ a : Γ(X, U), σ (X.presheaf.germ U p.1 hpU a) = X.presheaf.germ U q.1 hqU a :=
    fun a => X.presheaf.germ_stalkSpecializes_apply hpU hqp a
  refine ⟨q, hqp, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨b, c, hb, hbc⟩ := hQs g
    refine ⟨ρ (X.presheaf.germ U p.1 hpU b), hb, ⟨X.presheaf.germ U p.1 hpU c, ?_⟩⟩
    rw [hρ, ← hσ, ← hσ, hσg, hσg, ← hbc, map_mul, mul_comm]
  · rintro ⟨s, hs, t, ht⟩
    obtain ⟨r, rfl⟩ := hρs s
    have hrJ : r ∉ J := hs
    obtain ⟨b, c, hb, hbc⟩ := hPs r
    have hbu := (hPu b).2 hb
    have hcJ : X.presheaf.germ U p.1 hpU c ∉ J := by
      rw [← hbc]
      intro h
      exact (hJ.mem_or_mem h).elim hrJ (hunitJ _ hbu)
    have hcu := (hQu c).2 hcJ
    have hσr : IsUnit (σ r) := by
      rw [← hσg, ← hbc, map_mul] at hcu
      exact isUnit_of_mul_isUnit_left hcu
    obtain ⟨u, hu⟩ := hσr
    refine ⟨(↑u⁻¹ : X.presheaf.stalk q.1) * σ t, ?_⟩
    have hne : genMap ξ q (σ r) * genMap ξ q (↑u⁻¹ : X.presheaf.stalk q.1) = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [map_mul, hσ, ht, hρ, ← hσ r, ← _root_.mul_assoc, mul_comm (genMap ξ q _), hne, _root_.one_mul]

end GlobalTheory.CompanionTheory.Ar
