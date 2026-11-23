import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DescentIntersectionNumberStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ConstantsMonomialApproximationStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem mem_of_residue_map_mem_specialIdeal {K : Type} [DecidableEq K] {ι : K → Type} {O : Type}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {W : Ideal (MRing ι O)}
    (hW : (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O) ≤ W) {f : MRing ι O}
    (hf : MvPolynomial.map (IsLocalRing.residue O) f ∈ specialIdeal W) : f ∈ W := by
  obtain ⟨g, hg, hgf⟩ := (Ideal.mem_map_iff_of_surjective _
    (MvPolynomial.map_surjective _ IsLocalRing.residue_surjective)).1 hf
  have hker : f - g ∈ W := by
    apply hW
    rw [MvPolynomial.mem_map_C_iff]
    intro d
    rw [← IsLocalRing.residue_eq_zero_iff]
    have h := congrArg (MvPolynomial.coeff d) hgf
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at h
    rw [MvPolynomial.coeff_sub, map_sub, h, sub_self]
  have := W.add_mem hker hg
  simpa using this

theorem map_mem_pointIdeal {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {A O : Type} [CommRing A] [CommRing O] [Algebra A O] [Algebra A Ω]
    [Algebra O Ω] [IsScalarTower A O Ω] {f : MRing ι A} (hf : f ∈ pointIdeal A y) :
    MvPolynomial.map (algebraMap A O) f ∈ pointIdeal O y := by
  rw [pointIdeal, RingHom.mem_ker] at hf ⊢
  rw [← hf]
  simp only [pointConeMap]
  exact MvPolynomial.aeval_map_algebraMap _ _ _

theorem isMultiHomog_map {K : Type} [DecidableEq K] {ι : K → Type} {R S : Type} [CommRing R]
    [CommRing S] (φ : R →+* S) {G : MRing ι R} {b : K → ℕ} (hG : IsMultiHomog G b) :
    IsMultiHomog (MvPolynomial.map φ G) b := by
  intro d hd
  apply hG
  intro h0
  apply hd
  rw [MvPolynomial.coeff_map, h0, map_zero]

theorem intNumL_zmod_eq_residueDegree_mul_vNumL : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], HasConstants ℤ A y → ∀ (p : ℕ) [Fact p.Prime] (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], (p : A) ∈ m → ∀ fd : ℕ, Nat.card (A ⧸ m) = p ^ fd → ∀ W' : Ideal (MRing ι O), W'.IsPrime → IsMultiHomogIdeal W' → pointIdeal O y ≤ W' → (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O) ≤ W' → ∀ l : List (K → ℤ), intNumL (ZMod p) (extTo (ZMod p) (W'.comap (MvPolynomial.map (Int.castRingHom O)))) l = (fd : ℤ) * vNumL W' l := by
  intro K _ _ ι _ Ω _ y A _ _ _ _ hconst p _ m _ O _ _ _ _ _ _ _ hpm fd hcard W' hWp hWh hpt hϖ l
  have hmne : m ≠ ⊥ := by
    intro h
    apply IsDiscreteValuationRing.not_a_field O
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m O, h, Ideal.map_bot]
  haveI hmax : m.IsMaximal := Ideal.IsPrime.isMaximal ‹_› hmne
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal m O
  have hsurj : ∀ x : IsLocalRing.ResidueField O, ∃ a : A,
      IsLocalRing.residue O (algebraMap A O a) = x := by
    intro x
    obtain ⟨q, hq⟩ := e.surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨a, ?_⟩
    rw [← hq]
    exact (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk m O a).symm
  have hcardκ : Nat.card (IsLocalRing.ResidueField O) = p ^ fd :=
    (Nat.card_congr e.toEquiv).symm.trans hcard
  have hp0 : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    have h1 : algebraMap A O (p : A) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff O m _).2 hpm
    have h2 := (IsLocalRing.residue_eq_zero_iff _).2 h1
    simpa using h2
  haveI hchar : CharP (IsLocalRing.ResidueField O) p := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 (ringChar.dvd hp0) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h ▸ ringChar.charP _
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField O) := ZMod.algebra _ p
  haveI hfin : Finite (IsLocalRing.ResidueField O) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcardκ]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  haveI : FiniteDimensional (ZMod p) (IsLocalRing.ResidueField O) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p) (IsLocalRing.ResidueField O) = fd := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := IsLocalRing.ResidueField O)
    rw [hcardκ, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  have hhom : (algebraMap (ZMod p) (IsLocalRing.ResidueField O)).comp
      (Int.castRingHom (ZMod p)) = (IsLocalRing.residue O).comp (Int.castRingHom O) :=
    Subsingleton.elim _ _
  have hmm : ∀ g : MRing ι ℤ,
      MvPolynomial.map (algebraMap (ZMod p) (IsLocalRing.ResidueField O))
        (MvPolynomial.map (Int.castRingHom (ZMod p)) g) =
      MvPolynomial.map (IsLocalRing.residue O) (MvPolynomial.map (Int.castRingHom O) g) := by
    intro g
    rw [MvPolynomial.map_map, MvPolynomial.map_map, hhom]
  have hcomap : (specialIdeal W').comap
      (MvPolynomial.map (algebraMap (ZMod p) (IsLocalRing.ResidueField O))) =
      extTo (ZMod p) (W'.comap (MvPolynomial.map (Int.castRingHom O))) := by
    have hs : Function.Surjective
        (MvPolynomial.map (σ := (Σ k, ι k)) (Int.castRingHom (ZMod p))) :=
      MvPolynomial.map_surjective _ (ZMod.ringHom_surjective _)
    ext g
    obtain ⟨g0, rfl⟩ := hs g
    rw [Ideal.mem_comap, hmm, extTo]
    constructor
    · intro h
      exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.2 (mem_of_residue_map_mem_specialIdeal hϖ h))
    · intro h
      obtain ⟨g1, hg1, hg⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 h
      rw [← hmm, ← hg, hmm]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.1 hg1)
  have hsu : ∀ (c : ∀ k, ι k) (a : IsLocalRing.ResidueField O), ∃ (n : ℕ)
      (G : MRing ι (ZMod p)), IsMultiHomog G (fun _ => n) ∧
      C a * (∏ k, X ⟨k, c k⟩) ^ n -
        MvPolynomial.map (algebraMap (ZMod p) (IsLocalRing.ResidueField O)) G ∈
        specialIdeal W' := by
    intro c a
    obtain ⟨a0, rfl⟩ := hsurj a
    obtain ⟨n, G, hG, hmem⟩ := GlobalTheory.T.constants_monomial_approximation K ι Ω y A hconst c a0
    refine ⟨n, MvPolynomial.map (Int.castRingHom (ZMod p)) G, isMultiHomog_map _ hG, ?_⟩
    have h1 := hpt (map_mem_pointIdeal (O := O) hmem)
    have h2 : MvPolynomial.map (IsLocalRing.residue O) _ ∈ specialIdeal W' :=
      Ideal.mem_map_of_mem _ h1
    rw [hmm]
    have hG' : MvPolynomial.map (IsLocalRing.residue O) (MvPolynomial.map (algebraMap A O)
        (MvPolynomial.map (Int.castRingHom A) G)) =
        MvPolynomial.map (IsLocalRing.residue O) (MvPolynomial.map (Int.castRingHom O) G) := by
      simp only [MvPolynomial.map_map]
      exact congrArg (fun φ : ℤ →+* IsLocalRing.ResidueField O => MvPolynomial.map φ G)
        (Subsingleton.elim _ _)
    simpa [hG'] using h2
  have key := GlobalTheory.T.descent_intersection_number K ι (ZMod p) (IsLocalRing.ResidueField O) (specialIdeal W')
    (SpecialIdealMultiHomog.full O K ι W' hWh) hsu l
  rw [hcomap, hfr] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.Num
