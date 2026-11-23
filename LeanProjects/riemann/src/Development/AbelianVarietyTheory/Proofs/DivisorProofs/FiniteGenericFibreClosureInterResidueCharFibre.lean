import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimQuotientLeOfMinimalPrimes

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open scoped TensorProduct

namespace GlobalTheory.GenFibClosure

theorem finite_of_finite_spec (K S : Type) [Field K] [CommRing S] [Algebra K S] [Algebra.FiniteType K S]
    [Finite (PrimeSpectrum S)] : Module.Finite K S := by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := K)
  have : DiscreteTopology (PrimeSpectrum S) := JacobsonSpace.discreteTopology (Set.toFinite _)
  exact (Module.finite_iff_krullDimLE_zero K S).2
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.1 this).2

theorem isAlgebraic_of_injective {B S : Type} [CommRing B] [CommRing S] [Algebra ℚ S] [Module.Finite ℚ S]
    (f : B →+* S) (hf : Function.Injective f) : Algebra.IsAlgebraic ℤ B := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℤ S := Algebra.IsAlgebraic.trans ℤ ℚ S
  exact Algebra.IsAlgebraic.of_injective f.toIntAlgHom hf

theorem finiteType_of_surjective {A B : Type} [CommRing A] [CommRing B] [Algebra.FiniteType ℤ A]
    (f : A →+* B) (hf : Function.Surjective f) : Algebra.FiniteType ℤ B :=
  Algebra.FiniteType.of_surjective f.toIntAlgHom hf

theorem isAlgebraic_of_finite (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (h : {Q : PrimeSpectrum B | ∀ n : ℕ, n ≠ 0 → (n : B) ∉ Q.asIdeal}.Finite) : Algebra.IsAlgebraic ℤ B := by
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)
  let S := ℚ ⊗[ℤ] B
  letI : Algebra B S := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization M S := IsLocalization.tensorRight ℚ (nonZeroDivisors ℤ)
  have hinj := PrimeSpectrum.localization_comap_injective S M
  have hfin : Finite (PrimeSpectrum S) := by
    refine Set.finite_univ_iff.1 (Set.Finite.of_finite_image (h.subset ?_) hinj.injOn)
    rintro _ ⟨Q, -, rfl⟩ n hn hQ
    have h1 : (n : S) ∈ Q.asIdeal := by
      have := hQ
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at this
      exact this
    have h2 : IsUnit (n : S) := by
      have : IsUnit (n : ℚ) := (Nat.cast_ne_zero.2 hn).isUnit
      simpa using this.map (algebraMap ℚ S)
    exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 h2)
  have hf : Module.Finite ℚ S := finite_of_finite_spec ℚ S
  have hi : Function.Injective (algebraMap B S) := by
    refine IsLocalization.injective S (M := M) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by simpa using nonZeroDivisors.ne_zero hz)
  exact isAlgebraic_of_injective _ hi

theorem finite_primes_domain (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (h : {Q : PrimeSpectrum B | ∀ n : ℕ, n ≠ 0 → (n : B) ∉ Q.asIdeal}.Finite) (l : ℕ) (hl : l ≠ 0) :
    {Q : PrimeSpectrum B | (l : B) ∈ Q.asIdeal}.Finite := by
  have := isAlgebraic_of_finite B h
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  have hd := GlobalTheory.IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one B (RingHom.injective_int _)
  rw [trdeg_eq_zero] at hd
  have hd1 : Ring.KrullDimLE 1 B := by
    rw [Ring.krullDimLE_iff, hd]; simp
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B (Ideal.span {(l : B)})
  refine (hfin.preimage (f := PrimeSpectrum.asIdeal) fun _ _ _ _ e => PrimeSpectrum.ext e).subset ?_
  intro P hP
  refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hP⟩, fun Q hQ hQP => ?_⟩
  have hQ0 : Q ≠ ⊥ := fun e => by
    have := (Ideal.span_singleton_le_iff_mem _).1 hQ.2
    rw [e] at this
    exact Nat.cast_ne_zero.2 hl this
  have hm : Q.IsMaximal := Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hd1 Q hQ0 hQ.1
  exact (hm.eq_of_le P.isPrime.ne_top hQP).ge

theorem finite_primes (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] (P : PrimeSpectrum A)
    (hP : ∀ n : ℕ, n ≠ 0 → (n : A) ∉ P.asIdeal)
    (h : {Q : PrimeSpectrum A | P ≤ Q ∧ ∀ n : ℕ, n ≠ 0 → (n : A) ∉ Q.asIdeal}.Finite) (l : ℕ) (hl : l ≠ 0) :
    {Q : PrimeSpectrum A | P ≤ Q ∧ (l : A) ∈ Q.asIdeal}.Finite := by
  let π := Ideal.Quotient.mk P.asIdeal
  have hs : Function.Surjective π := Ideal.Quotient.mk_surjective
  have : CharZero (A ⧸ P.asIdeal) := @CharP.charP_to_charZero _ _ (by
    refine ⟨fun n => ⟨fun hn => ?_, fun hn => by rw [zero_dvd_iff.1 hn, Nat.cast_zero]⟩⟩
    by_contra hne
    refine hP n (fun e => hne (e ▸ dvd_rfl)) ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hn)
  have := finiteType_of_surjective π hs
  have hinj := PrimeSpectrum.comap_injective_of_surjective π hs
  have hr : Set.range (PrimeSpectrum.comap π) = PrimeSpectrum.zeroLocus (P.asIdeal : Set A) := by
    rw [range_comap_of_surjective _ π hs, Ideal.mk_ker]
  have hf := finite_primes_domain (A ⧸ P.asIdeal) ((h.preimage hinj.injOn).subset fun Q hQ => ⟨by
    have : PrimeSpectrum.comap π Q ∈ PrimeSpectrum.zeroLocus (P.asIdeal : Set A) := hr ▸ ⟨Q, rfl⟩
    exact this, fun n hn h1 => hQ n hn (by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at h1; exact h1)⟩) l hl
  refine (hf.image (PrimeSpectrum.comap π)).subset ?_
  rintro Q ⟨h1, h2⟩
  have : Q ∈ Set.range (PrimeSpectrum.comap π) := hr ▸ h1
  obtain ⟨Q, rfl⟩ := this
  refine ⟨Q, ?_, rfl⟩
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at h2
  exact h2

theorem natCast_eq_zero_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (Q : PrimeSpectrum Γ(X, U)) (n : ℕ) :
    (n : X.residueField (hU.fromSpec Q)) = 0 ↔ (n : Γ(X, U)) ∈ Q.asIdeal := by
  have hx : hU.fromSpec Q ∈ U := by
    have : hU.fromSpec Q ∈ Set.range hU.fromSpec := ⟨Q, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hb : hU.fromSpec Q ∈ X.basicOpen (n : Γ(X, U)) ↔ (n : Γ(X, U)) ∉ Q.asIdeal :=
    SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen _) Q
  rw [← map_natCast (X.evaluation U _ hx).hom n]
  exact (X.evaluation_eq_zero_iff_notMem_basicOpen _ hx _).trans (hb.not.trans not_not)

theorem finite_closure_inter_fib : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ W : Set X, IsClosed W → (W ∩ fib X 0).Finite → ∀ ℓ : ℕ, (closure (W ∩ fib X 0) ∩ fib X ℓ).Finite := by
  intro k _ X _ p D hX W hW hfin l
  have hsub : closure (W ∩ fib X 0) ⊆ W := closure_minimal Set.inter_subset_left hW
  rcases eq_or_ne l 0 with rfl | hl
  · exact hfin.subset (Set.inter_subset_inter_left _ hsub)
  have := hX.isNoetherian
  have hft : LocallyOfFiniteType (p ≫ spMap (Int.castRingHom k)) := by
    obtain ⟨N, j, _, hj⟩ := hX.isProjOver
    have := isProper_str k N
    have : IsProper p := hj ▸ inferInstance
    have : IsFinite (spMap (Int.castRingHom k)) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
    infer_instance
  have key (U : X.Opens) (hU : IsAffineOpen U) : (closure (W ∩ fib X 0) ∩ fib X l ∩ U).Finite := by
    have : Algebra.FiniteType ℤ Γ(X, U) := by
      set t := p ≫ spMap (Int.castRingHom k)
      have e : (t.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℤ)).inv.hom =
        algebraMap ℤ Γ(X, U) := RingHom.ext_int _ _
      rw [← RingHom.finiteType_algebraMap, ← e, RingHom.finiteType_respectsIso.cancel_left_isIso]
      exact HasRingHomProperty.appLE @LocallyOfFiniteType t hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    have hemb := hU.fromSpec.isOpenEmbedding
    have h0 (Q : PrimeSpectrum Γ(X, U)) :
        hU.fromSpec Q ∈ fib X 0 ↔ ∀ n : ℕ, n ≠ 0 → (n : Γ(X, U)) ∉ Q.asIdeal := by
      change ringChar _ = 0 ↔ _
      simp only [← natCast_eq_zero_iff hU, ringChar.spec]
      refine ⟨fun h n hn => by rw [h, zero_dvd_iff]; exact hn, fun h => ?_⟩
      by_contra hne
      exact h _ hne dvd_rfl
    have hS : (hU.fromSpec ⁻¹' (W ∩ fib X 0)).Finite := hfin.preimage hemb.injective.injOn
    have hT := hS.biUnion (t := fun P : PrimeSpectrum Γ(X, U) =>
        {Q : PrimeSpectrum Γ(X, U) | P ≤ Q ∧ (l : Γ(X, U)) ∈ Q.asIdeal}) fun P hP =>
      finite_primes _ P ((h0 P).1 hP.2) (hS.subset fun Q hQ => ⟨hW.stableUnderSpecialization
        (((PrimeSpectrum.le_iff_specializes P Q).1 hQ.1).map hemb.continuous) hP.1, (h0 Q).2 hQ.2⟩) l hl
    refine (hT.image hU.fromSpec).subset ?_
    rintro y ⟨⟨hy, hyl⟩, hyU⟩
    have : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hyU
    obtain ⟨Q, rfl⟩ := this
    refine ⟨Q, ?_, rfl⟩
    have h1 : Q ∈ closure (hU.fromSpec ⁻¹' (W ∩ fib X 0)) := by
      rw [← hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous]; exact hy
    rw [← Set.biUnion_of_singleton (hU.fromSpec ⁻¹' (W ∩ fib X 0)), hS.closure_biUnion] at h1
    obtain ⟨P, hP, h1⟩ := Set.mem_iUnion₂.1 h1
    refine Set.mem_iUnion₂.2 ⟨P, hP, (PrimeSpectrum.le_iff_specializes P Q).2 (specializes_iff_mem_closure.2 h1), ?_⟩
    exact (natCast_eq_zero_iff hU Q l).1 ((ringChar.spec _ _).2 (dvd_of_eq hyl))
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.2)
    fun x _ => by
      obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top x)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩
  refine (s.finite_toSet.biUnion fun U _ => key U.1 U.2).subset fun y hy => ?_
  obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  exact Set.mem_iUnion₂.2 ⟨U, hU, hy, hyU⟩

end GlobalTheory.GenFibClosure
