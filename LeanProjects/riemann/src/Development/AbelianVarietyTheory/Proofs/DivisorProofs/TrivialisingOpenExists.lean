import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedOfChart

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat

namespace GlobalTheory.WeilIntegral

theorem exists_open_generic_le (p : ℕ) (O : Type) [CommRing O] (h : SpecialFibreNotInClosure p O)
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp O) [Smooth f] (x : X)
    (hx : (p : O) ∈ PrimeSpectrum.asIdeal (R := O) (f x)) (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ U : X.Opens, (∃ y : X, y ∈ U ∧ (p : O) ∈ PrimeSpectrum.asIdeal (R := O) (f y)) ∧
      ∀ y ∈ U, PrimeSpectrum.asIdeal (R := O) (f y) = ⊥ → y ∈ W := by
  obtain ⟨R, j, hj, ⟨x', rfl⟩, -⟩ := X.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) trivial
  have : Nonempty (Spec R) := ⟨x'⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 ‹_›
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ f)
  have hs : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
  have hs' : φ.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hs
  letI : Algebra O R := φ.hom.toAlgebra
  have : Algebra.Smooth O R := hs'
  have key : ∀ (z : Spec R) (c : O), c ∈ PrimeSpectrum.asIdeal (R := O) (f (j z)) ↔
      algebraMap O R c ∈ PrimeSpectrum.asIdeal (R := R) z := by
    intro z c
    rw [← Scheme.Hom.comp_apply, ← hφ]
    rfl
  obtain ⟨_, hz, z, rfl⟩ := nonempty_preirreducible_inter W.isOpen j.isOpenEmbedding.isOpen_range hW ⟨_, x', rfl⟩
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hza, ha⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
    (a := (z : PrimeSpectrum R)) (u := (j ⁻¹ᵁ W : Set (Spec R))) hz (j ⁻¹ᵁ W).isOpen
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hza (Ideal.zero_mem _)
  obtain ⟨q, g, c, hq, hg, hc, d, hd⟩ := h R a ha0 ⟨x', by simpa using (key x' p).1 hx⟩
  refine ⟨j ''ᵁ (PrimeSpectrum.basicOpen g), ⟨j q, ⟨q, hg, rfl⟩, (key q p).2 (by simpa using hq)⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ h0
  refine ha (a := y) fun hay => ?_
  have h1 : algebraMap O R c * g ∈ PrimeSpectrum.asIdeal (R := R) y := hd ▸ Ideal.mul_mem_right _ _ hay
  rcases (PrimeSpectrum.isPrime (R := R) y).mem_or_mem h1 with h2 | h2
  · exact hc (h0.le ((key y c).2 h2))
  · exact hy h2

theorem hasTrivialisingOpen_of_specialFibreNotInClosure (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [hp : Fact ¬IsUnit (p : O)]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) (h : SpecialFibreNotInClosure p O) :
    HasTrivialisingOpen P := by
  have hinj := P.integers.hom_inj
  have : IsDomain O := hinj.isDomain (algebraMap O C)
  have : IsFractionRing O C := P.integers.isFractionRing
  have := P.semi.smooth
  have := P.semi.geomConnected
  have : IsIntegral P.G.left := isIntegral_of_smooth_of_geometricallyConnected P.G.hom
  have := geometricallyIntegral_of_smooth P.G.hom
  have : IsPreimmersion (spMap (algebraMap O C)) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have : IsPreimmersion P.gen := MorphismProperty.of_isPullback P.gen_pull.1.flip ‹_›
  obtain ⟨m, hm, hpm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hp.out)
  obtain ⟨x, hx⟩ := P.G.hom.surjective (⟨m, hm.isPrime⟩ : PrimeSpectrum O)
  have := P.A.isAb.smooth
  have := P.A.isAb.geomConnected
  have : IsIntegral P.A.A.left := isIntegral_of_smooth_of_geometricallyConnected P.A.A.hom
  obtain ⟨a⟩ : Nonempty P.A.A.left := inferInstance
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (P.A.isLB.cover.ge (Set.mem_univ a))
  obtain ⟨W, hW, hWV⟩ := P.gen.isEmbedding.isInducing.isOpen_iff.1 (P.A.L.U i).isOpen
  obtain ⟨U, hU, hUW⟩ := exists_open_generic_le p O h P.G.hom x (by rw [hx]; exact hpm) ⟨W, hW⟩
    ⟨P.gen a, hWV.ge hi⟩
  refine ⟨U, hU, ChartRig.exists_gen_pull _ _ i P.A.isLB fun y _ => hWV.le (hUW _ y.2 ?_)⟩
  rw [← Scheme.Hom.comp_apply, P.gen_pull.1.w, Scheme.Hom.comp_apply]
  have e : ∀ z : PrimeSpectrum C, Ideal.comap (algebraMap O C) z.asIdeal = ⊥ := fun z => by
    rw [Ideal.eq_bot_of_prime z.asIdeal]
    exact Ideal.comap_bot_of_injective _ hinj
  exact e _

theorem hasTrivialisingOpen (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) (h : SpecialFibreNotInClosure p O) :
    HasTrivialisingOpen P :=
  hasTrivialisingOpen_of_specialFibreNotInClosure p C v O Λ P h

end GlobalTheory.WeilIntegral
