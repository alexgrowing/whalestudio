import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealAssignment
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

private theorem exists_affineOpens_mem (X : Scheme.{u}) (x : ↥X) :
    ∃ U : X.affineOpens, x ∈ U.1.1 := by
  have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U, hU⟩

theorem maximalIdeal_stalk_ne_bot_of_specializes
    (X : Scheme.{u}) (x y : ↥X) (h : y ⤳ x) (hne : y ≠ x) :
    IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ≠ ⊥ := by
  intro hbot
  obtain ⟨U, hxU0⟩ := exists_affineOpens_mem X x
  have hxU : x ∈ U.1 := hxU0
  have hU : IsAffineOpen U.1 := U.2
  have hmem : x ∈ closure ({y} : Set ↥X) := specializes_iff_mem_closure.mp h
  have hyU : y ∈ U.1 := by
    have hopen : IsOpen ((U.1 : Set ↥X)) := U.1.2
    obtain ⟨z, hzU, hzy⟩ := (mem_closure_iff.mp hmem) ((U.1 : Set ↥X)) hopen hxU
    rw [Set.mem_singleton_iff] at hzy
    have hy2 : y ∈ ((U.1 : Set ↥X)) := by rw [← hzy]; exact hzU
    exact hy2
  have hind : Topology.IsInducing (⇑(hU.fromSpec)) :=
    (hU.fromSpec).isOpenEmbedding.toIsEmbedding.toIsInducing
  have e1 : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨x, hxU⟩) = x :=
    hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have e2 : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨y, hyU⟩) = y :=
    hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  have hspec : hU.primeIdealOf ⟨y, hyU⟩ ⤳ hU.primeIdealOf ⟨x, hxU⟩ := by
    apply hind.specializes_iff.mp
    rw [e1, e2]
    exact h
  have hqp : (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    have h2 := specializes_iff_mem_closure.mp hspec
    rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus] at h2
    exact fun z hz => h2 hz
  have hne' : (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ≠ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    intro heq
    apply hne
    have hpe : hU.primeIdealOf ⟨y, hyU⟩ = hU.primeIdealOf ⟨x, hxU⟩ := PrimeSpectrum.ext heq
    exact e2.symm.trans (by rw [hpe]; exact e1)
  obtain ⟨a, hap, haq⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hqp hne')
  let _ : Algebra Γ(X, U.1) ↑(X.presheaf.stalk x) := (X.presheaf.germ U.1 x hxU).hom.toAlgebra
  have hloc : IsLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      ↑(X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have hmax : Ideal.map (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x))
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      = IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal ..
  have hmapmem : (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) a
      ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
    rw [← hmax]
    exact Ideal.mem_map_of_mem _ hap
  have h0 : (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) a = 0 := by
    rw [hbot] at hmapmem
    simpa using hmapmem
  have h1 : (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) a
      = (algebraMap Γ(X, U.1) ↑(X.presheaf.stalk x)) 0 := by
    rw [h0, map_zero]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ↑(X.presheaf.stalk x)).mp h1
  have hca : (c : Γ(X, U.1)) * a = 0 := by
    rw [mul_zero] at hc
    exact hc
  have hcp : (c : Γ(X, U.1)) ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := c.2
  have hcq : (c : Γ(X, U.1)) ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := fun hc0 => hcp (hqp hc0)
  have hmem0 : (c : Γ(X, U.1)) * a ∈ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    rw [hca]
    exact Submodule.zero_mem _
  rcases (hU.primeIdealOf ⟨y, hyU⟩).isPrime.mem_or_mem hmem0 with hcc | haa
  · exact hcq hcc
  · exact haq haa

theorem orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents
    (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Closeds ↥X) (x : ↥X)
    (hx : IsGenericPoint x (S : Set ↥X))
    (hS : (S : Set ↥X) ∉ irreducibleComponents ↥X) :
    FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal S) x = 1 := by
  have hx' : closure ({x} : Set ↥X) = (S : Set ↥X) := hx
  have hSirr : IsIrreducible (S : Set ↥X) := by
    rw [← hx']
    exact isIrreducible_singleton.closure
  have hxS : x ∈ (S : Set ↥X) := by
    rw [← hx']
    exact subset_closure (Set.mem_singleton x)
  have hMax : Maximal (fun s : Set ↥X => IsIrreducible s ∧ s ⊆ (S : Set ↥X)) (S : Set ↥X) := by
    constructor
    · exact ⟨hSirr, subset_rfl⟩
    · intro b hb _
      exact hb.2
  obtain ⟨t, htpre, hSt, hmaxt⟩ := exists_preirreducible (S : Set ↥X) hSirr.2
  have htirr : IsIrreducible t := ⟨⟨x, hSt hxS⟩, htpre⟩
  have htclosed : IsClosed t := by
    have h1 : closure t = t := hmaxt (closure t) htpre.closure subset_closure
    rw [← h1]
    exact isClosed_closure
  have htmem : t ∈ irreducibleComponents ↥X := by
    constructor
    · exact htirr
    · intro u hu htu
      exact (hmaxt u hu.2 htu).le
  have hSnet : (S : Set ↥X) ≠ t := by
    intro hEq
    exact hS (hEq ▸ htmem)
  obtain ⟨y, hy⟩ := QuasiSober.sober htirr htclosed
  have hy' : closure ({y} : Set ↥X) = t := hy
  have hyx : y ⤳ x := by
    rw [specializes_iff_mem_closure, hy']
    exact hSt hxS
  have hyne : y ≠ x := by
    intro hEq
    apply hSnet
    rw [← hx', ← hEq]
    exact hy'
  have hbot : IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ≠ ⊥ :=
    maximalIdeal_stalk_ne_bot_of_specializes X x y hyx hyne
  exact _root_.FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one S x (S : Set ↥X) hMax hx hbot

theorem isLocallyNoetherian_subscheme_of_isSmoothDivisor
    (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    (U : W.Opens) (D : (U.toScheme).IdealSheafData)
    (hD : IsSmoothDivisor (U.ι ≫ p) D) :
    IsLocallyNoetherian D.subscheme := by
  obtain ⟨_, hsm⟩ := hD
  have : AlgebraicGeometry.Smooth (D.subschemeι ≫ U.ι ≫ p) := hsm
  have : LocallyOfFiniteType (D.subschemeι ≫ U.ι ≫ p) := inferInstance
  have : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ U.ι ≫ p)

theorem vanishingOrderOneOnSmoothDivisor : VanishingOrderOneOnSmoothDivisor.{u} := by
  intro k hk W p U D hD T y hy hT
  have : IsLocallyNoetherian D.subscheme :=
    isLocallyNoetherian_subscheme_of_isSmoothDivisor k W p U D hD
  rw [vanishingIdealAssignment_apply]
  exact orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents D.subscheme T y hy hT

end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
