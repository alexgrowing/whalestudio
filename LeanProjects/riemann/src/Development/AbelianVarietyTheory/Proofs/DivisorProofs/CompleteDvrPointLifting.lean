import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationRingPrimeDominanceStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.FactorDepth

theorem trdegGe_map_of_ringHom {k k' : Type} [Field k] [Field k'] (φ : k →+* k') {n : ℕ} (h : TrdegGe k n) :
    TrdegGe k' n := by
  obtain ⟨t, ht⟩ := h
  have hm : (⊥ : Subfield k).map φ = ⊥ := Subfield.map_bot φ
  let f : (⊥ : Subfield k) →+* (⊥ : Subfield k') :=
    (φ.comp (⊥ : Subfield k).subtype).codRestrict _ fun x => hm ▸ ⟨x.1, x.2, rfl⟩
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx, e⟩ : y.1 ∈ (⊥ : Subfield k).map φ := hm.symm ▸ y.2
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  exact ⟨φ ∘ t, ht.ringHom_of_comp_eq f φ hf φ.injective (by ext; rfl)⟩

theorem exists_specializes_over_closedPoint (O : Type) [CommRing O] [IsLocalRing O] (X : Scheme.{0})
    (s : X ⟶ Sp O) [IsProper s] (x : X) : ∃ ξ : X, x ⤳ ξ ∧ s ξ = closedPoint O := by
  have h1 : s x ⤳ closedPoint O := IsLocalRing.specializes_closedPoint _
  obtain ⟨ξ, h2, h3⟩ := s.isClosedMap.specializingMap h1
  exact ⟨ξ, h2, h3⟩

theorem exists_cdvr_centred_trdegGe (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (X : Scheme.{0}) (s : X ⟶ Sp O) [IsProper s] (K : Type) [Field K] (g : Sp K ⟶ X) [IsPreimmersion g]
    (a : O →+* K) (ha : Function.Injective a) (hg : g ≫ s = spMap a) (d : ℕ)
    (hd : letI := a.toAlgebra; (d : Cardinal) ≤ Algebra.trdeg O K) :
    ∃ (T : CDVR) (yt : Sp T.V ⟶ X) (ψ : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b ∧ yt ≫ s = spMap b ∧
      spMap (algebraMap T.V T.Fr) ≫ yt = spMap ψ ≫ g ∧ TrdegGe (X.residueField (yt (closedPoint T.V))) d := by
  obtain ⟨ξ, hξ, hs⟩ := exists_specializes_over_closedPoint O X s (g (closedPoint K))
  obtain ⟨A, _, j, _, p, rfl⟩ : ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X) (_ : IsOpenImmersion j)
      (p : PrimeSpectrum A), j p = ξ := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ξ) isOpen_univ
    have hU : IsAffineOpen U := hU
    have : ξ ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
    obtain ⟨p, hp⟩ := this
    exact ⟨Γ(X, U), inferInstance, hU.fromSpec, inferInstanceAs (IsOpenImmersion hU.fromSpec), p, hp⟩
  have hr : Set.range g ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (closedPoint K)]
    exact hξ.mem_open j.isOpenEmbedding.isOpen_range ⟨p, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : A →+* K, spMap φ ≫ j = g :=
    ⟨(Spec.preimage (IsOpenImmersion.lift j g hr)).hom, by
      rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  obtain ⟨α, hα⟩ : ∃ α : O →+* A, spMap α = j ≫ s :=
    ⟨(Spec.preimage (j ≫ s)).hom, by rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have hcomp : φ.comp α = a := by
    have : spMap (φ.comp α) = spMap a := by
      rw [← hg, ← hφ, Category.assoc, ← hα, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  let _ := a.toAlgebra
  let _ := φ.toAlgebra
  let _ := α.toAlgebra
  have : IsScalarTower O A K := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hft : Algebra.FiniteType O A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := CommRingCat.ofHom α)).mp
      (show LocallyOfFiniteType (spMap α) from hα ▸ inferInstance)
  have hpre : IsPreimmersion (spMap φ) := by
    have : IsPreimmersion (spMap φ ≫ j) := hφ ▸ inferInstance
    exact IsPreimmersion.of_comp _ j
  have hst : φ.SurjectiveOnStalks := ((IsPreimmersion.SpecMap_iff (CommRingCat.ofHom φ)).1 hpre).2
  have hfr : ∀ x : K, ∃ u v : A, algebraMap A K v ≠ 0 ∧ x * algebraMap A K v = algebraMap A K u := fun x => by
    obtain ⟨u, v, c, hc, hv, e⟩ := RingHom.surjectiveOnStalks_iff_forall_ideal.1 hst ⊥ bot_ne_top x
    refine ⟨u, v, hv, mul_left_cancel₀ (show c ≠ 0 from hc) ?_⟩
    rw [mul_comm x, ← mul_assoc]
    exact e
  have hker : RingHom.ker (algebraMap A K) ≤ p.asIdeal := by
    have h1 : j (spMap φ (closedPoint K)) ⤳ j p := by
      rw [← hφ] at hξ
      exact hξ
    have h2 := (PrimeSpectrum.le_iff_specializes (PrimeSpectrum.comap φ (closedPoint K)) p).mpr
      (j.isOpenEmbedding.isInducing.specializes_iff.mp h1)
    exact fun x hx => h2 (show φ x ∈ (closedPoint K).asIdeal from (show φ x = 0 from hx) ▸ Ideal.zero_mem _)
  have hmax : (maximalIdeal O).map (algebraMap O A) ≤ p.asIdeal := by
    have h1 : (j ≫ s) p = closedPoint O := hs
    rw [← hα] at h1
    exact Ideal.map_le_iff_le_comap.2 (congrArg PrimeSpectrum.asIdeal h1).ge
  obtain ⟨T, f, ψ, e, hl, ht⟩ := GlobalTheory.T.valuation_ring_prime_dominance O A K ha hfr p.asIdeal p.isPrime hker hmax d hd
  refine ⟨T, spMap f ≫ j, ψ, f.comp α, hl, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hα, spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  · rw [← hφ, ← Category.assoc, ← Category.assoc, spMap, spMap, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
  · let q : Sp A := PrimeSpectrum.comap f (closedPoint T.V)
    exact trdegGe_map_of_ringHom (k := q.asIdeal.ResidueField) (k' := X.residueField (j q))
      ((Scheme.Spec.residueFieldIso (.of A) q).inv ≫ inv (j.residueFieldMap q)).hom ht

end GlobalTheory.FactorDepth
