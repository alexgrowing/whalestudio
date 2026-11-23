import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem one_mem_of_mul_mem_of_dual_derivations {k : Type u} [Field k] {B : Type u} [CommRing B]
    [Algebra k B] (I : Ideal B) (y₁ y₂ f a b : B) (δ₁ δ₂ : Derivation k B B)
    (hf : f ∈ I) (hy₁ : y₁ = a * f) (hy₂ : y₂ = b * f)
    (e11 : δ₁ y₁ = 1) (e12 : δ₁ y₂ = 0) (e21 : δ₂ y₁ = 0) (e22 : δ₂ y₂ = 1) :
    (1 : B) ∈ I := by
  have hπf : (Ideal.Quotient.mk I) f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have key : ∀ (δ : Derivation k B B) (c : B),
      (Ideal.Quotient.mk I) (δ (c * f)) =
        (Ideal.Quotient.mk I) c * (Ideal.Quotient.mk I) (δ f) := by
    intro δ c
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hπf,
      zero_mul, add_zero]
  have k11 : (Ideal.Quotient.mk I) a * (Ideal.Quotient.mk I) (δ₁ f) = 1 := by
    rw [← key δ₁ a, ← hy₁, e11, map_one]
  have k12 : (Ideal.Quotient.mk I) a * (Ideal.Quotient.mk I) (δ₂ f) = 0 := by
    rw [← key δ₂ a, ← hy₁, e21, map_zero]
  have k21 : (Ideal.Quotient.mk I) b * (Ideal.Quotient.mk I) (δ₁ f) = 0 := by
    rw [← key δ₁ b, ← hy₂, e12, map_zero]
  have k22 : (Ideal.Quotient.mk I) b * (Ideal.Quotient.mk I) (δ₂ f) = 1 := by
    rw [← key δ₂ b, ← hy₂, e22, map_one]
  have hone : (1 : B ⧸ I) = 0 := by
    calc (1 : B ⧸ I)
        = ((Ideal.Quotient.mk I) a * (Ideal.Quotient.mk I) (δ₁ f)) *
            ((Ideal.Quotient.mk I) b * (Ideal.Quotient.mk I) (δ₂ f)) := by
          rw [k11, k22, one_mul]
      _ = ((Ideal.Quotient.mk I) a * (Ideal.Quotient.mk I) (δ₂ f)) *
            ((Ideal.Quotient.mk I) b * (Ideal.Quotient.mk I) (δ₁ f)) := by ring
      _ = 0 := by rw [k12, k21, mul_zero]
  refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
  rw [map_one]
  exact hone

private theorem one_mem_of_coord_mem_span_singleton_of_ne {k : Type u} [Field k] {m : ℕ} {B : Type u} [CommRing B]
    [Algebra (MvPolynomial (ULift.{u} (Fin m)) k) B] [Algebra k B]
    [IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) B]
    [Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) B]
    (I : Ideal B) (h : B) (hI : I = Ideal.span ({h} : Set B))
    (j₁ j₂ : Fin m) (hne : j₁ ≠ j₂)
    (hm1 : EtaleCoordinates.coord k (ULift.{u} (Fin m)) B (ULift.up j₁) ∈ I)
    (hm2 : EtaleCoordinates.coord k (ULift.{u} (Fin m)) B (ULift.up j₂) ∈ I) :
    (1 : B) ∈ I := by
  have hh : h ∈ I := by
    rw [hI]; exact Ideal.mem_span_singleton_self h
  rw [hI] at hm1 hm2
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hm1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hm2
  have hne' : (ULift.up j₁ : ULift.{u} (Fin m)) ≠ ULift.up j₂ := fun hc =>
    hne (congrArg ULift.down hc)
  exact one_mem_of_mul_mem_of_dual_derivations I _ _ h a b
    (EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) B (ULift.up j₁))
    (EtaleCoordinates.partialDeriv k (ULift.{u} (Fin m)) B (ULift.up j₂))
    hh ha.symm hb.symm
    (EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin m)) B (ULift.up j₁))
    (EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin m)) B _ _ hne')
    (EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin m)) B _ _ hne'.symm)
    (EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin m)) B (ULift.up j₂))

private theorem ideal_eq_bot_of_opens_eq {X : Scheme.{u}} (D : X.IdealSheafData)
    (W₁ W₂ : X.affineOpens) (hW : (W₁ : X.Opens) = (W₂ : X.Opens))
    (h : D.ideal W₁ = ⊥) : D.ideal W₂ = ⊥ := by
  obtain rfl : W₁ = W₂ := Subtype.ext hW
  exact h

private theorem exists_ideal_eq_span_singleton_of_opens_eq {X : Scheme.{u}} (D : X.IdealSheafData)
    (W₁ W₂ : X.affineOpens) (hW : (W₁ : X.Opens) = (W₂ : X.Opens))
    (h : ∃ f, D.ideal W₂ = Ideal.span ({f} : Set Γ(X, (W₂ : X.Opens)))) :
    ∃ f, D.ideal W₁ = Ideal.span ({f} : Set Γ(X, (W₁ : X.Opens))) := by
  obtain rfl : W₁ = W₂ := Subtype.ext hW
  exact h

theorem exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton {X : Scheme.{u}} {k : Type u} [Field k]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (D : X.IdealSheafData) (hD : IsSmoothDivisor p D) (x : X) (hx : x ∈ D.support) :
    ∃ (U : X.Opens) (m : ℕ) (c : EtaleChart p U m) (j : Fin m),
      x ∈ U ∧ restrictIdeal D U = c.coordIdeal ({j} : Finset (Fin m)) := by
  rw [isSmoothDivisor_iff] at hD
  obtain ⟨hcart, hsm⟩ := hD
  have : AlgebraicGeometry.Smooth (D.subschemeι ≫ p) := hsm
  obtain ⟨U, m, c, S, hxU, hU, hDU⟩ := exists_chart_restrictIdeal_eq_coordIdeal p D x hx
  have hideal : D.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) :=
    c.ideal_eq_span_coord hU D S hDU
  obtain ⟨V, f, hxV, hfnzd, hVf⟩ := hcart x
  obtain ⟨g, g', hgg', hxg⟩ := exists_basicOpen_le_affine_inter hU V.2 x ⟨hxU, hxV⟩
  have hWaff : IsAffineOpen (X.basicOpen g) := hU.basicOpen g
  have hresU : Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
      (D.ideal ⟨U, hU⟩) = D.ideal ⟨X.basicOpen g, hWaff⟩ :=
    D.map_ideal_basicOpen ⟨U, hU⟩ g
  have hspan : D.ideal ⟨X.basicOpen g, hWaff⟩ =
      Ideal.span ((fun j : Fin m =>
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (c.coord j)) ''
          (S : Set (Fin m))) := by
    rw [← hresU, hideal, Ideal.map_span, ← Set.image_comp]
    rfl
  have hxg' : x ∈ X.basicOpen g' := hgg' ▸ hxg
  have hmap := D.map_ideal_basicOpen V g'
  rw [hVf, Ideal.map_span, Set.image_singleton] at hmap
  have hSne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with rfl | hne
    · exfalso
      have h0 : D.ideal ⟨X.basicOpen g, hWaff⟩ = ⊥ := by
        rw [hspan]; simp
      have h0' : D.ideal (X.affineBasicOpen g') = ⊥ :=
        ideal_eq_bot_of_opens_eq D ⟨X.basicOpen g, hWaff⟩ (X.affineBasicOpen g') hgg' h0
      have hfzero := Ideal.span_singleton_eq_bot.mp (hmap.trans h0')
      have instLoc' : IsLocalization.Away g' Γ(X, X.basicOpen g') :=
        V.2.isLocalization_basicOpen g'
      have hfa : algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen g') f = 0 := hfzero
      obtain ⟨cc, hcc⟩ :=
        (IsLocalization.eq_iff_exists (Submonoid.powers g')
          Γ(X, X.basicOpen g')).mp (show
            algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen g') f =
              algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen g') 0 by
            rw [hfa, map_zero])
      have hz : (cc : Γ(X, (V : X.Opens))) = 0 :=
        (mem_nonZeroDivisors_iff.mp hfnzd).2 _ (by rw [hcc, mul_zero])
      have hunit : IsUnit (algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen g')
          (cc : Γ(X, (V : X.Opens)))) :=
        IsLocalization.map_units Γ(X, X.basicOpen g') cc
      rw [hz, map_zero] at hunit
      have h01 : (0 : Γ(X, X.basicOpen g')) = 1 := isUnit_zero_iff.mp hunit
      have h10 : (0 : X.presheaf.stalk x) = 1 := by
        have hq := congrArg (X.presheaf.germ (X.basicOpen g') x hxg').hom h01
        rwa [map_zero, map_one] at hq
      exact zero_ne_one h10
    · exact hne
  have hcard1 : ∀ j₁ ∈ S, ∀ j₂ ∈ S, j₁ = j₂ := by
    intro j₁ hj₁ j₂ hj₂
    by_contra hne
    obtain ⟨h, hI⟩ : ∃ h, D.ideal ⟨X.basicOpen g, hWaff⟩ =
        Ideal.span ({h} : Set Γ(X, X.basicOpen g)) :=
      exists_ideal_eq_span_singleton_of_opens_eq D ⟨X.basicOpen g, hWaff⟩ (X.affineBasicOpen g') hgg'
        ⟨_, hmap.symm⟩
    let instPB : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) :=
      (((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom).comp c.coordRingHom).toAlgebra
    let instkB : Algebra k Γ(X, X.basicOpen g) :=
      ((((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom).comp c.coordRingHom).comp
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)).toAlgebra
    have instTower : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k)
        Γ(X, X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq fun _ => by
        rw [MvPolynomial.algebraMap_eq]
        rfl
    let instPA : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
    have instFE1 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
      c.algebra_formallyEtale hU
    have instScalarTower : IsScalarTower (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)
        Γ(X, X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have instLoc : IsLocalization.Away g Γ(X, X.basicOpen g) := hU.isLocalization_basicOpen g
    have instFE2 : Algebra.FormallyEtale Γ(X, U) Γ(X, X.basicOpen g) :=
      Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)
    have instFE3 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k)
        Γ(X, X.basicOpen g) :=
      Algebra.FormallyEtale.comp (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)
        Γ(X, X.basicOpen g)
    have hcoord : ∀ j : Fin m,
        EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, X.basicOpen g) (ULift.up j) =
          (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (c.coord j) := by
      intro j
      rw [EtaleCoordinates.coord_def]
      show (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
          (c.coordRingHom (MvPolynomial.X (ULift.up j))) = _
      rw [c.coordRingHom_X]
    have hm1 : EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, X.basicOpen g) (ULift.up j₁) ∈
        D.ideal ⟨X.basicOpen g, hWaff⟩ := by
      rw [hcoord, hspan]
      exact Ideal.subset_span ⟨j₁, hj₁, rfl⟩
    have hm2 : EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, X.basicOpen g) (ULift.up j₂) ∈
        D.ideal ⟨X.basicOpen g, hWaff⟩ := by
      rw [hcoord, hspan]
      exact Ideal.subset_span ⟨j₂, hj₂, rfl⟩
    have hone : (1 : Γ(X, X.basicOpen g)) ∈ D.ideal ⟨X.basicOpen g, hWaff⟩ :=
      one_mem_of_coord_mem_span_singleton_of_ne (D.ideal ⟨X.basicOpen g, hWaff⟩) h hI j₁ j₂ hne hm1 hm2
    have htop : D.ideal ⟨X.basicOpen g, hWaff⟩ = ⊤ := (Ideal.eq_top_iff_one _).mpr hone
    have hle := ideal_le_primeIdealOf D hWaff hxg hx
    rw [htop] at hle
    exact (hWaff.primeIdealOf ⟨x, hxg⟩).isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨j, hj⟩ :=
    Finset.card_eq_one.mp
      (le_antisymm (Finset.card_le_one.mpr hcard1) (Finset.card_pos.mpr hSne))
  exact ⟨U, m, c, j, hxU, by rw [hDU, hj]⟩

theorem inStrictNormalCrossingPosition_singleton_of_isSmoothDivisor {X : Scheme.{u}} {k : Type u} [Field k]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (D : X.IdealSheafData) (hD : IsSmoothDivisor p D) :
    InStrictNormalCrossingPosition p [D] := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, fun x => ?_⟩
  · intro D' hD'
    simp only [List.mem_singleton] at hD'
    subst hD'
    exact hD
  · by_cases hx : x ∈ D.support
    · obtain ⟨U, m, c, j, hxU, hDU⟩ :=
        exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p D hD x hx
      refine ⟨U, hxU, m, c, fun _ => some j, ?_, ?_, ?_⟩
      · intro i hi i' hi' t _ _
        simp only [List.length_singleton] at hi hi'
        omega
      · intro i hi hnone
        simp at hnone
      · intro i hi t ht
        have htj : t = j := (Option.some.inj ht).symm
        subst htj
        have hi0 : i = 0 := by
          simp only [List.length_singleton] at hi
          omega
        subst hi0
        simpa using hDU
    · obtain ⟨U, m, hxU, hUW, hUaff, hc⟩ :=
        exists_etaleChart_le p x
          (⟨((D.support : Set X))ᶜ, D.support.2.isOpen_compl⟩ : X.Opens) hx
      obtain ⟨c⟩ := hc
      have hbot : (D.comap U.ι).support = ⊥ := by
        rw [Scheme.IdealSheafData.support_comap]
        refine le_antisymm ?_ bot_le
        intro y hy
        have h1 : U.ι.base y ∈ D.support := hy
        have h2 : U.ι.base y ∈ (U : Set ↥X) := by
          rw [← Scheme.Opens.range_ι U]
          exact Set.mem_range_self y
        exact absurd h1 (hUW h2)
      have htop : restrictIdeal D U = ⊤ := by
        rw [restrictIdeal_eq_comap_ι]
        exact (Scheme.IdealSheafData.support_eq_bot_iff _).mp hbot
      refine ⟨U, hxU, m, c, fun _ => none, ?_, ?_, ?_⟩
      · intro i hi i' hi' t ht _
        simp at ht
      · intro i hi _
        have hi0 : i = 0 := by
          simp only [List.length_singleton] at hi
          omega
        subst hi0
        simpa using htop
      · intro i hi t ht
        simp at ht

end FunctorialResolution.EmbeddedResolution
