import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem isPreirreducible_of_isPreirreducible_image_val {α : Type u} [TopologicalSpace α] {s : Set α}
    {T : Set s} (h : IsPreirreducible (Subtype.val '' T)) : IsPreirreducible T := by
  intro u v hu hv hTu hTv
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨a, haT, hau⟩ := hTu
  obtain ⟨b, hbT, hbv⟩ := hTv
  obtain ⟨w, ⟨t, htT, rfl⟩, hwu, hwv⟩ :=
    h u' v' hu' hv' ⟨(a : α), ⟨a, haT, rfl⟩, hau⟩ ⟨(b : α), ⟨b, hbT, rfl⟩, hbv⟩
  exact ⟨t, htT, hwu, hwv⟩

private theorem exists_fromSpec_mem_and_primeIdealOf_eq {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (P : PrimeSpectrum Γ(X, V)) :
    ∃ hz : hV.fromSpec.base P ∈ V, hV.primeIdealOf ⟨hV.fromSpec.base P, hz⟩ = P := by
  have hz : hV.fromSpec.base P ∈ V := by
    have h : hV.fromSpec.base P ∈ Set.range hV.fromSpec.base := ⟨P, rfl⟩
    rwa [hV.range_fromSpec] at h
  refine ⟨hz, hV.fromSpec.isOpenEmbedding.injective ?_⟩
  rw [hV.fromSpec_primeIdealOf]

private theorem mem_support_iff_ideal_le_primeIdealOf {X : Scheme.{u}} (I : X.IdealSheafData)
    {V : X.Opens} (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) :
    x ∈ I.support ↔ I.ideal ⟨V, hV⟩ ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let _ : Algebra ↑Γ(X, V) ↑(X.presheaf.stalk x) :=
    RingHom.toAlgebra (X.presheaf.germ V x hx).hom
  have : IsLocalization.AtPrime ↑(X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hcomap : Ideal.comap (X.presheaf.germ V x hx).hom
      (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
      = (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    have h := IsLocalization.AtPrime.under_maximalIdeal (R := ↑Γ(X, V))
      (S := ↑(X.presheaf.stalk x)) (I := (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
    exact h
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I x ⟨V, hV⟩ hx,
    Ideal.map_le_iff_le_comap]
  exact iff_of_eq (congrArg (fun J => I.ideal ⟨V, hV⟩ ≤ J) hcomap)

private theorem vanishingIdeal_ideal_le_primeIdealOf {X : Scheme.{u}} (Z : Closeds ↥X)
    {V : X.Opens} (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) (hxZ : x ∈ (Z : Set ↥X)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨V, hV⟩
      ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have heq : (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨V, hV⟩
      = PrimeSpectrum.vanishingIdeal (hV.fromSpec.base ⁻¹' (Z : Set ↥X)) := rfl
  intro f hf
  rw [heq, PrimeSpectrum.mem_vanishingIdeal] at hf
  refine hf (hV.primeIdealOf ⟨x, hx⟩) ?_
  have : hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  show hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) ∈ (Z : Set ↥X)
  rw [this]
  exact hxZ

private theorem le_vanishingIdeal_of_subset_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (Z : Closeds ↥X) (h : (Z : Set ↥X) ⊆ (I.support : Set ↥X)) :
    I ≤ Scheme.IdealSheafData.vanishingIdeal Z := by
  have key : ∀ U : X.affineOpens,
      I.ideal U ≤ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U := by
    intro U f hf
    have heq : (Scheme.IdealSheafData.vanishingIdeal Z).ideal U
        = PrimeSpectrum.vanishingIdeal (U.2.fromSpec.base ⁻¹' (Z : Set ↥X)) := rfl
    rw [heq, PrimeSpectrum.mem_vanishingIdeal]
    intro P hP
    obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq U.2 P
    have hzs : U.2.fromSpec.base P ∈ I.support := h hP
    rw [mem_support_iff_ideal_le_primeIdealOf I U.2 hz, hzP] at hzs
    exact hzs hf
  exact key

structure IsIrreducibleComponentOfSupport {X : Scheme.{u}} (D : X.IdealSheafData) (C : Set X) : Prop where
  isIrreducible : IsIrreducible C
  maximal : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C
  subset_support : C ⊆ (D.support : Set X)

namespace IsIrreducibleComponentOfSupport

variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}

theorem isClosed (hC : IsIrreducibleComponentOfSupport D C) : IsClosed C :=
  isClosed_of_maximal_irreducible_subset_support D hC.isIrreducible hC.subset_support hC.maximal

theorem closure_genericPoint (hC : IsIrreducibleComponentOfSupport D C) :
    closure {hC.isIrreducible.genericPoint} = C :=
  hC.isIrreducible.isGenericPoint_genericPoint hC.isClosed

theorem genericPoint_mem (hC : IsIrreducibleComponentOfSupport D C) :
    hC.isIrreducible.genericPoint ∈ C := by
  have h : hC.isIrreducible.genericPoint ∈ closure {hC.isIrreducible.genericPoint} :=
    subset_closure (Set.mem_singleton _)
  rwa [hC.closure_genericPoint] at h

theorem genericPoint_specializes (hC : IsIrreducibleComponentOfSupport D C) {x : X} (hx : x ∈ C) :
    hC.isIrreducible.genericPoint ⤳ x := by
  refine specializes_iff_mem_closure.mpr ?_
  rw [hC.closure_genericPoint]
  exact hx

theorem genericPoint_mem_support (hC : IsIrreducibleComponentOfSupport D C) :
    hC.isIrreducible.genericPoint ∈ (D.support : Set X) :=
  hC.subset_support hC.genericPoint_mem

end IsIrreducibleComponentOfSupport

theorem exists_isIrreducibleComponentOfSupport {X : Scheme.{u}} (D : X.IdealSheafData) (x : X)
    (hx : x ∈ (D.support : Set X)) :
    ∃ C : Set X, IsIrreducibleComponentOfSupport D C ∧ x ∈ C := by
  have hchain : ∀ c ⊆ {t : Set X | IsIrreducible t ∧ t ⊆ (D.support : Set X)},
      IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {t : Set X | IsIrreducible t ∧ t ⊆ (D.support : Set X)}, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hch hne
    refine ⟨⋃₀ c, ⟨⟨?_, ?_⟩, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · obtain ⟨t, ht⟩ := hne
      obtain ⟨y, hy⟩ := (hcS ht).1.nonempty
      exact ⟨y, t, ht, hy⟩
    · rintro u v hu hv ⟨y, ⟨q, hq, hyq⟩, hyu⟩ ⟨z, ⟨r, hr, hzr⟩, hzv⟩
      rcases hch.total hq hr with h | h
      · obtain ⟨w, hw, hwuv⟩ := (hcS hr).1.2 u v hu hv ⟨y, h hyq, hyu⟩ ⟨z, hzr, hzv⟩
        exact ⟨w, ⟨r, hr, hw⟩, hwuv⟩
      · obtain ⟨w, hw, hwuv⟩ := (hcS hq).1.2 u v hu hv ⟨y, hyq, hyu⟩ ⟨z, h hzr, hzv⟩
        exact ⟨w, ⟨q, hq, hw⟩, hwuv⟩
    · exact Set.sUnion_subset fun t ht => (hcS ht).2
  obtain ⟨m, hxm, hm⟩ := zorn_subset_nonempty
    {t : Set X | IsIrreducible t ∧ t ⊆ (D.support : Set X)} hchain {x}
    ⟨isIrreducible_singleton, Set.singleton_subset_iff.mpr hx⟩
  exact ⟨m, ⟨hm.1.1, fun C' hC' hmC' hC'S =>
    Set.Subset.antisymm (hm.2 ⟨hC', hC'S⟩ hmC') hmC', hm.1.2⟩, hxm rfl⟩

theorem finite_isIrreducibleComponentOfSupport {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace ↥X]
    (D : X.IdealSheafData) :
    {C : Set X | IsIrreducibleComponentOfSupport D C}.Finite := by
  have hfin : (irreducibleComponents ↥((D.support : Set X))).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have himg : ∀ C ∈ {C : Set X | IsIrreducibleComponentOfSupport D C},
      (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))) ∈
        irreducibleComponents ↥((D.support : Set X)) := by
    intro C hC
    have hCsub : C ⊆ (D.support : Set X) := hC.subset_support
    have himgC :
        (Subtype.val '' (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))) : Set ↥X) = C :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hCsub)
    have hirr : IsIrreducible (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))) := by
      obtain ⟨y, hy⟩ := hC.isIrreducible.nonempty
      refine ⟨⟨⟨y, hCsub hy⟩, hy⟩, ?_⟩
      apply isPreirreducible_of_isPreirreducible_image_val
      rw [himgC]
      exact hC.isIrreducible.2
    refine ⟨hirr, ?_⟩
    intro T' hT' hle
    have h1 : IsIrreducible (Subtype.val '' T' : Set ↥X) :=
      hT'.image _ continuous_subtype_val.continuousOn
    have h2 : (Subtype.val '' T' : Set ↥X) ⊆ (D.support : Set X) := by
      rintro _ ⟨t, _, rfl⟩
      exact t.2
    have h3 : C ⊆ (Subtype.val '' T' : Set ↥X) := by
      rw [← himgC]
      exact Set.image_mono hle
    have h4 := hC.maximal _ h1 h3 h2
    intro t ht
    have hmem : (t : ↥X) ∈ C := by rw [← h4]; exact ⟨t, ht, rfl⟩
    exact hmem
  have hsub : (fun C : Set X => (Subtype.val ⁻¹' C : Set ↥((D.support : Set X)))) ''
      {C : Set X | IsIrreducibleComponentOfSupport D C} ⊆ irreducibleComponents ↥((D.support : Set X)) := by
    rintro _ ⟨C, hC, rfl⟩
    exact himg C hC
  have hinj : Set.InjOn (fun C : Set X => (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))))
      {C : Set X | IsIrreducibleComponentOfSupport D C} := by
    intro C1 h1 C2 h2 heq
    have e1 :
        (Subtype.val '' (Subtype.val ⁻¹' C1 : Set ↥((D.support : Set X))) : Set ↥X) = C1 :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact h1.subset_support)
    have e2 :
        (Subtype.val '' (Subtype.val ⁻¹' C2 : Set ↥((D.support : Set X))) : Set ↥X) = C2 :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact h2.subset_support)
    rw [← e1, ← e2]
    exact congrArg (Set.image Subtype.val) heq
  exact Set.Finite.of_finite_image (hfin.subset hsub) hinj

theorem stalkIdeal_ne_bot_of_nonzeroOnComponents {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : NonzeroOnComponents I) (x : X) : stalkIdeal I x ≠ ⊥ := by
  intro hbot
  rw [nonzeroOnComponents_iff] at hI
  refine hI (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x) ?_
  have hTirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hTcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  have hgen : closure {hTirr.genericPoint} = irreducibleComponent x :=
    hTirr.isGenericPoint_genericPoint hTcl
  have hspec : hTirr.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, hgen]
    exact mem_irreducibleComponent
  obtain ⟨V, hxV⟩ := Scheme.exists_affineOpens_mem x
  have hetaV : hTirr.genericPoint ∈ (V : X.Opens) := hspec.mem_open (V : X.Opens).isOpen hxV
  have hmapeq : CommRingCat.Hom.hom (X.presheaf.germ (V : X.Opens) hTirr.genericPoint hetaV)
      = (CommRingCat.Hom.hom (X.presheaf.stalkSpecializes hspec)).comp
        (CommRingCat.Hom.hom (X.presheaf.germ (V : X.Opens) x hxV)) := by
    rw [← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]
  have hetabot : stalkIdeal I hTirr.genericPoint = ⊥ := by
    rw [stalkIdeal_eq_map_germ I hTirr.genericPoint V hetaV, hmapeq, ← Ideal.map_map,
      ← stalkIdeal_eq_map_germ I x V hxV, hbot, Ideal.map_bot]
  have hbt : (⊥ : Ideal ↑(X.presheaf.stalk hTirr.genericPoint)) ≠ ⊤ := by
    intro h
    have h1 : (1 : ↑(X.presheaf.stalk hTirr.genericPoint)) ∈
        (⊥ : Ideal ↑(X.presheaf.stalk hTirr.genericPoint)) := by
      rw [h]; exact Submodule.mem_top
    rw [Ideal.mem_bot] at h1
    exact one_ne_zero h1
  have hmem : hTirr.genericPoint ∈ I.support :=
    (mem_support_iff_stalkIdeal_ne_top I _).mpr (by rw [hetabot]; exact hbt)
  calc irreducibleComponent x = closure {hTirr.genericPoint} := hgen.symm
    _ ⊆ closure ((I.support : Set ↥X)) :=
        closure_mono (Set.singleton_subset_iff.mpr hmem)
    _ = (I.support : Set ↥X) := I.support.isClosed.closure_eq

theorem orderAt_ne_top_of_nonzeroOnComponents {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I) (x : X) : orderAt I x ≠ ⊤ :=
  orderAt_ne_top_of_stalkIdeal_ne_bot I x (stalkIdeal_ne_bot_of_nonzeroOnComponents I hI x)

private theorem vanishingIdeal_ideal_eq_of_restrictIdeal_eq_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (D : X.IdealSheafData) {C : Set ↥X} (hCcl : IsClosed C)
    (hCsub : C ⊆ (D.support : Set ↥X))
    {W : X.Opens} (hW : IsAffineOpen W) {n : ℕ} (c : EtaleChart p W n) (S : Finset (Fin n))
    (hD : restrictIdeal D W = c.coordIdeal S)
    (hWC : ∀ y : ↥X, y ∈ W → y ∈ (D.support : Set ↥X) → y ∈ C) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨C, hCcl⟩ : Closeds ↥X)).ideal ⟨W, hW⟩
      = D.ideal ⟨W, hW⟩ := by
  refine le_antisymm ?_ ?_
  · have hrad : (D.ideal ⟨W, hW⟩).IsRadical :=
      isRadical_ideal_of_restrictIdeal_eq_coordIdeal p hW c D S hD
    have hJ : D.ideal ⟨W, hW⟩ = sInf {P : Ideal Γ(X, W) | D.ideal ⟨W, hW⟩ ≤ P ∧ P.IsPrime} := by
      rw [← Ideal.radical_eq_sInf, hrad.radical]
    rw [hJ]
    refine le_sInf ?_
    rintro P ⟨hPle, hPprime⟩
    obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq hW ⟨P, hPprime⟩
    have hzs : hW.fromSpec.base (⟨P, hPprime⟩ : PrimeSpectrum Γ(X, W)) ∈ D.support := by
      rw [mem_support_iff_ideal_le_primeIdealOf D hW hz, hzP]
      exact hPle
    have hzC : hW.fromSpec.base (⟨P, hPprime⟩ : PrimeSpectrum Γ(X, W)) ∈ C := hWC _ hz hzs
    have hfinal : (Scheme.IdealSheafData.vanishingIdeal (⟨C, hCcl⟩ : Closeds ↥X)).ideal ⟨W, hW⟩
        ≤ (hW.primeIdealOf ⟨_, hz⟩).asIdeal :=
      vanishingIdeal_ideal_le_primeIdealOf (⟨C, hCcl⟩ : Closeds ↥X) hW hz hzC
    rw [hzP] at hfinal
    exact hfinal
  · exact le_vanishingIdeal_of_subset_support D (⟨C, hCcl⟩ : Closeds ↥X) hCsub ⟨W, hW⟩

namespace IsIrreducibleComponentOfSupport

variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}

theorem orderAt_genericPoint_ne_top [IsLocallyNoetherian X] (hC : IsIrreducibleComponentOfSupport D C)
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I) :
    orderAt I hC.isIrreducible.genericPoint ≠ ⊤ :=
  orderAt_ne_top_of_nonzeroOnComponents I hI hC.isIrreducible.genericPoint

variable {k : Type u} [Field k]

theorem disjoint {C' : Set X} (hC : IsIrreducibleComponentOfSupport D C) (hC' : IsIrreducibleComponentOfSupport D C')
    (p : X ⟶ Spec (CommRingCat.of k))
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    (hne : C ≠ C') : Disjoint C C' := by
  rw [Set.disjoint_left]
  intro y hyC hyC'
  apply hne
  obtain ⟨V, hV, hyV, hetaV, n, c, j, hD, hspec, hetas, hmin⟩ :=
    exists_etaleChart_genericPoint_mem p D hloc hC.isIrreducible hC.subset_support hC.maximal y hyC
  have hspec' : hC'.isIrreducible.genericPoint ⤳ y := hC'.genericPoint_specializes hyC'
  have heta'V : hC'.isIrreducible.genericPoint ∈ V := hspec'.mem_open V.isOpen hyV
  have heta's : hC'.isIrreducible.genericPoint ∈ D.support := hC'.genericPoint_mem_support
  have hmin' : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩).asIdeal →
      P = (hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩).asIdeal := by
    intro P hP hcoord hle
    obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq hV ⟨P, hP⟩
    have hzs : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ∈ D.support := by
      rw [mem_support_iff_ideal_le_primeIdealOf D hV hz, hzP]
      rw [c.ideal_eq_span_coord hV D {j} hD, Ideal.span_le]
      rintro f ⟨i, hi, rfl⟩
      have hij : i = j := by simpa using hi
      subst hij
      exact hcoord
    have hsp : (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ⤳
        hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩ := by
      rw [specializes_iff_mem_closure, PrimeSpectrum.closure_singleton,
        PrimeSpectrum.mem_zeroLocus]
      exact hle
    have hspz : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ⤳
        hC'.isIrreducible.genericPoint := by
      have hmapped := hsp.map hV.fromSpec.base.hom.continuous
      rwa [hV.fromSpec_primeIdealOf] at hmapped
    have hclo : closure {hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))} = C' := by
      refine hC'.maximal _ isIrreducible_singleton.closure ?_ ?_
      · have h1 : {hC'.isIrreducible.genericPoint} ⊆
            closure {hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))} :=
          Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hspz)
        have h2 := closure_mono h1
        rw [closure_closure] at h2
        rw [← hC'.closure_genericPoint]
        exact h2
      · have h3 : closure {hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))}
            ⊆ closure ((D.support : Set ↥X)) :=
          closure_mono (Set.singleton_subset_iff.mpr hzs)
        rwa [D.support.isClosed.closure_eq] at h3
    have hzC' : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ∈ C' := by
      rw [← hclo]; exact subset_closure (Set.mem_singleton _)
    have hzeq : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))
        = hC'.isIrreducible.genericPoint :=
      (hspz.antisymm (hC'.genericPoint_specializes hzC')).eq
    have hfin : hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩
        = (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) := by
      rw [← hzP]
      congr 1
      exact Subtype.ext hzeq.symm
    exact (congrArg PrimeSpectrum.asIdeal hfin).symm
  have e1 := primeIdealOf_eq_comap_span_germ_coord p hV c j D hD y
    hC.isIrreducible.genericPoint hyV hetaV hspec hetas hmin
  have e2 := primeIdealOf_eq_comap_span_germ_coord p hV c j D hD y
    hC'.isIrreducible.genericPoint hyV heta'V hspec' heta's hmin'
  have hP : hV.primeIdealOf ⟨hC.isIrreducible.genericPoint, hetaV⟩
      = hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩ :=
    PrimeSpectrum.ext (e1.trans e2.symm)
  have hpts : hC.isIrreducible.genericPoint = hC'.isIrreducible.genericPoint := by
    have h := congrArg (fun q => hV.fromSpec.base q) hP
    simpa only [hV.fromSpec_primeIdealOf] using h
  rw [← hC.closure_genericPoint, ← hC'.closure_genericPoint, hpts]

theorem exists_affineOpen_etaleChart_coordIdeal [TopologicalSpace.NoetherianSpace ↥X] (hC : IsIrreducibleComponentOfSupport D C)
    (p : X ⟶ Spec (CommRingCat.of k))
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    (x : X) (hx : x ∈ C) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : x ∈ V) (n : ℕ) (c : EtaleChart p V n) (j : Fin n),
      restrictIdeal D V = c.coordIdeal {j} ∧
      (∀ y : X, y ∈ V → y ∈ (D.support : Set X) → y ∈ C) ∧
      (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).ideal ⟨V, hV⟩ = D.ideal ⟨V, hV⟩ ∧
      (∀ W : X.affineOpens, (↑W : X.Opens) ≤ V →
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).ideal W = D.ideal W) ∧
      (∀ y : X, y ∈ V →
        stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) y = stalkIdeal D y) := by
  obtain ⟨U, hxU, n, c₀, hU⟩ := hloc x
  have hxs : x ∈ (D.support : Set X) := hC.subset_support hx
  have hDUex : ∃ j : Fin n, restrictIdeal D U = c₀.coordIdeal {j} := by
    rcases hU with h | h
    · exact absurd hxs (notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U h x hxU)
    · exact h
  obtain ⟨j, hDU⟩ := hDUex
  obtain ⟨B, hBclosed, hxB, hBmem⟩ :
      ∃ B : Set ↥X, IsClosed B ∧ x ∉ B ∧
        ∀ y : ↥X, y ∈ (D.support : Set X) → y ∉ B → y ∈ C := by
    refine ⟨⋃ C'' ∈ {C'' : Set X | IsIrreducibleComponentOfSupport D C''} \ {C}, C'', ?_, ?_, ?_⟩
    · refine Set.Finite.isClosed_biUnion
        ((finite_isIrreducibleComponentOfSupport D).subset Set.sdiff_subset) ?_
      intro C'' hC''
      exact hC''.1.isClosed
    · intro hmem
      obtain ⟨C'', hC''mem, hxC''⟩ := Set.mem_iUnion₂.mp hmem
      exact Set.disjoint_left.mp
        (hC.disjoint hC''mem.1 p hloc (fun h => hC''mem.2 h.symm)) hx hxC''
    · intro y hys hyB
      obtain ⟨C'', hC''comp, hyC''⟩ := exists_isIrreducibleComponentOfSupport D y hys
      by_cases h : C'' = C
      · exact h ▸ hyC''
      · exact absurd (Set.mem_iUnion₂.mpr ⟨C'', ⟨hC''comp, h⟩, hyC''⟩) hyB
  have hxUB : x ∈ (⟨(U : Set ↥X) ∩ Bᶜ, U.isOpen.inter hBclosed.isOpen_compl⟩ : X.Opens) :=
    ⟨hxU, hxB⟩
  obtain ⟨V, hxV, hVle⟩ := Scheme.exists_affineOpens_mem_le hxUB
  have hVU : (V : X.Opens) ≤ U := fun y hy => (hVle hy).1
  have hVB : ∀ y : ↥X, y ∈ (V : X.Opens) → y ∉ B := fun y hy => (hVle hy).2
  have hDV : restrictIdeal D (V : X.Opens) = (c₀.restrict hVU).coordIdeal {j} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c₀ D {j} hDU
  have hVC : ∀ y : X, y ∈ (V : X.Opens) → y ∈ (D.support : Set X) → y ∈ C :=
    fun y hy hys => hBmem y hys (hVB y hy)
  have key : ∀ W : X.affineOpens, (W : X.Opens) ≤ (V : X.Opens) →
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hC.isClosed⟩ : Closeds ↥X)).ideal W = D.ideal W := by
    intro W hWV
    have hDW : restrictIdeal D (W : X.Opens)
        = ((c₀.restrict hVU).restrict hWV).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWV (c₀.restrict hVU) D {j} hDV
    exact vanishingIdeal_ideal_eq_of_restrictIdeal_eq_coordIdeal D hC.isClosed hC.subset_support W.2
      ((c₀.restrict hVU).restrict hWV) {j} hDW
      (fun y hy hys => hVC y (hWV hy) hys)
  refine ⟨(V : X.Opens), V.2, hxV, n, c₀.restrict hVU, j, hDV, hVC, key V le_rfl, ?_, ?_⟩
  · intro W hWV
    exact key W hWV
  · intro y hy
    rw [stalkIdeal_eq_map_germ
        (Scheme.IdealSheafData.vanishingIdeal (⟨C, hC.isClosed⟩ : Closeds ↥X)) y V hy,
      stalkIdeal_eq_map_germ D y V hy, key V le_rfl]

theorem stalkIdeal_vanishingIdeal_eq [TopologicalSpace.NoetherianSpace ↥X]
    (hC : IsIrreducibleComponentOfSupport D C) (p : X ⟶ Spec (CommRingCat.of k))
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    (x : X) (hx : x ∈ C) :
    stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) x = stalkIdeal D x := by
  obtain ⟨V, hV, hxV, n, c, j, -, -, -, -, hstalk⟩ := hC.exists_affineOpen_etaleChart_coordIdeal p hloc x hx
  exact hstalk x hxV

end IsIrreducibleComponentOfSupport

end FunctorialResolution.EmbeddedResolution
