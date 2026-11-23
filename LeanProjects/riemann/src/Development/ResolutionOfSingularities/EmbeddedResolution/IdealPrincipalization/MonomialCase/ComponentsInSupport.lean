import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CoordinateSubspaceIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem mem_basicOpen_iff_notMem_asIdeal_primeIdealOf {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    {x : ↥X} (hx : x ∈ V) (f : Γ(X, V)) :
    x ∈ X.basicOpen f ↔ f ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 : hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 : (hV.primeIdealOf ⟨x, hx⟩) ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x ∈ X.basicOpen f := by
    show hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ _
    rw [h1]
  rw [← h2, hV.fromSpec_preimage_basicOpen]
  exact PrimeSpectrum.mem_basicOpen f _

private theorem mem_support_iff_ideal_le_asIdeal_primeIdealOf {X : Scheme.{u}} (I : X.IdealSheafData) {V : X.Opens}
    (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) :
    x ∈ I.support ↔ I.ideal ⟨V, hV⟩ ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hx, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h f hf
    by_contra hfP
    exact h f hf ((mem_basicOpen_iff_notMem_asIdeal_primeIdealOf hV hx f).mpr hfP)
  · intro h f hf hb
    exact (mem_basicOpen_iff_notMem_asIdeal_primeIdealOf hV hx f).mp hb (h (SetLike.mem_coe.mp hf))

private theorem mem_of_mul_pow_mem {R : Type u} [CommRing R] (I : Ideal R) (g : R)
    (hnzd : ∀ x : R, g * x ∈ I → x ∈ I) :
    ∀ (n : ℕ) (u : R), u * g ^ n ∈ I → u ∈ I := by
  intro n
  induction n with
  | zero =>
      intro u h
      simpa using h
  | succ n ih =>
      intro u h
      refine ih u (hnzd _ ?_)
      have e : g * (u * g ^ n) = u * g ^ (n + 1) := by ring
      rw [e]
      exact h

private theorem exists_isPrime_between_notMem_of_mul_mem {R : Type u} [CommRing R] (I : Ideal R) (g : R)
    (hnzd : ∀ x : R, g * x ∈ I → x ∈ I)
    (P : Ideal R) (hP : P.IsPrime) (hIP : I ≤ P) :
    ∃ Q : Ideal R, Q.IsPrime ∧ I ≤ Q ∧ Q ≤ P ∧ g ∉ Q := by
  classical
  have h1P : (1 : R) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  let M : Submonoid R :=
    { carrier := {x : R | ∃ (u : R) (n : ℕ), u ∉ P ∧ x = u * g ^ n}
      mul_mem' := by
        rintro x y ⟨u, n, hu, rfl⟩ ⟨v, l, hv, rfl⟩
        refine ⟨u * v, n + l, ?_, by ring⟩
        intro h
        rcases hP.mem_or_mem h with h' | h'
        · exact hu h'
        · exact hv h'
      one_mem' := ⟨1, 0, h1P, by ring⟩ }
  have hdisj : Disjoint (I : Set R) (M : Set R) := by
    rw [Set.disjoint_left]
    rintro x hxI ⟨u, n, hu, rfl⟩
    exact hu (hIP (mem_of_mul_pow_mem I g hnzd n u hxI))
  obtain ⟨Q, hQ, hIQ, hQdisj⟩ := Ideal.exists_le_prime_disjoint I M hdisj
  refine ⟨Q, hQ, hIQ, ?_, ?_⟩
  · intro x hx
    by_contra hxP
    exact Set.disjoint_left.mp hQdisj hx ⟨x, 0, hxP, by ring⟩
  · intro hg
    exact Set.disjoint_left.mp hQdisj hg ⟨1, 1, h1P, by ring⟩

private theorem mem_map_of_mul_mem_of_etale_of_isSMulRegular {P A : Type u} [CommRing P] [CommRing A]
    {f : P →+* A} (hf : f.Etale) (I : Ideal P) (w : P)
    (hw : ∀ a b : P ⧸ I,
      (Ideal.Quotient.mk I) w * a = (Ideal.Quotient.mk I) w * b → a = b)
    (x : A) (hx : f w * x ∈ Ideal.map f I) : x ∈ Ideal.map f I := by
  have hg : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).Etale :=
    etale_quotientMap hf I
  let _ : Algebra (P ⧸ I) (A ⧸ Ideal.map f I) :=
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).toAlgebra
  have : Algebra.Etale (P ⧸ I) (A ⧸ Ideal.map f I) := hg
  have : Module.Flat (P ⧸ I) (A ⧸ Ideal.map f I) := inferInstance
  have hy : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)
        ((Ideal.Quotient.mk I) w) * (Ideal.Quotient.mk (Ideal.map f I)) x = 0 := by
    rw [Ideal.quotientMap_mk, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hsm : ((Ideal.Quotient.mk I) w) • ((Ideal.Quotient.mk (Ideal.map f I)) x)
      = (0 : A ⧸ Ideal.map f I) := by
    show (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)
        ((Ideal.Quotient.mk I) w) * (Ideal.Quotient.mk (Ideal.map f I)) x = 0
    exact hy
  have hreg0 : IsSMulRegular (P ⧸ I) ((Ideal.Quotient.mk I) w) := fun a b h => hw a b h
  have hreg : IsSMulRegular (A ⧸ Ideal.map f I) ((Ideal.Quotient.mk I) w) := hreg0.of_flat
  have hzero : (Ideal.Quotient.mk (Ideal.map f I)) x = 0 := by
    refine hreg ?_
    show ((Ideal.Quotient.mk I) w) • ((Ideal.Quotient.mk (Ideal.map f I)) x)
      = ((Ideal.Quotient.mk I) w) • (0 : A ⧸ Ideal.map f I)
    rw [smul_zero]
    exact hsm
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

private theorem mem_mvPolynomialCoordIdeal_of_X_mul_mem (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) {s : Fin m} (hs : s ∉ S) (r : MvPolynomial (ULift.{u} (Fin m)) k)
    (h : MvPolynomial.X (ULift.up.{u} s) * r ∈ mvPolynomialCoordIdeal k m S) :
    r ∈ mvPolynomialCoordIdeal k m S := by
  classical
  obtain ⟨ψ, hψC, hψX⟩ :
      ∃ ψ : MvPolynomial (ULift.{u} (Fin m)) k →+* MvPolynomial (ULift.{u} (Fin m)) k,
        (∀ a : k, ψ (MvPolynomial.C a) = MvPolynomial.C a) ∧
        (∀ j : Fin m, ψ (MvPolynomial.X (ULift.up.{u} j))
          = if j ∈ S then 0 else MvPolynomial.X (ULift.up.{u} j)) := by
    refine ⟨MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i : ULift.{u} (Fin m) =>
        if i.down ∈ S then (0 : MvPolynomial (ULift.{u} (Fin m)) k)
        else MvPolynomial.X i), ?_, ?_⟩
    · intro a
      simp
    · intro j
      simp
  have hker : mvPolynomialCoordIdeal k m S ≤ RingHom.ker ψ := by
    rw [mvPolynomialCoordIdeal_eq_span, Ideal.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hz : ψ (MvPolynomial.X (ULift.up.{u} j)) = 0 := by
      rw [hψX j]
      exact if_pos (Finset.mem_coe.mp hj)
    exact SetLike.mem_coe.mpr (RingHom.mem_ker.mpr hz)
  have key : (Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S)).comp ψ
      = Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, hψC]
    · intro i
      obtain ⟨j⟩ := i
      rw [RingHom.comp_apply, hψX j]
      by_cases hi : j ∈ S
      · rw [if_pos hi, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr (X_mem_mvPolynomialCoordIdeal k m S hi)).symm
      · rw [if_neg hi]
  have h0 : ψ (MvPolynomial.X (ULift.up.{u} s) * r) = 0 :=
    RingHom.mem_ker.mp (hker h)
  rw [map_mul, hψX s, if_neg hs] at h0
  have hXne : (MvPolynomial.X (ULift.up.{u} s) : MvPolynomial (ULift.{u} (Fin m)) k) ≠ 0 :=
    MvPolynomial.X_ne_zero _
  have hψr : ψ r = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hXne
    · exact h1
  have hfin := DFunLike.congr_fun key r
  rw [RingHom.comp_apply, hψr, map_zero] at hfin
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfin.symm

private theorem false_of_restrictIdeal_eq_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ}
    (c : EtaleChart p V m) (Z D : X.IdealSheafData) (S : Finset (Fin m)) (s : Fin m)
    (hs : s ∉ S) (hZ : restrictIdeal Z V = c.coordIdeal S)
    (hD : restrictIdeal D V = c.coordIdeal {s})
    (ξ : ↥X) (hξV : ξ ∈ V) (hξZ : ξ ∈ Z.support) (_hξD : ξ ∈ D.support)
    (hmin : ∀ η : ↥X, η ∈ Z.support → ξ ∈ closure ({η} : Set ↥X) → η ∈ D.support) : False := by
  classical
  have hIZ : Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k m S) = Z.ideal ⟨V, hV⟩ :=
    c.map_mvPolynomialCoordIdeal_eq_ideal hV Z S hZ
  have hID : Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k m {s}) = D.ideal ⟨V, hV⟩ :=
    c.map_mvPolynomialCoordIdeal_eq_ideal hV D {s} hD
  have hDspan : D.ideal ⟨V, hV⟩ = Ideal.span {c.coord s} := by
    rw [← hID, mvPolynomialCoordIdeal_eq_span, Finset.coe_singleton, Set.image_singleton, Ideal.map_span,
      Set.image_singleton, c.coordRingHom_X]
  have hnzd : ∀ x : Γ(X, V), c.coord s * x ∈ Z.ideal ⟨V, hV⟩ → x ∈ Z.ideal ⟨V, hV⟩ := by
    intro x hx
    rw [← hIZ] at hx ⊢
    refine mem_map_of_mul_mem_of_etale_of_isSMulRegular (c.coordRingHom_etale hV) (mvPolynomialCoordIdeal k m S)
      (MvPolynomial.X (ULift.up.{u} s)) ?_ x ?_
    · intro A B hAB
      obtain ⟨A', rfl⟩ := Ideal.Quotient.mk_surjective A
      obtain ⟨B', rfl⟩ := Ideal.Quotient.mk_surjective B
      rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at hAB
      exact Ideal.Quotient.eq.mpr (mem_mvPolynomialCoordIdeal_of_X_mul_mem k m S hs (A' - B') hAB)
    · rw [c.coordRingHom_X]
      exact hx
  have hIP : Z.ideal ⟨V, hV⟩ ≤ (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal :=
    (mem_support_iff_ideal_le_asIdeal_primeIdealOf Z hV hξV).mp hξZ
  obtain ⟨Q, hQp, hIQ, hQP, hgQ⟩ :=
    exists_isPrime_between_notMem_of_mul_mem (Z.ideal ⟨V, hV⟩) (c.coord s) hnzd
      (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal (hV.primeIdealOf ⟨ξ, hξV⟩).isPrime hIP
  obtain ⟨q, hqQ⟩ : ∃ q : PrimeSpectrum Γ(X, V), q.asIdeal = Q := ⟨⟨Q, hQp⟩, rfl⟩
  have hrange : hV.fromSpec.base q ∈ V := by
    have h0 : hV.fromSpec.base q ∈ Set.range ⇑hV.fromSpec.base := ⟨q, rfl⟩
    rw [hV.range_fromSpec] at h0
    exact h0
  have hQeq : hV.primeIdealOf ⟨hV.fromSpec.base q, hrange⟩ = q := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [hV.fromSpec_primeIdealOf]
  have hηZ : hV.fromSpec.base q ∈ Z.support := by
    rw [mem_support_iff_ideal_le_asIdeal_primeIdealOf Z hV hrange, hQeq, hqQ]
    exact hIQ
  have hspec : ξ ∈ closure ({hV.fromSpec.base q} : Set ↥X) := by
    have hle : q.asIdeal ≤ (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal := by
      rw [hqQ]
      exact hQP
    have h1 : q ⤳ hV.primeIdealOf ⟨ξ, hξV⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have h2 := h1.map hV.fromSpec.base.hom.continuous
    rw [hV.fromSpec_primeIdealOf] at h2
    exact specializes_iff_mem_closure.mp h2
  have hηD := hmin _ hηZ hspec
  rw [mem_support_iff_ideal_le_asIdeal_primeIdealOf D hV hrange, hQeq, hDspan, hqQ] at hηD
  exact hgQ (hηD (Ideal.mem_span_singleton_self _))

private theorem not_subset_boundary_support_of_notMem (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme)
    (hC : C ∈ intersectionComponents T.boundary J) (i : Fin T.boundary.length) (hi : i ∉ J)
    (hsub : C ⊆ ((T.boundary.get i).support : Set ↥T.scheme)) : False := by
  classical
  obtain ⟨hirr, hCsub, hmax⟩ := hC
  have hirr' : IsIrreducible C := hirr
  have hclosed : IsClosed C :=
    isClosed_of_maximal_irreducible_subset_support (intersectionIdeal T.boundary J) hirr' hCsub hmax
  have hgen : closure ({hirr'.genericPoint} : Set ↥T.scheme) = C := by
    have h : closure ({hirr'.genericPoint} : Set ↥T.scheme) = closure C :=
      hirr'.genericPoint_closure_eq
    rw [h, hclosed.closure_eq]
  have hxiC : hirr'.genericPoint ∈ C := IsGenericPoint.mem hgen
  have hxiZ : hirr'.genericPoint ∈ (intersectionIdeal T.boundary J).support := hCsub hxiC
  have hxiD : hirr'.genericPoint ∈ (T.boundary.get i).support := hsub hxiC
  obtain ⟨U, hxiU, m, c, a, hinj, hnone, hsome⟩ := hT.snc.2 hirr'.genericPoint
  obtain ⟨V, hVaff, hxiV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.scheme.isBasis_affineOpens hxiU
  have hV : IsAffineOpen V := hVaff
  have key : ∀ j : Fin T.boundary.length, hirr'.genericPoint ∈ (T.boundary.get j).support →
      ∃ t : Fin m, a (j : ℕ) = some t ∧
        restrictIdeal (T.boundary.get j) V = (c.restrict hVU).coordIdeal {t} := by
    intro j hj
    cases hA : a (j : ℕ) with
    | none =>
        exfalso
        have h1 : restrictIdeal (T.boundary[(j : ℕ)]'j.isLt) U = ⊤ := hnone (j : ℕ) j.isLt hA
        have h2 : restrictIdeal (T.boundary.get j) U = ⊤ := by
          rw [List.get_eq_getElem]
          exact h1
        exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top (T.boundary.get j) U h2
          hirr'.genericPoint hxiU hj
    | some t =>
        refine ⟨t, rfl, ?_⟩
        have h1 : restrictIdeal (T.boundary[(j : ℕ)]'j.isLt) U = c.coordIdeal {t} :=
          hsome (j : ℕ) j.isLt t hA
        have h2 : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by
          rw [List.get_eq_getElem]
          exact h1
        exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (T.boundary.get j) {t} h2
  have hmemJ : ∀ j ∈ J, hirr'.genericPoint ∈ (T.boundary.get j).support := by
    intro j hj
    refine Scheme.IdealSheafData.support_antitone ?_ hxiZ
    rw [intersectionIdeal_eq_iSup]
    exact le_biSup T.boundary.get hj
  obtain ⟨si, hsi, hDi⟩ := key i hxiD
  obtain ⟨S, hmemS⟩ :
      ∃ S : Finset (Fin m), ∀ t : Fin m, t ∈ S ↔ ∃ j ∈ J, a (j : ℕ) = some t :=
    ⟨Finset.univ.filter (fun t : Fin m => ∃ j ∈ J, a (j : ℕ) = some t), by
      intro t
      simp⟩
  have hsiS : si ∉ S := by
    intro hmem
    obtain ⟨j, hj, haj⟩ := (hmemS si).mp hmem
    have hval : (i : ℕ) = (j : ℕ) := hinj (i : ℕ) i.isLt (j : ℕ) j.isLt si hsi haj
    have hij : i = j := Fin.eq_of_val_eq hval
    exact hi (by rw [hij]; exact hj)
  have hZV : restrictIdeal (intersectionIdeal T.boundary J) V = (c.restrict hVU).coordIdeal S := by
    have hbi : restrictIdeal (intersectionIdeal T.boundary J) V
        = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) V := by
      rw [intersectionIdeal_eq_iSup]
      exact MonomialChart.restrictIdeal_biSup_finset V T.boundary.get J
    have hcb : (c.restrict hVU).coordIdeal S = ⨆ t ∈ S, (c.restrict hVU).coordIdeal {t} :=
      MonomialChart.coordIdeal_eq_biSup_singleton T.structMap V m (c.restrict hVU) S
    rw [hbi, hcb]
    refine le_antisymm (iSup₂_le fun j hj => ?_) (iSup₂_le fun t ht => ?_)
    · obtain ⟨t, hat, hres⟩ := key j (hmemJ j hj)
      rw [hres]
      exact le_biSup (fun t : Fin m => (c.restrict hVU).coordIdeal {t})
        ((hmemS t).mpr ⟨j, hj, hat⟩)
    · obtain ⟨j, hj, hat⟩ := (hmemS t).mp ht
      obtain ⟨t', hat', hres⟩ := key j (hmemJ j hj)
      have htt : t = t' := Option.some.inj (hat.symm.trans hat')
      rw [htt, ← hres]
      exact le_biSup (fun j : Fin T.boundary.length => restrictIdeal (T.boundary.get j) V) hj
  refine false_of_restrictIdeal_eq_coordIdeal hV (c.restrict hVU) (intersectionIdeal T.boundary J) (T.boundary.get i)
    S si hsiS hZV hDi hirr'.genericPoint hxiV hxiZ hxiD ?_
  intro η hηZ hηxi
  have hirr2 : IsIrreducible (closure ({η} : Set ↥T.scheme)) := isIrreducible_singleton.closure
  have hs1 : C ⊆ closure ({η} : Set ↥T.scheme) := by
    rw [← hgen]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηxi) isClosed_closure
  have hs2 : closure ({η} : Set ↥T.scheme)
      ⊆ ((intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    closure_minimal (Set.singleton_subset_iff.mpr hηZ)
      (intersectionIdeal T.boundary J).support.2
  have heq : closure ({η} : Set ↥T.scheme) = C := hmax _ hirr2 hs1 hs2
  have hηC : η ∈ C := by
    rw [← heq]
    exact subset_closure (Set.mem_singleton η)
  exact hsub hηC

theorem intersectionComponents_subset_support_iff : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)),
      ∀ C ∈ intersectionComponents T.boundary J,
        ∀ (i : Fin T.boundary.length),
          C ⊆ ((T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J := by
  intro T hT J C hC i
  constructor
  · intro hsub
    by_contra hi
    exact not_subset_boundary_support_of_notMem T hT J C hC i hi hsub
  · intro hi x hx
    have hle : T.boundary.get i ≤ intersectionIdeal T.boundary J := by
      rw [intersectionIdeal_eq_iSup]
      exact le_biSup T.boundary.get hi
    exact Scheme.IdealSheafData.support_antitone hle (hC.2.1 hx)

end FunctorialResolution.EmbeddedResolution

end
