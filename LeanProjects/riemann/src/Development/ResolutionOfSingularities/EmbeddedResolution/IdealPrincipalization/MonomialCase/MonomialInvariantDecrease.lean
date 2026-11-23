import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BlowupAtMonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LexOrderEncoding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

noncomputable abbrev blowupTripleAtCenterIdeal (T : MarkedIdealWithBoundary.{u}) : MarkedIdealWithBoundary.{u} :=
  @MarkedIdealWithBoundary.mk T.base T.instField
    (Blowup.blowup (monomialCenter T.ideal T.mult T.boundary))
    (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary) ≫ T.structMap)
    (residualByPow (T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)))
      ((monomialCenter T.ideal T.mult T.boundary).comap
        (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) T.mult)
    T.mult
    (transformedBoundary (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
      (monomialCenter T.ideal T.mult T.boundary) T.boundary)

private theorem foldr_mul_ofFn_eq_prod {Y : Scheme.{u}} :
    ∀ {n : ℕ} (F : Fin n → Y.IdealSheafData),
      List.foldr (· * ·) (⊤ : Y.IdealSheafData) (List.ofFn F) = ∏ i, F i := by
  intro n
  induction n with
  | zero =>
      intro F
      simp only [List.ofFn_zero, List.foldr_nil, Finset.univ_eq_empty, Finset.prod_empty]
      exact Scheme.IdealSheafData.one_eq_top.symm
  | succ n ih =>
      intro F
      rw [List.ofFn_succ, List.foldr_cons, ih, Fin.prod_univ_succ]

private theorem comap_prod {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∀ {n : ℕ} (F : Fin n → Y.IdealSheafData),
      (∏ i, F i).comap f = ∏ i, (F i).comap f := by
  intro n
  induction n with
  | zero =>
      intro F
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      rw [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top]
      exact Scheme.IdealSheafData.one_eq_top.symm
  | succ n ih =>
      intro F
      rw [Fin.prod_univ_succ, Scheme.IdealSheafData.comap_mul, ih, Fin.prod_univ_succ]

private theorem prod_pow_comap_transformedBoundary_eq {X X' : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (L : List X.IdealSheafData) (W : X'.Opens)
    (a : Fin L.length → ℕ) (d : ℕ) :
    (∏ i : Fin (transformedBoundary π Z L).length,
        (((transformedBoundary π Z L).get i).comap W.ι) ^
          (if hi : (i : ℕ) < L.length then a ⟨i, hi⟩ else d))
      = (∏ i : Fin L.length, ((Blowup.strictTransform π Z (L.get i)).comap W.ι) ^ a i)
          * ((Blowup.exceptionalIdeal π Z).comap W.ι) ^ d := by
  classical
  have hlen : (transformedBoundary π Z L).length = L.length + 1 := transformedBoundary_length π Z L
  have hg1 : ∀ j : Fin L.length,
      (transformedBoundary π Z L).get (Fin.cast hlen.symm (Fin.castSucc j))
        = Blowup.strictTransform π Z (L.get j) := by
    intro j
    simp [transformedBoundary, List.get_eq_getElem, j.isLt]
  have hg2 : (transformedBoundary π Z L).get (Fin.cast hlen.symm (Fin.last L.length))
      = Blowup.exceptionalIdeal π Z := by
    simp [transformedBoundary, List.get_eq_getElem]
  rw [Fintype.prod_equiv (finCongr hlen)
      (fun i : Fin (transformedBoundary π Z L).length =>
        (((transformedBoundary π Z L).get i).comap W.ι) ^
          (if hi : (i : ℕ) < L.length then a ⟨i, hi⟩ else d))
      (fun j : Fin (L.length + 1) =>
        (((transformedBoundary π Z L).get (Fin.cast hlen.symm j)).comap W.ι) ^
          (if hj : (j : ℕ) < L.length then a ⟨j, hj⟩ else d))
      (fun i => by simp)]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro j _
    rw [hg1 j]
    exact congrArg (fun t : ℕ => ((Blowup.strictTransform π Z (L.get j)).comap W.ι) ^ t) (dif_pos j.isLt)
  · rw [hg2, dif_neg (by simp : ¬ ((Fin.last L.length : Fin (L.length + 1)) : ℕ) < L.length)]

private theorem isMonomialNear_transformedBoundary_of_isBlowupAlongIdealSheaf (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData)
    (hblow : Blowup.IsBlowupAlongIdealSheaf π Z)
    (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap))
    (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (hZco : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult)
    (hZsupp : (↑Z.support : Set ↥T.scheme) = ⋃₀ centerComponents T.ideal T.mult T.boundary)
    (J : X'.IdealSheafData)
    (hJ : (Z.comap π) ^ T.mult * J = T.ideal.comap π)
    (x' : ↥X') (hx' : x' ∈ orderAtLeastLocus J T.mult) :
    MonomialCenter.IsMonomialNear (transformedBoundary π Z T.boundary) J x' := by
  classical
  have hmemcompl : ∀ y : ↥T.scheme, y ∈ (Z.support.compl : T.scheme.Opens) ↔ y ∉ Z.support :=
    fun y => Iff.rfl
  have hzc : π x' ∈ orderAtLeastLocus T.ideal T.mult := by
    by_cases hxe : x' ∈ (Z.comap π).support
    · exact hZco (by exact Scheme.IdealSheafData.mem_support_comap.1 hxe)
    · have h1 : (T.mult : ℕ∞) ≤ orderAt J x' := (mem_orderAtLeastLocus_iff _ _ _).1 hx'
      have h2 : orderAt J x' ≤ orderAt (T.ideal.comap π) x' := by
        have hmul := add_orderAt_le_orderAt_mul ((Z.comap π) ^ T.mult) J x'
        rw [hJ] at hmul
        exact le_trans le_add_self hmul
      have h3 : orderAt (T.ideal.comap π) x' = orderAt T.ideal (π x') := by
        refine hGeom.orderAt_comap_off_exceptional T hT.valid _ π Z hblow x' ?_ T.ideal
        rw [Blowup.exceptionalIdeal_eq_comap]
        exact hxe
      exact (mem_orderAtLeastLocus_iff _ _ _).2 (by rw [← h3]; exact le_trans h1 h2)
  obtain ⟨U, hzU, a, hmon⟩ := hT.monomialNear (π x') hzc
  have hbt : ∀ i : Fin T.boundary.length, ∃ (V : X'.Opens) (ε : ℕ),
      x' ∈ V ∧ (ε = 0 ∨ ε = 1) ∧
        (ε = 1 ↔ ∃ O : T.scheme.Opens, π x' ∈ O ∧
          (↑Z.support : Set ↥T.scheme) ∩ (↑O : Set ↥T.scheme) ⊆
            (↑(T.boundary.get i).support : Set ↥T.scheme)) ∧
        ((T.boundary.get i).comap π).comap V.ι =
          (Blowup.strictTransform π Z (T.boundary.get i)).comap V.ι *
            (Blowup.exceptionalIdeal π Z).comap V.ι ^ ε := by
    intro i
    exact hGeom.blowup_total_transform T hT.valid Z hsm hsnc
      _ π hblow (T.boundary.get i) (List.getElem_mem i.isLt) x'
  choose Vf ef hxV hef01 hefiff hefeq using hbt
  set e := ∑ i : Fin T.boundary.length, ef i * a i with hedef
  have hme : T.mult ≤ e := by
    by_cases hxe : x' ∈ (Z.comap π).support
    · have hzZ : π x' ∈ Z.support := Scheme.IdealSheafData.mem_support_comap.1 hxe
      obtain ⟨C, hC, hzC⟩ : ∃ C ∈ centerComponents T.ideal T.mult T.boundary, π x' ∈ C := by
        have hmem : π x' ∈ ⋃₀ centerComponents T.ideal T.mult T.boundary := by
          rw [← hZsupp]; exact hzZ
        exact hmem
      have hCc : C ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
        centerComponents_subset_intersectionComponents _ _ _ hC
      have hord : orderAlong T.ideal C
          = ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ℕ∞) :=
        orderAlong_eq_sum_of_monomial hGeom hT hCc hzC U hzU a hmon
      have hCmax : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary :=
        ((mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hC).2
      have hmax : (T.mult : ℕ∞) ≤ maxCandidateOrder T.ideal T.mult T.boundary := by
        have hne : minIndexCard T.ideal T.mult T.boundary ≠ 0 := by
          intro h0
          have hemp : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme) :=
            orderAtLeastLocus_eq_empty_of_minIndexCard_eq_zero hGeom hT h0
          have : π x' ∈ (∅ : Set ↥T.scheme) := by rw [← hemp]; exact hzc
          exact this.elim
        exact (maxCandidateOrder_spec hGeom hT hne).2.2.1
      have hsum : T.mult ≤ ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by
        have hcast : (T.mult : ℕ∞)
            ≤ ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ℕ∞) := by
          rw [← hord, hCmax]; exact hmax
        exact_mod_cast hcast
      have hef1 : ∀ j ∈ lexMaxIndices T.ideal T.mult T.boundary, ef j = 1 := by
        intro j hj
        refine (hefiff j).2 ⟨⊤, trivial, ?_⟩
        intro y hy
        have hy1 : y ∈ (↑Z.support : Set ↥T.scheme) := hy.1
        rw [hZsupp] at hy1
        obtain ⟨C', hC', hyC'⟩ := hy1
        exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT
          (centerComponents_subset_intersectionComponents _ _ _ hC') j).2 hj hyC'
      calc T.mult ≤ ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := hsum
        _ = ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, ef j * a j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hef1 j hj, one_mul]
        _ ≤ e := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    · have hzZ : π x' ∉ Z.support := fun hc => hxe (Scheme.IdealSheafData.mem_support_comap.2 hc)
      have hef1 : ∀ i : Fin T.boundary.length, ef i = 1 := by
        intro i
        refine (hefiff i).2 ⟨Z.support.compl, (hmemcompl (π x')).2 hzZ, ?_⟩
        intro y hy
        have hy2 : y ∉ Z.support := (hmemcompl y).1 hy.2
        exact absurd hy.1 hy2
      have hordz : orderAt T.ideal (π x')
          = ((∑ j ∈ supportIndices T.boundary (π x'), a j : ℕ) : ℕ∞) :=
        orderAt_eq_sum_supportIndices hGeom hT (π x') U hzU a hmon
      have h1 : (T.mult : ℕ∞) ≤ orderAt T.ideal (π x') := (mem_orderAtLeastLocus_iff _ _ _).1 hzc
      have hsum : T.mult ≤ ∑ j ∈ supportIndices T.boundary (π x'), a j := by
        have hcast : (T.mult : ℕ∞)
            ≤ ((∑ j ∈ supportIndices T.boundary (π x'), a j : ℕ) : ℕ∞) := by
          rw [← hordz]; exact h1
        exact_mod_cast hcast
      calc T.mult ≤ ∑ j ∈ supportIndices T.boundary (π x'), a j := hsum
        _ ≤ ∑ j : Fin T.boundary.length, a j :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = e := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [hef1 j, one_mul]
  set W : X'.Opens :=
    ⟨(⋂ i : Fin T.boundary.length, ((Vf i : X'.Opens) : Set ↥X'))
        ∩ ((π ⁻¹ᵁ U : X'.Opens) : Set ↥X'),
      (isOpen_iInter_of_finite fun i => (Vf i).isOpen).inter (π ⁻¹ᵁ U).isOpen⟩ with hWdef
  have hxW : x' ∈ W := ⟨Set.mem_iInter.2 (fun i => hxV i), hzU⟩
  have hWU : W ≤ π ⁻¹ᵁ U := fun y hy => hy.2
  have hbi : ∀ i : Fin T.boundary.length,
      ((T.boundary.get i).comap π).comap W.ι =
        (Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι
          * ((Z.comap π).comap W.ι) ^ ef i := by
    intro i
    have hle : W ≤ Vf i := fun y hy => Set.mem_iInter.1 hy.1 i
    have hcongr := congrArg (fun A => A.comap (X'.homOfLE hle)) (hefeq i)
    simpa [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
      ← restrictIdeal_eq_comap_homOfLE_restrictIdeal, Blowup.exceptionalIdeal_eq_comap] using hcongr
  have hcomp : ((X'.homOfLE hWU) ≫ (π ∣_ U)) ≫ U.ι = W.ι ≫ π := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hg : ∀ A : T.scheme.IdealSheafData,
      (A.comap U.ι).comap ((X'.homOfLE hWU) ≫ (π ∣_ U)) = (A.comap π).comap W.ι := by
    intro A
    simp only [← Scheme.IdealSheafData.comap_comp]
    rw [hcomp]
  rw [foldr_mul_ofFn_eq_prod] at hmon
  have hmonW : (T.ideal.comap π).comap W.ι =
      ∏ i : Fin T.boundary.length, (((T.boundary.get i).comap π).comap W.ι) ^ a i := by
    calc (T.ideal.comap π).comap W.ι
        = (T.ideal.comap U.ι).comap ((X'.homOfLE hWU) ≫ (π ∣_ U)) := (hg _).symm
      _ = (∏ i : Fin T.boundary.length, ((T.boundary.get i).comap U.ι) ^ a i).comap
            ((X'.homOfLE hWU) ≫ (π ∣_ U)) := by rw [hmon]
      _ = ∏ i : Fin T.boundary.length,
            (((T.boundary.get i).comap U.ι) ^ a i).comap
              ((X'.homOfLE hWU) ≫ (π ∣_ U)) := comap_prod _ _
      _ = ∏ i : Fin T.boundary.length, (((T.boundary.get i).comap π).comap W.ι) ^ a i := by
            refine Finset.prod_congr rfl ?_
            intro i _
            rw [Scheme.IdealSheafData.comap_pow, hg]
  have hprod : (T.ideal.comap π).comap W.ι =
      (∏ i : Fin T.boundary.length,
          ((Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι) ^ a i)
        * ((Z.comap π).comap W.ι) ^ e := by
    rw [hmonW]
    have hterm : ∀ i : Fin T.boundary.length,
        (((T.boundary.get i).comap π).comap W.ι) ^ a i
          = ((Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι) ^ a i
              * (((Z.comap π).comap W.ι) ^ (ef i * a i)) := by
      intro i
      rw [hbi i, mul_pow, ← pow_mul]
    rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((Z.comap π).comap W.ι) := by
    have h0 : Blowup.IsLocallyGeneratedByNonZeroDivisor (Z.comap π) := by
      have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hblow
      rwa [Blowup.exceptionalIdeal_eq_comap] at hc
    exact h0.comap_of_isOpenImmersion W.ι
  have hcomapJ : ((Z.comap π).comap W.ι) ^ T.mult * J.comap W.ι
      = (T.ideal.comap π).comap W.ι := by
    rw [← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_mul, hJ]
  have hrw : ((Z.comap π).comap W.ι) ^ T.mult *
      ((∏ i : Fin T.boundary.length,
          ((Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι) ^ a i)
        * ((Z.comap π).comap W.ι) ^ (e - T.mult))
      = (∏ i : Fin T.boundary.length,
          ((Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι) ^ a i)
        * ((Z.comap π).comap W.ι) ^ e := by
    rw [← mul_assoc, mul_comm (((Z.comap π).comap W.ι) ^ T.mult), mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hme]
  have hfinal : J.comap W.ι =
      (∏ i : Fin T.boundary.length,
          ((Blowup.strictTransform π Z (T.boundary.get i)).comap W.ι) ^ a i)
        * ((Z.comap π).comap W.ι) ^ (e - T.mult) := by
    refine eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul hcart T.mult ?_
    rw [hcomapJ, hrw, hprod]
  refine ⟨W, hxW, fun i => if hi : (i : ℕ) < T.boundary.length then a ⟨i, hi⟩ else e - T.mult, ?_⟩
  rw [foldr_mul_ofFn_eq_prod,
    prod_pow_comap_transformedBoundary_eq π Z T.boundary W a (e - T.mult), Blowup.exceptionalIdeal_eq_comap]
  exact hfinal

theorem isLocallyMonomialTriple_blowupTripleAtCenterIdeal (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    MonomialCenter.IsLocallyMonomialTriple (blowupTripleAtCenterIdeal T) := by
  refine ⟨?_, ?_⟩
  · have key := hGeom.level_valid T hT.valid
      (MarkedBlowupSequenceData.ofSingleBlowup T.structMap T.ideal T.mult T.boundary
        (monomialCenter T.ideal T.mult T.boundary)
        (smooth_monomialCenter hGeom hT h) (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h)
        (support_monomialCenter_subset_orderAtLeastLocus hGeom hT h)
        (exists_controlledTransform_monomialCenter hGeom hT h)).toMarkedSequenceOfBlowups 1
      (by rw [MarkedBlowupSequenceData.toMarkedSequence_length]; exact Nat.le_refl 1)
    exact key
  · intro x' hx'
    refine isMonomialNear_transformedBoundary_of_isBlowupAlongIdealSheaf hGeom hT
      (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
      (monomialCenter T.ideal T.mult T.boundary)
      (Blowup.blowup.isBlowupAlongIdealSheaf_proj _)
      (smooth_monomialCenter hGeom hT h)
      (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h)
      (support_monomialCenter_subset_orderAtLeastLocus hGeom hT h)
      (by
        rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents])
      (residualByPow (T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)))
        ((monomialCenter T.ideal T.mult T.boundary).comap
          (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) T.mult)
      (pow_mul_residualByPow _ _ _ (exists_controlledTransform_monomialCenter hGeom hT h))
      x' hx'

private theorem krullDimSucc_schemeAt_one_le_dim (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (d : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hlen : 1 ≤ d.length) :
    krullDimSucc (d.obj 1) ≤ T.krullDimSucc := by
  have key := hGeom.level_schemeDim_le T hT.valid d.toMarkedSequenceOfBlowups 1
    (by rw [MarkedBlowupSequenceData.toMarkedSequence_length]; exact hlen)
  rwa [MarkedBlowupSequenceData.toMarkedSequence_schemeAt] at key

theorem krullDimSucc_blowupTripleAtCenterIdeal_le (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    krullDimSucc (blowupTripleAtCenterIdeal T).scheme ≤ T.krullDimSucc :=
  krullDimSucc_schemeAt_one_le_dim hGeom hT
    (MarkedBlowupSequenceData.ofSingleBlowup T.structMap T.ideal T.mult T.boundary
      (monomialCenter T.ideal T.mult T.boundary)
      (smooth_monomialCenter hGeom hT h) (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h)
      (support_monomialCenter_subset_orderAtLeastLocus hGeom hT h)
      (exists_controlledTransform_monomialCenter hGeom hT h))
    (Nat.le_refl 1)

private theorem orderAt_controlledTransform_eq_of_notMem_support (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) {X' : Scheme.{u}} (π : X' ⟶ T.scheme)
    (Z : T.scheme.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I' : X'.IdealSheafData)
    (hI' : (Z.comap π) ^ T.mult * I' = T.ideal.comap π) (x' : ↥X')
    (hx' : x' ∉ (Z.comap π).support) :
    orderAt I' x' = orderAt T.ideal (π x') := by
  have h1 : stalkIdeal (Z.comap π) x' = 1 := by
    rw [Ideal.one_eq_top]
    by_contra hc
    exact hx' ((mem_support_iff_stalkIdeal_ne_top _ _).2 hc)
  have h2 : stalkIdeal (T.ideal.comap π) x' = stalkIdeal I' x' := by
    rw [← hI', stalkIdeal_mul, stalkIdeal_pow, h1, one_pow, one_mul]
  have h3 : orderAt I' x' = orderAt (T.ideal.comap π) x' :=
    orderAt_eq_of_stalkIdeal_eq h2.symm
  rw [h3]
  exact hGeom.orderAt_comap_off_exceptional T hT.valid _ π Z hπ x'
    (by rw [Blowup.exceptionalIdeal_eq_comap]; exact hx') T.ideal

private theorem get_transformedBoundary_strictTransformIndex_eq_strictTransform {X' X : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (L : List X.IdealSheafData) (j : Fin L.length) :
    (transformedBoundary π Z L).get (strictTransformIndex π Z L j) = Blowup.strictTransform π Z (L.get j) := by
  simp [transformedBoundary, List.get_eq_getElem, strictTransformIndex_val, j.isLt]

private theorem get_transformedBoundary_exceptionalIndex_eq_comap {X' X : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (L : List X.IdealSheafData) :
    (transformedBoundary π Z L).get (exceptionalIndex π Z L) = Z.comap π := by
  have hlen : (transformedBoundary π Z L).length = L.length + 1 :=
    transformedBoundary_length π Z L
  have hg2 : (transformedBoundary π Z L).get (Fin.cast hlen.symm (Fin.last L.length))
      = Blowup.exceptionalIdeal π Z := by
    simp [transformedBoundary, List.get_eq_getElem]
  have hfin : exceptionalIndex π Z L = Fin.cast hlen.symm (Fin.last L.length) := by
    apply Fin.val_injective
    simp [exceptionalIndex_val]
  rw [hfin, hg2, Blowup.exceptionalIdeal_eq_comap]

private theorem injective_strictTransformIndex {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) : Function.Injective (strictTransformIndex π Z L) := by
  intro i j hij
  apply Fin.val_injective
  have h := congrArg (fun z : Fin (transformedBoundary π Z L).length => (z : ℕ)) hij
  simpa [strictTransformIndex_val] using h

private theorem strictMono_strictTransformIndex {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) : StrictMono (strictTransformIndex π Z L) := by
  intro i j hij
  rw [Fin.lt_def, strictTransformIndex_val, strictTransformIndex_val]
  exact hij

private theorem sortedIndices_image_strictTransformIndex {X' X : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (L : List X.IdealSheafData) (S : Finset (Fin L.length)) :
    MonomialCenter.sortedIndices (Finset.image (strictTransformIndex π Z L) S)
      = MonomialCenter.sortedIndices S := by
  rw [MonomialCenter.sortedIndices_image_of_strictMono (strictTransformIndex π Z L)
    (strictMono_strictTransformIndex π Z L) S]
  simp only [strictTransformIndex_val]
  rfl

private theorem image_strictTransformIndex_preimageStrictTransformIndex_eq_erase {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData)
    (J' : Finset (Fin (transformedBoundary π Z L).length)) :
    Finset.image (strictTransformIndex π Z L) (preimageStrictTransformIndex π Z L J') = J'.erase (exceptionalIndex π Z L) := by
  classical
  have hlen : (transformedBoundary π Z L).length = L.length + 1 :=
    transformedBoundary_length π Z L
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    refine Finset.mem_erase.2 ⟨?_, (mem_preimageStrictTransformIndex_iff π Z L J' j).1 hj⟩
    intro hc
    have h1 : ((strictTransformIndex π Z L j : Fin (transformedBoundary π Z L).length) : ℕ) = L.length := by
      rw [hc, exceptionalIndex_val]
    rw [strictTransformIndex_val] at h1
    exact absurd h1 (Nat.ne_of_lt j.isLt)
  · intro hi
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hi
    have h1 : (i : ℕ) < (transformedBoundary π Z L).length := i.isLt
    have h2 : (i : ℕ) ≠ L.length := by
      intro hc
      exact hne (Fin.val_injective (by rw [hc, exceptionalIndex_val]))
    have hlt : (i : ℕ) < L.length := by omega
    have hid : strictTransformIndex π Z L ⟨(i : ℕ), hlt⟩ = i := Fin.val_injective (by rw [strictTransformIndex_val])
    refine Finset.mem_image.2 ⟨⟨(i : ℕ), hlt⟩, ?_, hid⟩
    exact (mem_preimageStrictTransformIndex_iff π Z L J' ⟨(i : ℕ), hlt⟩).2 (by rw [hid]; exact hmem)

private theorem sum_lt_mult_of_card_lt_minIndexCard (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) {x : ↥T.scheme} {U : T.scheme.Opens}
    (hxU : x ∈ U) (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤)
    (S : Finset (Fin T.boundary.length)) (hS : ∀ j ∈ S, x ∈ (T.boundary.get j).support)
    (hcard : S.card < minIndexCard T.ideal T.mult T.boundary) :
    ∑ j ∈ S, a j < T.mult := by
  classical
  by_contra hc
  push Not at hc
  have hxsupp : x ∈ (↑(intersectionIdeal T.boundary S).support : Set ↥T.scheme) :=
    mem_support_intersectionIdeal T.boundary S x hS
  obtain ⟨C, hxC, hC⟩ := exists_mem_intersectionComponents_of_mem_support T.boundary S x hxsupp
  have hord : orderAlong T.ideal C = ((∑ j ∈ S, a j : ℕ) : ℕ∞) :=
    orderAlong_eq_sum_of_monomial hGeom hT hC hxC U hxU a hmon
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary S.card S C :=
    ⟨rfl, hC, by rw [hord]; exact_mod_cast hc⟩
  have hone : 1 ≤ S.card := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hp
    · exfalso
      have hS0 : S = ∅ := Finset.card_eq_zero.1 h0
      rw [hS0, Finset.sum_empty] at hc
      have hm1 : 1 ≤ T.mult := hT.valid.one_le_mult
      omega
    · exact hp
  have hle := (minIndexCard_spec T.ideal T.mult T.boundary ⟨S.card, hone, S, C, hcand⟩).2.2
    S.card hone S C hcand
  omega

private theorem exists_mem_intersectionComponents_orderAlong_eq (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData)
    (hZ : Z = componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (isOpen_preimage_sUnion_centerComponents hGeom hT))
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I' : X'.IdealSheafData)
    (hI' : (Z.comap π) ^ T.mult * I' = T.ideal.comap π)
    (J' : Finset (Fin (transformedBoundary π Z T.boundary).length))
    (hnew : exceptionalIndex π Z T.boundary ∉ J') {C' : Set ↥X'}
    (hC' : C' ∈ intersectionComponents (transformedBoundary π Z T.boundary) J') :
    ∃ C : Set ↥T.scheme,
      C ∈ intersectionComponents T.boundary (preimageStrictTransformIndex π Z T.boundary J') ∧
        C ∉ centerComponents T.ideal T.mult T.boundary ∧
        orderAlong I' C' = orderAlong T.ideal C := by
  classical
  have himg := (image_strictTransformIndex_preimageStrictTransformIndex_eq_erase π Z T.boundary J').trans
    (Finset.erase_eq_of_notMem hnew)
  subst hZ
  obtain ⟨hoff, C, hC, hCnot, -, hgen⟩ :=
    hGeom.transformed_components T hT.valid (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (centerComponents_subset_intersectionComponents _ _ _)
      (isOpen_preimage_sUnion_centerComponents hGeom hT) X' π hπ
      (preimageStrictTransformIndex π _ T.boundary J') C' (by rw [himg]; exact hC')
      (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC')
  refine ⟨C, hC, hCnot, ?_⟩
  have hπgen : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      = (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
    hgen _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents I' hC', orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC,
    ← hπgen]
  refine orderAt_controlledTransform_eq_of_notMem_support hGeom hT π _ hπ I' hI' _ ?_
  rw [Blowup.exceptionalIdeal_eq_comap] at hoff
  exact hoff

private theorem minIndexCard_le_card_add_one_of_exceptionalIndex_mem (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base))
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (I' : X'.IdealSheafData)
    (hI' : ((monomialCenter T.ideal T.mult T.boundary).comap π) ^ T.mult * I' = T.ideal.comap π)
    (hT' : MonomialCenter.IsLocallyMonomialTriple (blowupTriple T π q I'))
    (J' : Finset (Fin (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary).length))
    (hnew : exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∈ J')
    {C' : Set ↥X'}
    (hC' : C' ∈ intersectionComponents (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary) J')
    (hord : (T.mult : ℕ∞) ≤ orderAlong I' C') :
    minIndexCard T.ideal T.mult T.boundary
        ≤ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card + 1 ∧
      ((preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card
          < minIndexCard T.ideal T.mult T.boundary →
        orderAlong I' C' < maxCandidateOrder T.ideal T.mult T.boundary) := by
  classical
  have hgenericPtC : IsGenericPoint (isIrreducible_of_mem_intersectionComponents hC').genericPoint C' :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC'
  have hξmem : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ C' := by
    have h0 : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
        closure ({(isIrreducible_of_mem_intersectionComponents hC').genericPoint} : Set ↥X') :=
      subset_closure rfl
    rwa [hgenericPtC] at h0
  have hdiv : ∀ i : Fin (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary).length, i ∈ J' →
      C' ⊆ (↑((transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary).get i).support : Set ↥X') := by
    intro i hi
    exact (hGeom.components_subset_divisor_iff (blowupTriple T π q I') hT'.valid J' C' hC' i).2 hi
  have hξE : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
      ((monomialCenter T.ideal T.mult T.boundary).comap π).support := by
    have h1 := hdiv _ hnew
    rw [get_transformedBoundary_exceptionalIndex_eq_comap] at h1
    exact h1 hξmem
  have hπξ : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
      (monomialCenter T.ideal T.mult T.boundary).support :=
    Scheme.IdealSheafData.mem_support_comap.1 hξE
  have hπξset : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
      (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) := hπξ
  rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents] at hπξset
  obtain ⟨C₀, hC₀opt, hmem₀⟩ := hπξset
  have hcoS : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ orderAtLeastLocus T.ideal T.mult :=
    support_monomialCenter_subset_orderAtLeastLocus hGeom hT h hπξ
  obtain ⟨U, hU, a, hmon⟩ := hT.monomialNear _ hcoS
  have hkey := orderAlong_transform_add_mult_of_exceptionalIndex_mem hGeom hT h π q hπ I' hI' hT' hnew hC'
    U hU a hmon hC₀opt hmem₀
  have hC₀comp : C₀ ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
    centerComponents_subset_intersectionComponents _ _ _ hC₀opt
  have hordC₀ : orderAlong T.ideal C₀
      = ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ℕ∞) :=
    orderAlong_eq_sum_of_monomial hGeom hT hC₀comp hmem₀ U hU a hmon
  have hmaxC₀ : orderAlong T.ideal C₀ = maxCandidateOrder T.ideal T.mult T.boundary :=
    ((mem_centerComponents_iff _ _ _ C₀).1 hC₀opt).2
  rw [hordC₀] at hkey
  obtain ⟨S1, hS1⟩ : ∃ s : ℕ, s = ∑ i ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
      T.boundary J', a i := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ s : ℕ, s = ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j :=
    ⟨_, rfl⟩
  rw [← hS1, ← hS2] at hkey
  have hltop : orderAlong I' C' < ⊤ := by
    refine lt_of_le_of_lt ?_ (lt_of_le_of_ne (le_top : ((S1 : ℕ∞) + (S2 : ℕ∞)) ≤ ⊤) ?_)
    · rw [← hkey]
      exact le_self_add
    · intro hc
      have hcc : ((S1 + S2 : ℕ) : ℕ∞) = ⊤ := by rw [Nat.cast_add]; exact hc
      simp at hcc
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (ne_of_lt hltop)
  have hnm : n + T.mult = S1 + S2 := by
    have hc2 : ((n + T.mult : ℕ) : ℕ∞) = ((S1 + S2 : ℕ) : ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_add, hn]
      exact hkey
    exact_mod_cast hc2
  have hmn : T.mult ≤ n := by
    have hc3 : ((T.mult : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := by rw [hn]; exact hord
    exact_mod_cast hc3
  by_cases hk : (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card
      < minIndexCard T.ideal T.mult T.boundary
  · have holdsub : ∀ j ∈ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J',
        π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ (T.boundary.get j).support := by
      intro j hj
      have h1 := hdiv _ ((mem_preimageStrictTransformIndex_iff _ _ _ _ j).1 hj)
      rw [get_transformedBoundary_strictTransformIndex_eq_strictTransform] at h1
      have h2 : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
          (Blowup.strictTransform π (monomialCenter T.ideal T.mult T.boundary)
            (T.boundary.get j)).support := h1 hξmem
      have h3 : (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
          ((T.boundary.get j).comap π).support :=
        Scheme.IdealSheafData.support_antitone (comap_le_strictTransform π _ _) h2
      exact Scheme.IdealSheafData.mem_support_comap.1 h3
    have hp : S1 < T.mult := by
      rw [hS1]
      exact sum_lt_mult_of_card_lt_minIndexCard hGeom hT hU a hmon _ holdsub hk
    have hcardch : (lexMaxIndices T.ideal T.mult T.boundary).card
        = minIndexCard T.ideal T.mult T.boundary := card_lexMaxIndices hGeom hT h
    have hchsub : ∀ j ∈ lexMaxIndices T.ideal T.mult T.boundary,
        π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈ (T.boundary.get j).support := by
      intro j hj
      exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hC₀comp j).2 hj hmem₀
    obtain ⟨j₀, hj₀ch, hj₀old⟩ : ∃ j₀ ∈ lexMaxIndices T.ideal T.mult T.boundary,
        j₀ ∉ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J' := by
      by_contra hc
      push Not at hc
      have hsub : lexMaxIndices T.ideal T.mult T.boundary
          ⊆ preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J' :=
        fun j hj => hc j hj
      have hcc := Finset.card_le_card hsub
      omega
    have herase : (∑ j ∈ (lexMaxIndices T.ideal T.mult T.boundary).erase j₀, a j) < T.mult := by
      refine sum_lt_mult_of_card_lt_minIndexCard hGeom hT hU a hmon _
        (fun j hj => hchsub j (Finset.mem_of_mem_erase hj)) ?_
      have hce := Finset.card_erase_of_mem hj₀ch
      omega
    have hsplit : (∑ j ∈ (lexMaxIndices T.ideal T.mult T.boundary).erase j₀, a j) + a j₀ = S2 := by
      rw [hS2]
      exact Finset.sum_erase_add _ _ hj₀ch
    have hSge : T.mult ≤ ∑ j ∈ insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary J'), a j := by
      rw [Finset.sum_insert hj₀old, ← hS1]
      omega
    have hmemsupp : π (isIrreducible_of_mem_intersectionComponents hC').genericPoint ∈
        (↑(intersectionIdeal T.boundary (insert j₀ (preimageStrictTransformIndex π
          (monomialCenter T.ideal T.mult T.boundary) T.boundary J'))).support : Set ↥T.scheme) := by
      refine mem_support_intersectionIdeal T.boundary _ _ ?_
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj2
      · exact hchsub _ hj₀ch
      · exact holdsub _ hj2
    obtain ⟨C, hxC, hCcomp⟩ :=
      exists_mem_intersectionComponents_of_mem_support T.boundary _ _ hmemsupp
    have hordC : orderAlong T.ideal C
        = ((∑ j ∈ insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
            T.boundary J'), a j : ℕ) : ℕ∞) :=
      orderAlong_eq_sum_of_monomial hGeom hT hCcomp hxC U hU a hmon
    have hcand : IsCandidateComponent T.ideal T.mult T.boundary
        (insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')).card
        (insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')) C :=
      ⟨rfl, hCcomp, by rw [hordC]; exact_mod_cast hSge⟩
    have hone : 1 ≤ (insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary J')).card := Finset.card_pos.2 ⟨j₀, Finset.mem_insert_self _ _⟩
    have hminle := (minIndexCard_spec T.ideal T.mult T.boundary ⟨_, hone, _, _, hcand⟩).2.2
      _ hone _ _ hcand
    have hcardS : (insert j₀ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary J')).card
        ≤ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card + 1 :=
      Finset.card_insert_le _ _
    refine ⟨by omega, fun _ => ?_⟩
    rw [← hn, ← hmaxC₀, hordC₀, ← hS2]
    have hlt : n < S2 := by omega
    exact_mod_cast hlt
  · exact ⟨by omega, fun hc => absurd hc hk⟩

private theorem minIndexCard_lt_or_maxCandidateOrder_lt_of_isBlowupAlongIdealSheaf (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Scheme.{u}} (π : X' ⟶ T.scheme) (q : X' ⟶ Spec (CommRingCat.of T.base))
    (hZp : monomialCenter T.ideal T.mult T.boundary =
      componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
        (centerComponents T.ideal T.mult T.boundary)
        (isOpen_preimage_sUnion_centerComponents hGeom hT))
    (hπ : Blowup.IsBlowupAlongIdealSheaf π (monomialCenter T.ideal T.mult T.boundary))
    (I' : X'.IdealSheafData)
    (hI' : ((monomialCenter T.ideal T.mult T.boundary).comap π) ^ T.mult * I' = T.ideal.comap π)
    (hT' : MonomialCenter.IsLocallyMonomialTriple (blowupTriple T π q I'))
    (h' : minIndexCard I' T.mult
      (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ≠ 0) :
    minIndexCard T.ideal T.mult T.boundary
        < minIndexCard I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ∨
      (minIndexCard T.ideal T.mult T.boundary
          = minIndexCard I' T.mult
            (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ∧
        (maxCandidateOrder I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
            < maxCandidateOrder T.ideal T.mult T.boundary ∨
          (maxCandidateOrder T.ideal T.mult T.boundary
              = maxCandidateOrder I' T.mult
                (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ∧
            List.Lex (· < ·)
              (MonomialCenter.sortedIndices (lexMaxIndices T.ideal T.mult T.boundary))
              (MonomialCenter.sortedIndices
                (lexMaxIndices I' T.mult
                  (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                    T.boundary)))))) := by
  classical
  have hA : ∀ (J' : Finset (Fin (transformedBoundary π
        (monomialCenter T.ideal T.mult T.boundary) T.boundary).length)) (C' : Set ↥X'),
      C' ∈ intersectionComponents (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary) J' →
      (T.mult : ℕ∞) ≤ orderAlong I' C' → 1 ≤ J'.card →
      minIndexCard T.ideal T.mult T.boundary ≤ J'.card := by
    intro J' C' hmem hordJ hone
    by_cases hnew : exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∈ J'
    · have hx := minIndexCard_le_card_add_one_of_exceptionalIndex_mem hGeom hT h π q hπ I' hI' hT' J' hnew hmem
        hordJ
      have hcarde := Finset.card_erase_of_mem hnew
      have himg := image_strictTransformIndex_preimageStrictTransformIndex_eq_erase π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary J'
      have hcimg : (Finset.image (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
            (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')).card
          = (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card :=
        Finset.card_image_of_injective _
          (injective_strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      rw [himg] at hcimg
      have h1 := hx.1
      omega
    · obtain ⟨C, hC, -, hordeq⟩ :=
        exists_mem_intersectionComponents_orderAlong_eq hGeom hT π (monomialCenter T.ideal T.mult T.boundary)
          hZp hπ I' hI' J' hnew hmem
      have himg := (image_strictTransformIndex_preimageStrictTransformIndex_eq_erase π (monomialCenter T.ideal T.mult T.boundary) T.boundary
        J').trans (Finset.erase_eq_of_notMem hnew)
      have hcimg : (Finset.image (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
            (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J')).card
          = (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card :=
        Finset.card_image_of_injective _
          (injective_strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
      rw [himg] at hcimg
      have hcand : IsCandidateComponent T.ideal T.mult T.boundary
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J').card
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary J') C :=
        ⟨rfl, hC, by rw [← hordeq]; exact hordJ⟩
      have hone' : 1 ≤ (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
          T.boundary J').card := by omega
      have hle := (minIndexCard_spec T.ideal T.mult T.boundary ⟨_, hone', _, _, hcand⟩).2.2
        _ hone' _ _ hcand
      omega
  obtain ⟨J₁, C₁, hcand₁⟩ := exists_isCandidateComponent_minIndexCard I' T.mult
    (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) h'
  have hsplit₁ : J₁.card = minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ∧
      C₁ ∈ intersectionComponents (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary) J₁ ∧ (T.mult : ℕ∞) ≤ orderAlong I' C₁ := hcand₁
  obtain ⟨hcard₁, hmem₁, hord₁⟩ := hsplit₁
  have hone₁ : 1 ≤ J₁.card := by
    rw [hcard₁]
    exact Nat.pos_of_ne_zero h'
  have hAle : minIndexCard T.ideal T.mult T.boundary
      ≤ minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) := by
    rw [← hcard₁]
    exact hA J₁ C₁ hmem₁ hord₁ hone₁
  rcases lt_or_eq_of_le hAle with hlt | heq
  · exact Or.inl hlt
  refine Or.inr ⟨heq, ?_⟩
  have hbest' : ∃ C : Set ↥X',
      IsCandidateComponent I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
          (minIndexCard I' T.mult
            (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
          (lexMaxIndices I' T.mult
            (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) C ∧
        orderAlong I' C = maxCandidateOrder I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) :=
    (lexMaxIndices_spec hGeom hT' h').1
  obtain ⟨C', hcand', hordC'⟩ := hbest'
  have hsplit' : (lexMaxIndices I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)).card
        = minIndexCard I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ∧
      C' ∈ intersectionComponents (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
        (lexMaxIndices I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)) ∧
      (T.mult : ℕ∞) ≤ orderAlong I' C' := hcand'
  obtain ⟨hcardc', hmemc', hordc'⟩ := hsplit'
  by_cases hnew : exceptionalIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary ∈
      lexMaxIndices I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
  · left
    have hx := minIndexCard_le_card_add_one_of_exceptionalIndex_mem hGeom hT h π q hπ I' hI' hT' _ hnew hmemc'
      hordc'
    have hcarde := Finset.card_erase_of_mem hnew
    have himg := image_strictTransformIndex_preimageStrictTransformIndex_eq_erase π (monomialCenter T.ideal T.mult T.boundary) T.boundary
      (lexMaxIndices I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
    have hcimg : (Finset.image (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                T.boundary)))).card
        = (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                T.boundary))).card :=
      Finset.card_image_of_injective _
        (injective_strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
    rw [himg] at hcimg
    have hmin' : minIndexCard I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary) ≠ 0 := h'
    have hpos : 1 ≤ (lexMaxIndices I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)).card := by
      rw [hcardc']
      exact Nat.pos_of_ne_zero hmin'
    have hlt2 : (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
        (lexMaxIndices I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))).card
        < minIndexCard T.ideal T.mult T.boundary := by omega
    rw [← hordC']
    exact hx.2 hlt2
  · obtain ⟨C, hC, hCnot, hordeq⟩ :=
      exists_mem_intersectionComponents_orderAlong_eq hGeom hT π (monomialCenter T.ideal T.mult T.boundary)
        hZp hπ I' hI' _ hnew hmemc'
    have himgc := (image_strictTransformIndex_preimageStrictTransformIndex_eq_erase π (monomialCenter T.ideal T.mult T.boundary) T.boundary
      (lexMaxIndices I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))).trans
      (Finset.erase_eq_of_notMem hnew)
    have hcimg : (Finset.image (strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                T.boundary)))).card
        = (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                T.boundary))).card :=
      Finset.card_image_of_injective _
        (injective_strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
    rw [himgc] at hcimg
    have hcardJ : (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
        (lexMaxIndices I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))).card
        = minIndexCard T.ideal T.mult T.boundary := by
      rw [← hcimg, hcardc']
      exact heq.symm
    have hmC : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
      rw [← hordeq]
      exact hordc'
    have hcandJ : IsCandidateComponent T.ideal T.mult T.boundary
        (minIndexCard T.ideal T.mult T.boundary)
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
          (lexMaxIndices I' T.mult
            (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))) C :=
      ⟨hcardJ, hC, hmC⟩
    have hvle : maxCandidateOrder I' T.mult
        (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary)
        ≤ maxCandidateOrder T.ideal T.mult T.boundary := by
      rw [← hordC', hordeq]
      exact (maxCandidateOrder_spec hGeom hT h).2.1 _ _ hcandJ
    rcases lt_or_eq_of_le hvle with hv | hv
    · exact Or.inl hv
    refine Or.inr ⟨hv.symm, ?_⟩
    have hordC2 : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary := by
      rw [← hordeq, hordC', hv]
    have hbestJ : IsMaxOrderIndexSet T.ideal T.mult T.boundary
        (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
          (lexMaxIndices I' T.mult
            (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))) :=
      ⟨C, hcandJ, hordC2⟩
    have hnotlex := (lexMaxIndices_spec hGeom hT h).2 _ hbestJ
    have hsp : MonomialCenter.sortedIndices (lexMaxIndices I' T.mult
          (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
        = MonomialCenter.sortedIndices
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))) := by
      conv_lhs => rw [← himgc]
      exact sortedIndices_image_strictTransformIndex π (monomialCenter T.ideal T.mult T.boundary)
        T.boundary _
    rcases trichotomous_of (List.Lex (· < ·))
        (MonomialCenter.sortedIndices (lexMaxIndices T.ideal T.mult T.boundary))
        (MonomialCenter.sortedIndices
          (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))))
      with hlex | hlexeq | hlex
    · rw [hsp]
      exact hlex
    · exfalso
      have hJeq : preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
            (lexMaxIndices I' T.mult
              (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary) T.boundary))
          = lexMaxIndices T.ideal T.mult T.boundary := by
        ext j
        constructor
        · intro hj
          have h1 : (j : ℕ) ∈ MonomialCenter.sortedIndices
              (preimageStrictTransformIndex π (monomialCenter T.ideal T.mult T.boundary) T.boundary
                (lexMaxIndices I' T.mult
                  (transformedBoundary π (monomialCenter T.ideal T.mult T.boundary)
                    T.boundary))) := (MonomialCenter.mem_sortedIndices _ _).2 ⟨j, hj, rfl⟩
          rw [← hlexeq] at h1
          obtain ⟨j2, hj2, hvv⟩ := (MonomialCenter.mem_sortedIndices _ _).1 h1
          have hje : j2 = j := Fin.val_injective hvv
          rwa [hje] at hj2
        · intro hj
          have h1 : (j : ℕ) ∈ MonomialCenter.sortedIndices
              (lexMaxIndices T.ideal T.mult T.boundary) :=
            (MonomialCenter.mem_sortedIndices _ _).2 ⟨j, hj, rfl⟩
          rw [hlexeq] at h1
          obtain ⟨j2, hj2, hvv⟩ := (MonomialCenter.mem_sortedIndices _ _).1 h1
          have hje : j2 = j := Fin.val_injective hvv
          rwa [hje] at hj2
      apply hCnot
      refine (mem_centerComponents_iff _ _ _ C).2 ⟨⟨?_, ?_, ?_⟩, hordC2⟩
      · exact card_lexMaxIndices hGeom hT h
      · rw [← hJeq]
        exact hC
      · exact hmC
    · exact absurd hlex hnotlex

theorem minIndexCard_blowupTripleAtCenterIdeal_eq_zero_or_centerInvariant_lt (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
        (blowupTripleAtCenterIdeal T).boundary = 0 ∨
      MonomialCenter.CenterInvariant.Lt (MonomialCenter.centerInvariant T.ideal T.mult T.boundary)
        (MonomialCenter.centerInvariant (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
          (blowupTripleAtCenterIdeal T).boundary) := by
  classical
  by_cases h' : minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
      (blowupTripleAtCenterIdeal T).boundary = 0
  · exact Or.inl h'
  refine Or.inr ?_
  have hT' : MonomialCenter.IsLocallyMonomialTriple
      (blowupTriple T (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
        (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary) ≫ T.structMap)
        (residualByPow (T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)))
          ((monomialCenter T.ideal T.mult T.boundary).comap
            (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) T.mult)) :=
    isLocallyMonomialTriple_blowupTripleAtCenterIdeal hGeom hT h
  have hI' : ((monomialCenter T.ideal T.mult T.boundary).comap
        (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) ^ T.mult *
      residualByPow (T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)))
        ((monomialCenter T.ideal T.mult T.boundary).comap
          (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) T.mult
      = T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)) :=
    pow_mul_residualByPow _ _ _ (exists_controlledTransform_monomialCenter hGeom hT h)
  exact minIndexCard_lt_or_maxCandidateOrder_lt_of_isBlowupAlongIdealSheaf hGeom hT h
    (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
    (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary) ≫ T.structMap)
    (monomialCenter_eq_componentUnionIdeal hGeom hT h) (Blowup.blowup.isBlowupAlongIdealSheaf_proj _) _ hI' hT' h'

noncomputable def numMaxOrderCandidates (T : MarkedIdealWithBoundary.{u}) : ℕ :=
  {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
      IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) p.1 p.2 ∧
        orderAlong T.ideal p.2 = maxCandidateOrder T.ideal T.mult T.boundary}.ncard

noncomputable def monomialInvariant (D : ℕ) (T : MarkedIdealWithBoundary.{u}) :
    Lex (ℕ × Lex (ℕ × ℕ)) :=
  toLex (D - minIndexCard T.ideal T.mult T.boundary,
    toLex ((maxCandidateOrder T.ideal T.mult T.boundary).toNat, numMaxOrderCandidates T))

private theorem toNat_lt_toNat_of_lt_of_ne_top {a b : ℕ∞} (hab : a < b) (hb : b ≠ ⊤) :
    a.toNat < b.toNat := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hb
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hab)
  subst hn
  subst hm
  have hmn : m < n := by exact_mod_cast hab
  simpa using hmn

private theorem monomialInvariant_lt_of_lex_lt {D : ℕ} {T1 T2 : MarkedIdealWithBoundary.{u}}
    (hstep :
      D - minIndexCard T1.ideal T1.mult T1.boundary
          < D - minIndexCard T2.ideal T2.mult T2.boundary ∨
        (D - minIndexCard T1.ideal T1.mult T1.boundary
            = D - minIndexCard T2.ideal T2.mult T2.boundary ∧
          ((maxCandidateOrder T1.ideal T1.mult T1.boundary).toNat
              < (maxCandidateOrder T2.ideal T2.mult T2.boundary).toNat ∨
            ((maxCandidateOrder T1.ideal T1.mult T1.boundary).toNat
                = (maxCandidateOrder T2.ideal T2.mult T2.boundary).toNat ∧
              numMaxOrderCandidates T1 < numMaxOrderCandidates T2)))) :
    monomialInvariant D T1 < monomialInvariant D T2 := by
  have hgen : ∀ {a b c a' b' c' : ℕ},
      (a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c < c')))) →
      (toLex (a, toLex (b, c)) : Lex (ℕ × Lex (ℕ × ℕ)))
        < toLex (a', toLex (b', c')) := by
    intro a b c a' b' c' hh
    rcases hh with h1 | ⟨rfl, h1⟩
    · exact Prod.Lex.left _ _ h1
    · refine Prod.Lex.right _ ?_
      rcases h1 with h2 | ⟨rfl, h2⟩
      · exact Prod.Lex.left _ _ h2
      · exact Prod.Lex.right _ h2
  exact hgen hstep

theorem monomialInvariant_blowupTripleAtCenterIdeal_lt (hGeom : MonomialGeometryHypotheses.{u}) {D : ℕ} {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    (hD : krullDimSucc T.scheme ≤ D)
    (h' : minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
      (blowupTripleAtCenterIdeal T).boundary ≠ 0) :
    monomialInvariant D (blowupTripleAtCenterIdeal T) < monomialInvariant D T := by
  classical
  have hTstep : MonomialCenter.IsLocallyMonomialTriple (blowupTripleAtCenterIdeal T) :=
    isLocallyMonomialTriple_blowupTripleAtCenterIdeal hGeom hT h
  have hkey0 := (minIndexCard_blowupTripleAtCenterIdeal_eq_zero_or_centerInvariant_lt hGeom hT h).resolve_left h'
  have hkeyU :
      minIndexCard T.ideal T.mult T.boundary
          < minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
              (blowupTripleAtCenterIdeal T).boundary ∨
        (minIndexCard T.ideal T.mult T.boundary
            = minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
                (blowupTripleAtCenterIdeal T).boundary ∧
          (maxCandidateOrder (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
                (blowupTripleAtCenterIdeal T).boundary
              < maxCandidateOrder T.ideal T.mult T.boundary ∨
            (maxCandidateOrder T.ideal T.mult T.boundary
                = maxCandidateOrder (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
                    (blowupTripleAtCenterIdeal T).boundary ∧
              List.Lex (· < ·)
                (MonomialCenter.sortedIndices (lexMaxIndices T.ideal T.mult T.boundary))
                (MonomialCenter.sortedIndices
                  (lexMaxIndices (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
                    (blowupTripleAtCenterIdeal T).boundary))))) := hkey0
  refine monomialInvariant_lt_of_lex_lt ?_
  rcases hkeyU with hrank | ⟨hrank, hrest⟩
  · left
    obtain ⟨J, C, hcand⟩ :=
      exists_isCandidateComponent_minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
        (blowupTripleAtCenterIdeal T).boundary h'
    unfold IsCandidateComponent at hcand
    obtain ⟨hcard, hCmem, -⟩ := hcand
    have hlt : J.card < krullDimSucc (blowupTripleAtCenterIdeal T).scheme :=
      hGeom.card_lt_dim (blowupTripleAtCenterIdeal T) hTstep.valid J ⟨C, hCmem⟩
    have hdim : krullDimSucc (blowupTripleAtCenterIdeal T).scheme ≤ D :=
      le_trans (krullDimSucc_blowupTripleAtCenterIdeal_le hGeom hT h) hD
    omega
  · right
    refine ⟨by rw [hrank], ?_⟩
    rcases hrest with hval | ⟨hval, hpos⟩
    · left
      exact toNat_lt_toNat_of_lt_of_ne_top hval (maxCandidateOrder_spec hGeom hT h).2.2.2.ne
    · right
      refine ⟨by rw [hval], ?_⟩
      exact maxOrderCandidatePairs_ncard_lt_of_blowup hGeom hT h
        (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
        (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary) ≫ T.structMap)
        (Blowup.blowup.isBlowupAlongIdealSheaf_proj _)
        (residualByPow (T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)))
          ((monomialCenter T.ideal T.mult T.boundary).comap
            (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) T.mult)
        (pow_mul_residualByPow _ _ _ (exists_controlledTransform_monomialCenter hGeom hT h))
        hTstep h' hrank.symm hval.symm

end FunctorialResolution.EmbeddedResolution

end
