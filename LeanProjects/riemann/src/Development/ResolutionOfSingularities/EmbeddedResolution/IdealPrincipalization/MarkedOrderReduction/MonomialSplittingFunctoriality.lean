import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}}

private theorem mem_closure_image_iff_exists_prod_pow {α : Type*} {N : Type*} [CommMonoid N]
    (E : List α) (f : α → N) (y : N) :
    y ∈ Submonoid.closure (f '' {D | D ∈ E}) ↔
      ∃ a : Fin E.length → ℕ, y = ∏ i, f (E.get i) ^ a i := by
  constructor
  · intro hy
    induction hy using Submonoid.closure_induction with
    | mem z hz =>
        obtain ⟨D, hD, rfl⟩ := hz
        have hD' : D ∈ E := hD
        obtain ⟨i, hi⟩ := List.get_of_mem hD'
        refine ⟨fun j => if j = i then 1 else 0, ?_⟩
        have h1 : (∏ j, f (E.get j) ^ (if j = i then 1 else 0))
            = f (E.get i) ^ (if i = i then 1 else 0) :=
          Finset.prod_eq_single i (fun j _ hj => by simp [hj])
            (fun h => absurd (Finset.mem_univ i) h)
        rw [h1, hi]
        simp
    | one => exact ⟨fun _ => 0, by simp⟩
    | mul z w hz hw ihz ihw =>
        obtain ⟨a, rfl⟩ := ihz
        obtain ⟨b, rfl⟩ := ihw
        refine ⟨a + b, ?_⟩
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, pow_add]
  · rintro ⟨a, rfl⟩
    apply Submonoid.prod_mem
    intro i _
    exact pow_mem (Submonoid.subset_closure (Set.mem_image_of_mem f (by simp))) _

theorem isMonomialIn_iff_forall_exists_mem_closure (E : List X.IdealSheafData)
    (M : X.IdealSheafData) :
    IsMonomialIn E M ↔ ∀ x : ↥X, ∃ U : X.Opens, x ∈ U ∧
      M.comap U.ι ∈
        Submonoid.closure ((fun D : X.IdealSheafData => D.comap U.ι) '' {D | D ∈ E}) := by
  unfold IsMonomialIn
  refine forall_congr' fun x => exists_congr fun U => and_congr_right fun _ => ?_
  exact (mem_closure_image_iff_exists_prod_pow E (fun D : X.IdealSheafData => D.comap U.ι)
    (M.comap U.ι)).symm

theorem isMonomialIn_of_mem_of_ne_top {E E' : List X.IdealSheafData}
    (h : ∀ D ∈ E, D ≠ ⊤ → D ∈ E') {M : X.IdealSheafData} (hM : IsMonomialIn E M) :
    IsMonomialIn E' M := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hM ⊢
  intro x
  obtain ⟨U, hxU, hMU⟩ := hM x
  refine ⟨U, hxU, Submonoid.mem_closure.mp hMU _ ?_⟩
  rintro y ⟨D, hD, rfl⟩
  by_cases hDtop : D = ⊤
  · have h1 : D.comap U.ι = 1 := by
      rw [hDtop]
      simp
    show D.comap U.ι ∈ _
    rw [h1]
    exact Submonoid.one_mem _
  · exact Submonoid.subset_closure ⟨D, h D hD hDtop, rfl⟩

theorem isMonomialIn_of_setOf_mem_ne_top_eq {E E' : List X.IdealSheafData}
    (h : {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} = {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤})
    {M : X.IdealSheafData} (hM : IsMonomialIn E M) :
    IsMonomialIn E' M := by
  refine isMonomialIn_of_mem_of_ne_top (fun D hD hDtop => ?_) hM
  have hmem : D ∈ {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} := ⟨hD, hDtop⟩
  rw [h] at hmem
  exact hmem.1

theorem isMonomialSplitting_of_setOf_mem_ne_top_eq {E E' : List X.IdealSheafData}
    (h : {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} = {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤})
    {I M N : X.IdealSheafData} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting E' I M N := by
  refine ⟨hs.eq_mul, ?_, isMonomialIn_of_setOf_mem_ne_top_eq h hs.monomial, ?_⟩
  · intro x hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 (hs.monomial_support hx)
    have hDtop : D ≠ ⊤ := by
      intro hDt
      have hempty : (↑D.support : Set ↥X) = ∅ :=
        (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty D).1 hDt
      rw [hempty] at hxD
      simp at hxD
    have hmem : D ∈ {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} := ⟨hD, hDtop⟩
    rw [h] at hmem
    exact Set.mem_iUnion₂.2 ⟨D, hmem.1, hxD⟩
  · intro D hD C hC hCsubD hCmax
    by_cases hDtop : D = ⊤
    · exfalso
      have hempty : (↑D.support : Set ↥X) = ∅ :=
        (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty D).1 hDtop
      obtain ⟨y, hy⟩ := hC.nonempty
      have hy' := hCsubD hy
      rw [hempty] at hy'
      simp at hy'
    · have hmem : D ∈ {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤} := ⟨hD, hDtop⟩
      rw [← h] at hmem
      exact hs.transversal D hmem.1 C hC hCsubD hCmax

private theorem mem_nontrivialPart_iff (E : List X.IdealSheafData)
    (D : X.IdealSheafData) :
    D ∈ MarkedIdealWithBoundary.nontrivialPart E ↔ D ∈ E ∧ D ≠ ⊤ := by
  classical
  simp [MarkedIdealWithBoundary.nontrivialPart, List.mem_filter]

theorem MarkedIdealWithBoundary.SameNontrivialBoundary.setOf_mem_ne_top_eq {E E' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') :
    {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} = {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤} := by
  have hE : MarkedIdealWithBoundary.nontrivialPart E = MarkedIdealWithBoundary.nontrivialPart E' :=
    (MarkedIdealWithBoundary.sameNontrivialBoundary_iff E E').1 h
  ext D
  constructor
  · intro hD
    have hD' := (mem_nontrivialPart_iff E D).2 hD
    rw [hE] at hD'
    exact (mem_nontrivialPart_iff E' D).1 hD'
  · intro hD
    have hD' := (mem_nontrivialPart_iff E' D).2 hD
    rw [← hE] at hD'
    exact (mem_nontrivialPart_iff E D).1 hD'

theorem isMonomialSplitting_congr {E E' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') (I M N : X.IdealSheafData) :
    IsMonomialSplitting E I M N ↔ IsMonomialSplitting E' I M N :=
  ⟨fun hs => isMonomialSplitting_of_setOf_mem_ne_top_eq h.setOf_mem_ne_top_eq hs,
    fun hs => isMonomialSplitting_of_setOf_mem_ne_top_eq h.symm.setOf_mem_ne_top_eq hs⟩

private theorem coe_support_top_eq_empty {X : Scheme.{u}} :
    ((⊤ : X.IdealSheafData).support : Set ↥X) = ∅ :=
  (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty
    (⊤ : X.IdealSheafData)).1 rfl

theorem isMonomialSplitting_nil (I : X.IdealSheafData) :
    IsMonomialSplitting ([] : List X.IdealSheafData) I ⊤ I := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Scheme.IdealSheafData.one_eq_top, one_mul]
  · rw [coe_support_top_eq_empty]
    exact Set.empty_subset _
  · intro x
    refine ⟨⊤, by simp, fun _ => 0, ?_⟩
    rw [Scheme.IdealSheafData.comap_top, ← Scheme.IdealSheafData.one_eq_top]
    exact (Fin.prod_univ_zero _).symm
  · intro D hD
    exact absurd hD (by simp)

namespace IsMonomialSplitting

variable {E : List X.IdealSheafData} {I M N : X.IdealSheafData}

theorem le_nonMonomial (h : IsMonomialSplitting E I M N) : I ≤ N := by
  rw [h.eq_mul, Scheme.IdealSheafData.le_def]
  intro U
  rw [Scheme.IdealSheafData.ideal_mul]
  exact Ideal.mul_le_right

theorem support_nonMonomial_subset (h : IsMonomialSplitting E I M N) :
    (↑N.support : Set ↥X) ⊆ (↑I.support : Set ↥X) := by
  intro x hx
  have hxN : x ∈ N.support := hx
  have hIN : I ≤ N := h.le_nonMonomial
  have h1 : stalkIdeal N x ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top N x).1 hxN
  have h2 : stalkIdeal I x ≠ ⊤ := by
    intro hI
    apply h1
    have hle := stalkIdeal_mono hIN x
    rw [hI] at hle
    exact top_le_iff.1 hle
  exact (mem_support_iff_stalkIdeal_ne_top I x).2 h2

theorem nonzeroOnComponents_nonMonomial (h : IsMonomialSplitting E I M N)
    (hI : NonzeroOnComponents I) : NonzeroOnComponents N := by
  rw [nonzeroOnComponents_iff] at hI ⊢
  intro T hT hTsub
  exact hI T hT (hTsub.trans h.support_nonMonomial_subset)

theorem orderAt_eq_add {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    {E : List Y.IdealSheafData} {I M N : Y.IdealSheafData}
    (h : IsMonomialSplitting E I M N) (x : ↥Y) :
    orderAt I x = orderAt M x + orderAt N x := by
  rw [h.eq_mul]
  exact orderAt_mul k p M N x

private theorem idealSheafData_comap_prod {Z W : Scheme.{u}} (f : W ⟶ Z) {κ : Type*}
    (s : Finset κ) (J : κ → Z.IdealSheafData) :
    (∏ i ∈ s, J i).comap f = ∏ i ∈ s, (J i).comap f := by
  induction s using Finset.cons_induction
  · rw [Finset.prod_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.one_eq_top]
  · rename_i b t hb ih
    rw [Finset.prod_cons, Finset.prod_cons, Scheme.IdealSheafData.comap_mul, ih]

theorem exists_comap_eq_prod_pow_of_orderAt_eq_zero (h : IsMonomialSplitting E I M N) {x : ↥X}
    (hx : orderAt N x = 0) :
    ∃ (U : X.Opens) (e : Fin E.length → ℕ), x ∈ U ∧
      I.comap U.ι = ∏ i : Fin E.length, ((E.get i).comap U.ι) ^ e i := by
  have hmon : ∀ y : ↥X, ∃ V : X.Opens, y ∈ V ∧ ∃ c : Fin E.length → ℕ,
      M.comap V.ι = ∏ i : Fin E.length, ((E.get i).comap V.ι) ^ c i := h.monomial
  obtain ⟨U, hxU, a, haM⟩ := hmon x
  have hxN : x ∉ N.support := (orderAt_eq_zero_iff_not_mem_support N x).1 hx
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : X.Opens, (U₀ : Set ↥X) = ((N.support : Set ↥X))ᶜ :=
    ⟨⟨((N.support : Set ↥X))ᶜ, N.support.2.isOpen_compl⟩, rfl⟩
  have hx0 : x ∈ (U₀ : Set ↥X) := by
    rw [hU₀]
    exact hxN
  have hxV : x ∈ U ⊓ U₀ := by
    have hmem : x ∈ ((U ⊓ U₀ : X.Opens) : Set ↥X) := by
      rw [TopologicalSpace.Opens.coe_inf]
      exact ⟨hxU, hx0⟩
    exact hmem
  have hle : U ⊓ U₀ ≤ U := inf_le_left
  have hcomp : X.homOfLE hle ≫ U.ι = (U ⊓ U₀).ι := by simp
  have restr : ∀ J : X.IdealSheafData,
      (J.comap U.ι).comap (X.homOfLE hle) = J.comap (U ⊓ U₀).ι := by
    intro J
    rw [← hcomp, Scheme.IdealSheafData.comap_comp]
  have hNtop : N.comap (U ⊓ U₀).ι = ⊤ := by
    refine Blowup.comap_eq_top_of_notMem_support _ N ?_
    intro y hy
    have hy1 : ((U ⊓ U₀).ι y) ∈ ((U ⊓ U₀ : X.Opens) : Set ↥X) := y.2
    rw [TopologicalSpace.Opens.coe_inf, hU₀] at hy1
    exact hy1.2 hy
  have hM : M.comap (U ⊓ U₀).ι
      = ∏ i : Fin E.length, ((E.get i).comap (U ⊓ U₀).ι) ^ a i := by
    rw [← restr M, haM, idealSheafData_comap_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Scheme.IdealSheafData.comap_pow, restr]
  refine ⟨U ⊓ U₀, a, hxV, ?_⟩
  rw [h.eq_mul, Scheme.IdealSheafData.comap_mul, hNtop,
    ← Scheme.IdealSheafData.one_eq_top, mul_one, hM]

end IsMonomialSplitting

namespace PrincipalizationGeometryHypotheses

theorem isMonomialSplitting_monomialPart_nonMonomialPart (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) :
    IsMonomialSplitting T.boundary T.ideal (monomialPart T.boundary T.ideal)
      (nonMonomialPart T.boundary T.ideal) := by
  obtain ⟨M, N, h⟩ := hG.splitting_exists T hT
  exact EmbeddedResolution.isMonomialSplitting_monomialPart_nonMonomialPart T.boundary T.ideal ⟨(M, N), h⟩

theorem nonMonomialPart_eq_of_isMonomialSplitting (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (M N : T.scheme.IdealSheafData) (h : IsMonomialSplitting T.boundary T.ideal M N) :
    nonMonomialPart T.boundary T.ideal = N :=
  (hG.splitting_unique T hT _ _ M N (hG.isMonomialSplitting_monomialPart_nonMonomialPart T hT) h).2

theorem nonMonomialPart_eq_ideal_of_boundary_eq_nil (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (hE : T.boundary = []) :
    nonMonomialPart T.boundary T.ideal = T.ideal := by
  have h : IsMonomialSplitting T.boundary T.ideal ⊤ T.ideal := by
    rw [hE]
    exact isMonomialSplitting_nil T.ideal
  exact nonMonomialPart_eq_of_isMonomialSplitting hG T hT ⊤ T.ideal h

theorem nonMonomialPart_eq_of_sameNontrivialBoundary (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (E' : List T.scheme.IdealSheafData) (hE : MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E')
    (hT' : (T.withBoundary E').IsAdmissible) :
    nonMonomialPart E' T.ideal = nonMonomialPart T.boundary T.ideal := by
  have h0 : IsMonomialSplitting E' T.ideal (monomialPart E' T.ideal)
      (nonMonomialPart E' T.ideal) :=
    hG.isMonomialSplitting_monomialPart_nonMonomialPart (T.withBoundary E') hT'
  have h1 : IsMonomialSplitting T.boundary T.ideal (monomialPart E' T.ideal)
      (nonMonomialPart E' T.ideal) :=
    (isMonomialSplitting_congr hE T.ideal (monomialPart E' T.ideal)
      (nonMonomialPart E' T.ideal)).mpr h0
  exact (nonMonomialPart_eq_of_isMonomialSplitting hG T hT _ _ h1).symm

theorem nonMonomialPart_comap_of_sameNontrivialBoundary (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] (hq : h ≫ T.structMap = q)
    (hT' : (T.pullbackAlong Y q h).IsAdmissible) (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (hT'' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible) :
    nonMonomialPart E' (T.ideal.comap h) = (nonMonomialPart T.boundary T.ideal).comap h := by
  have h0 : IsMonomialSplitting T.boundary T.ideal (monomialPart T.boundary T.ideal)
      (nonMonomialPart T.boundary T.ideal) :=
    hG.isMonomialSplitting_monomialPart_nonMonomialPart T hT
  have h1 : IsMonomialSplitting (T.pullbackAlong Y q h).boundary (T.pullbackAlong Y q h).ideal
      ((monomialPart T.boundary T.ideal).comap h)
      ((nonMonomialPart T.boundary T.ideal).comap h) :=
    hG.splitting_smooth_pullback T hT Y q h hq hT'
      (monomialPart T.boundary T.ideal) (nonMonomialPart T.boundary T.ideal) h0
  have h2 : nonMonomialPart (T.pullbackAlong Y q h).boundary (T.pullbackAlong Y q h).ideal
      = (nonMonomialPart T.boundary T.ideal).comap h :=
    nonMonomialPart_eq_of_isMonomialSplitting hG (T.pullbackAlong Y q h) hT'
      ((monomialPart T.boundary T.ideal).comap h)
      ((nonMonomialPart T.boundary T.ideal).comap h) h1
  have h3 : nonMonomialPart E' (T.ideal.comap h)
      = nonMonomialPart (T.pullbackAlong Y q h).boundary (T.pullbackAlong Y q h).ideal :=
    nonMonomialPart_eq_of_sameNontrivialBoundary hG (T.pullbackAlong Y q h) hT' E' hE hT''
  exact h3.trans h2

end PrincipalizationGeometryHypotheses

end FunctorialResolution.EmbeddedResolution

end
