import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {U : X.Opens} {m : ℕ}
  {c : EtaleChart p U m} {S : Finset (Fin m)} {s : Fin m}

theorem coord_mem_ideal_of_mem (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (i : Fin m) (hi : i ∈ S) :
    c.coord i ∈ Z.ideal ⟨U, hU⟩ := by
  rw [EtaleChart.ideal_eq_span_coord c hU Z S hZ]
  exact Ideal.subset_span (Set.mem_image_of_mem c.coord (Finset.mem_coe.mpr hi))

theorem mk_coord_eq_zero_of_mem (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (i : Fin m) (hi : i ∈ S) :
    (Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) (c.coord i) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact coord_mem_ideal_of_mem hU Z hZ i hi

theorem isAffineOpen_domain_of_isPullback (hU : IsAffineOpen U) (B : BlowupChart π c S s)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    IsAffineOpen B.domain := by
  have hUaff : IsAffine U.toScheme := hU
  have hA : IsAffine (affineSpaceFin k m) := inferInstance
  have hP : IsAffine (Limits.pullback (coordBlowupSubstMap k m S s) c.map) := inferInstance
  exact IsAffine.of_isIso hB.isoPullback.hom

private theorem quotientMk_comp_appLE_eq_zero_of_mem (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) :
    ∀ a ∈ Z.ideal ⟨U, hU⟩,
      ((Ideal.Quotient.mk (Ideal.span {B.chart.coord s})).comp
          (π.appLE U B.domain B.domain_le).hom) a = 0 := by
  have key : Ideal.span (c.coord '' (S : Set (Fin m))) ≤
      Ideal.comap (π.appLE U B.domain B.domain_le).hom
        (Ideal.span {B.chart.coord s}) := by
    rw [Ideal.span_le]
    rintro x ⟨i, hi, rfl⟩
    have hmem : (π.appLE U B.domain B.domain_le).hom (c.coord i) ∈
        Ideal.span {B.chart.coord s} := by
      by_cases his : i = s
      · subst his
        rw [BlowupChart.appLE_coord_self B]
        exact Ideal.mem_span_singleton_self _
      · rw [BlowupChart.appLE_coord_of_mem B i (Finset.mem_coe.mp hi) his]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    exact hmem
  intro a ha
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  rw [EtaleChart.ideal_eq_span_coord c hU Z S hZ] at ha
  exact Ideal.mem_comap.mp (key ha)

def exceptionalQuotientBaseHom (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (_hs : s ∈ S) :
    (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) →+* (Γ(X₁, B.domain) ⧸ Ideal.span {B.chart.coord s}) :=
  Ideal.Quotient.lift (Z.ideal ⟨U, hU⟩)
    ((Ideal.Quotient.mk (Ideal.span {B.chart.coord s})).comp
      (π.appLE U B.domain B.domain_le).hom)
    (quotientMk_comp_appLE_eq_zero_of_mem hU Z hZ B)

theorem exceptionalQuotientBaseHom_mk (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (a : Γ(X, U)) :
    exceptionalQuotientBaseHom hU Z hZ B hs ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) a) =
      (Ideal.Quotient.mk (Ideal.span {B.chart.coord s}))
        ((π.appLE U B.domain B.domain_le).hom a) :=
  rfl

def mvPolynomialToExceptionalQuotient (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S) :
    MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) →+*
      (Γ(X₁, B.domain) ⧸ Ideal.span {B.chart.coord s}) :=
  MvPolynomial.eval₂Hom (exceptionalQuotientBaseHom hU Z hZ B hs)
    (fun t => (Ideal.Quotient.mk (Ideal.span {B.chart.coord s})) (B.chart.coord t.1))

theorem mvPolynomialToExceptionalQuotient_C (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (r : Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :
    mvPolynomialToExceptionalQuotient hU Z hZ B hs (MvPolynomial.C r) = exceptionalQuotientBaseHom hU Z hZ B hs r :=
  MvPolynomial.eval₂Hom_C _ _ r

theorem mvPolynomialToExceptionalQuotient_X (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (t : ↥(S.erase s)) :
    mvPolynomialToExceptionalQuotient hU Z hZ B hs (MvPolynomial.X t) =
      (Ideal.Quotient.mk (Ideal.span {B.chart.coord s})) (B.chart.coord t.1) :=
  MvPolynomial.eval₂Hom_X' _ _ t

private def exceptionalVar (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (cc : EtaleChart p U m) (SS : Finset (Fin m)) (ss : Fin m) (j : Fin m) :
    MvPolynomial ↥(SS.erase ss) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  if h : j ∈ SS.erase ss then MvPolynomial.X ⟨j, h⟩
  else MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) (cc.coord j))

private theorem exceptionalVar_of_mem (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (cc : EtaleChart p U m) (SS : Finset (Fin m)) (ss : Fin m) (j : Fin m)
    (h : j ∈ SS.erase ss) :
    exceptionalVar hU Z cc SS ss j = MvPolynomial.X ⟨j, h⟩ :=
  dif_pos h

private theorem exceptionalVar_of_not_mem (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (cc : EtaleChart p U m) (SS : Finset (Fin m)) (ss : Fin m) (j : Fin m)
    (h : j ∉ SS.erase ss) :
    exceptionalVar hU Z cc SS ss j =
      MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) (cc.coord j)) :=
  dif_neg h

private def exceptionalEvalHom (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (cc : EtaleChart p U m) (SS : Finset (Fin m)) (ss : Fin m) :
    MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) →+*
      MvPolynomial ↥(SS.erase ss) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) →+*
        MvPolynomial ↥(SS.erase ss) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩)).comp
      (Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)))
    (fun i => exceptionalVar hU Z cc SS ss i.down)

private theorem exceptionalEval_C (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (cc : EtaleChart p U m) (SS : Finset (Fin m)) (ss : Fin m) (a : Γ(X, U)) :
    exceptionalEvalHom hU Z cc SS ss (MvPolynomial.C a) =
      MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) a) :=
  MvPolynomial.eval₂Hom_C _ _ a

private theorem exceptionalEval_X (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (cc : EtaleChart p U m) (SS : Finset (Fin m)) (ss : Fin m) (j : Fin m) :
    exceptionalEvalHom hU Z cc SS ss (MvPolynomial.X (ULift.up j)) = exceptionalVar hU Z cc SS ss j :=
  MvPolynomial.eval₂Hom_X' _ _ (ULift.up j)

private theorem exceptionalEval_coordRelation (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (i : Fin m) :
    exceptionalEvalHom hU Z c S s (B.coordRelation i) = 0 := by
  have hpr : B.coordRelation i =
      (if i ∈ S ∧ i ≠ s then
          MvPolynomial.X (ULift.up i) * MvPolynomial.X (ULift.up s)
        else MvPolynomial.X (ULift.up i)) - MvPolynomial.C (c.coord i) := rfl
  have hsnot : s ∉ S.erase s := fun hc => (Finset.mem_erase.mp hc).1 rfl
  rw [hpr]
  by_cases h : i ∈ S ∧ i ≠ s
  · rw [if_pos h, map_sub, map_mul, exceptionalEval_X, exceptionalEval_X, exceptionalEval_C,
      exceptionalVar_of_not_mem hU Z c S s s hsnot,
      mk_coord_eq_zero_of_mem hU Z hZ s hs, mk_coord_eq_zero_of_mem hU Z hZ i h.1, map_zero,
      mul_zero, sub_zero]
  · have hnot : i ∉ S.erase s := fun hc =>
      h ⟨(Finset.mem_erase.mp hc).2, (Finset.mem_erase.mp hc).1⟩
    rw [if_neg h, map_sub, exceptionalEval_X, exceptionalEval_C,
      exceptionalVar_of_not_mem hU Z c S s i hnot, sub_self]

private theorem exceptionalEval_eq_zero_of_mem_span_coordRelation (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S) :
    ∀ a ∈ Ideal.span (Set.range B.coordRelation), exceptionalEvalHom hU Z c S s a = 0 := by
  have hsub : Ideal.span (Set.range B.coordRelation) ≤ RingHom.ker (exceptionalEvalHom hU Z c S s) := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    exact exceptionalEval_coordRelation hU Z hZ B hs i
  intro a ha
  exact RingHom.mem_ker.mp (hsub ha)

private def exceptionalHomOfChart (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    Γ(X₁, B.domain) →+* MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  (Ideal.Quotient.lift (Ideal.span (Set.range B.coordRelation)) (exceptionalEvalHom hU Z c S s)
      (exceptionalEval_eq_zero_of_mem_span_coordRelation hU Z hZ B hs)).comp
    (RingEquiv.ofBijective B.coordEvalQuotientHom (B.bijective_coordEvalQuotientHom hU hB)).symm.toRingHom

private theorem exceptionalHomOfChart_coordEvalHom (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)
    (f : MvPolynomial (ULift.{u} (Fin m)) Γ(X, U)) :
    exceptionalHomOfChart hU Z hZ B hs hB (B.coordEvalHom f) = exceptionalEvalHom hU Z c S s f := by
  have h1 : (RingEquiv.ofBijective B.coordEvalQuotientHom (B.bijective_coordEvalQuotientHom hU hB)).symm
      (B.coordEvalHom f) = (Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))) f := by
    apply (RingEquiv.ofBijective B.coordEvalQuotientHom (B.bijective_coordEvalQuotientHom hU hB)).injective
    rw [RingEquiv.apply_symm_apply]
    exact (BlowupChart.coordEvalQuotientHom_mk B f).symm
  have h2 : exceptionalHomOfChart hU Z hZ B hs hB (B.coordEvalHom f)
      = (Ideal.Quotient.lift (Ideal.span (Set.range B.coordRelation)) (exceptionalEvalHom hU Z c S s)
          (exceptionalEval_eq_zero_of_mem_span_coordRelation hU Z hZ B hs))
          ((RingEquiv.ofBijective B.coordEvalQuotientHom (B.bijective_coordEvalQuotientHom hU hB)).symm
            (B.coordEvalHom f)) := rfl
  simp only [h2, h1, Ideal.Quotient.lift_mk]

private theorem exceptionalHomOfChart_coord (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)
    (i : Fin m) :
    exceptionalHomOfChart hU Z hZ B hs hB (B.chart.coord i) = exceptionalVar hU Z c S s i := by
  rw [← BlowupChart.coordEvalHom_X B i, exceptionalHomOfChart_coordEvalHom, exceptionalEval_X]

private theorem exceptionalHomOfChart_coord_self (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    exceptionalHomOfChart hU Z hZ B hs hB (B.chart.coord s) = 0 := by
  rw [exceptionalHomOfChart_coord hU Z hZ B hs hB s,
    exceptionalVar_of_not_mem hU Z c S s s (fun hc => (Finset.mem_erase.mp hc).1 rfl),
    mk_coord_eq_zero_of_mem hU Z hZ s hs, map_zero]

private def exceptionalHomOfQuotientCoord (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    (Γ(X₁, B.domain) ⧸ Ideal.span {B.chart.coord s}) →+*
      MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  Ideal.Quotient.lift (Ideal.span {B.chart.coord s}) (exceptionalHomOfChart hU Z hZ B hs hB)
    (by
      intro a ha
      obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, exceptionalHomOfChart_coord_self hU Z hZ B hs hB, mul_zero])

private theorem exceptionalHomOfQuotientCoord_mk (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)
    (a : Γ(X₁, B.domain)) :
    exceptionalHomOfQuotientCoord hU Z hZ B hs hB ((Ideal.Quotient.mk (Ideal.span {B.chart.coord s})) a)
      = exceptionalHomOfChart hU Z hZ B hs hB a :=
  rfl

theorem bijective_mvPolynomialToExceptionalQuotient (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    Function.Bijective (mvPolynomialToExceptionalQuotient hU Z hZ B hs) := by
  have hcomp : (mvPolynomialToExceptionalQuotient hU Z hZ B hs).comp (exceptionalEvalHom hU Z c S s)
      = (Ideal.Quotient.mk (Ideal.span {B.chart.coord s})).comp B.coordEvalHom := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro a
      simp only [RingHom.comp_apply]
      rw [exceptionalEval_C, BlowupChart.coordEvalHom_C B a, mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk]
    · rintro ⟨i⟩
      simp only [RingHom.comp_apply]
      rw [exceptionalEval_X, BlowupChart.coordEvalHom_X B i]
      by_cases h : i ∈ S.erase s
      · rw [exceptionalVar_of_mem hU Z c S s i h, mvPolynomialToExceptionalQuotient_X]
      · have hEq : (π.appLE U B.domain B.domain_le).hom (c.coord i) = B.chart.coord i := by
          by_cases his : i = s
          · subst his
            exact BlowupChart.appLE_coord_self B
          · exact BlowupChart.appLE_coord_of_not_mem B i
              (fun hi => h (Finset.mem_erase.mpr ⟨his, hi⟩))
        rw [exceptionalVar_of_not_mem hU Z c S s i h, mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk, hEq]
  constructor
  · have hleft : (exceptionalHomOfQuotientCoord hU Z hZ B hs hB).comp (mvPolynomialToExceptionalQuotient hU Z hZ B hs)
        = RingHom.id (MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩)) := by
      refine MvPolynomial.ringHom_ext ?_ ?_
      · intro r
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk, exceptionalHomOfQuotientCoord_mk, ← BlowupChart.coordEvalHom_C B a,
          exceptionalHomOfChart_coordEvalHom, exceptionalEval_C]
      · intro t
        simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [mvPolynomialToExceptionalQuotient_X, exceptionalHomOfQuotientCoord_mk, exceptionalHomOfChart_coord]
        exact exceptionalVar_of_mem hU Z c S s t.1 t.2
    intro x y hxy
    have hx : exceptionalHomOfQuotientCoord hU Z hZ B hs hB ((mvPolynomialToExceptionalQuotient hU Z hZ B hs) x) = x :=
      DFunLike.congr_fun hleft x
    have hy : exceptionalHomOfQuotientCoord hU Z hZ B hs hB ((mvPolynomialToExceptionalQuotient hU Z hZ B hs) y) = y :=
      DFunLike.congr_fun hleft y
    rw [← hx, ← hy, hxy]
  · intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨f, rfl⟩ := B.surjective_coordEvalHom hU hB b
    exact ⟨exceptionalEvalHom hU Z c S s f, DFunLike.congr_fun hcomp f⟩

def exceptionalQuotientEquivMvPolynomial (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    (Γ(X₁, B.domain) ⧸ Ideal.span {B.chart.coord s}) ≃+*
      MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  (RingEquiv.ofBijective (mvPolynomialToExceptionalQuotient hU Z hZ B hs) (bijective_mvPolynomialToExceptionalQuotient hU Z hZ B hs hB)).symm

theorem exceptionalQuotientEquivMvPolynomial_symm_apply (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)
    (f : MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩)) :
    (exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB).symm f = mvPolynomialToExceptionalQuotient hU Z hZ B hs f :=
  rfl

theorem exceptionalQuotientEquivMvPolynomial_mk_appLE (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)
    (a : Γ(X, U)) :
    exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB
        ((Ideal.Quotient.mk (Ideal.span {B.chart.coord s}))
          ((π.appLE U B.domain B.domain_le).hom a)) =
      MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) a) := by
  apply (exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB).symm.injective
  rw [RingEquiv.symm_apply_apply, exceptionalQuotientEquivMvPolynomial_symm_apply, mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk]

theorem exceptionalQuotientEquivMvPolynomial_mk_coord (hU : IsAffineOpen U) (Z : X.IdealSheafData)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart π c S s) (hs : s ∈ S)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)
    (i : Fin m) (hi : i ∈ S) (his : i ≠ s) :
    exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB
        ((Ideal.Quotient.mk (Ideal.span {B.chart.coord s})) (B.chart.coord i)) =
      MvPolynomial.X ⟨i, Finset.mem_erase.mpr ⟨his, hi⟩⟩ := by
  apply (exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB).symm.injective
  rw [RingEquiv.symm_apply_apply, exceptionalQuotientEquivMvPolynomial_symm_apply]
  exact (mvPolynomialToExceptionalQuotient_X hU Z hZ B hs ⟨i, Finset.mem_erase.mpr ⟨his, hi⟩⟩).symm

theorem isAffineOpen_blowupChart_domain (hU : IsAffineOpen U) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S) (hs : s ∈ S) :
    IsAffineOpen (blowupChartOfIsBlowup π c S hπ hZ s hs).domain :=
  isAffineOpen_domain_of_isPullback hU (blowupChartOfIsBlowup π c S hπ hZ s hs)
    (isPullback_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ s hs)

def exceptionalQuotientEquivOfIsBlowup (hU : IsAffineOpen U) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S) (hs : s ∈ S) :
    (Γ(X₁, (blowupChartOfIsBlowup π c S hπ hZ s hs).domain) ⧸
        Ideal.span {(blowupChartOfIsBlowup π c S hπ hZ s hs).chart.coord s}) ≃+*
      MvPolynomial ↥(S.erase s) (Γ(X, U) ⧸ Z.ideal ⟨U, hU⟩) :=
  exceptionalQuotientEquivMvPolynomial hU Z hZ (blowupChartOfIsBlowup π c S hπ hZ s hs) hs
    (isPullback_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ s hs)

theorem exceptionalQuotientEquiv_mk_appLE (hU : IsAffineOpen U) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S) (hs : s ∈ S)
    (a : Γ(X, U)) :
    exceptionalQuotientEquivOfIsBlowup hU hπ hZ hs
        ((Ideal.Quotient.mk
            (Ideal.span {(blowupChartOfIsBlowup π c S hπ hZ s hs).chart.coord s}))
          ((π.appLE U (blowupChartOfIsBlowup π c S hπ hZ s hs).domain
            (blowupChartOfIsBlowup π c S hπ hZ s hs).domain_le).hom a)) =
      MvPolynomial.C ((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)) a) :=
  exceptionalQuotientEquivMvPolynomial_mk_appLE hU Z hZ (blowupChartOfIsBlowup π c S hπ hZ s hs) hs
    (isPullback_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ s hs) a

theorem exceptionalQuotientEquiv_mk_coord (hU : IsAffineOpen U) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S) (hs : s ∈ S)
    (i : Fin m) (hi : i ∈ S) (his : i ≠ s) :
    exceptionalQuotientEquivOfIsBlowup hU hπ hZ hs
        ((Ideal.Quotient.mk
            (Ideal.span {(blowupChartOfIsBlowup π c S hπ hZ s hs).chart.coord s}))
          ((blowupChartOfIsBlowup π c S hπ hZ s hs).chart.coord i)) =
      MvPolynomial.X ⟨i, Finset.mem_erase.mpr ⟨his, hi⟩⟩ :=
  exceptionalQuotientEquivMvPolynomial_mk_coord hU Z hZ (blowupChartOfIsBlowup π c S hπ hZ s hs) hs
    (isPullback_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ s hs) i hi his

theorem exceptionalIdeal_ideal_blowupChart_domain (hU : IsAffineOpen U)
    {Z : X.IdealSheafData} (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (hZ : restrictIdeal Z U = c.coordIdeal S) (hs : s ∈ S) :
    (Blowup.exceptionalIdeal π Z).ideal
        ⟨(blowupChartOfIsBlowup π c S hπ hZ s hs).domain,
          isAffineOpen_blowupChart_domain hU hπ hZ hs⟩ =
      Ideal.span {(blowupChartOfIsBlowup π c S hπ hZ s hs).chart.coord s} := by
  rw [EtaleChart.ideal_eq_span_coord (blowupChartOfIsBlowup π c S hπ hZ s hs).chart
      (isAffineOpen_blowupChart_domain hU hπ hZ hs) (Blowup.exceptionalIdeal π Z) {s}
      (BlowupChart.restrictIdeal_exceptionalIdeal (blowupChartOfIsBlowup π c S hπ hZ s hs) Z hs hZ),
    Finset.coe_singleton, Set.image_singleton]

end FunctorialResolution.EmbeddedResolution

end
