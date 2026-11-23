import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

namespace GlobalTheory.CompanionTheory.Ar.TupleCoords

private theorem valR_eq_valMap {A : Type} [CommRing A] {X : Scheme} (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ (TopologicalSpace.Opens.map x.base).obj U) (f : X.presheaf.obj (op U)) :
    valR x U f = (GlobalTheory.Points.valMap x U h).hom f := by
  simp only [valR, dif_pos h, GlobalTheory.Points.valMap, CommRingCat.hom_comp, RingHom.comp_apply]

theorem exists_tuple_eq_point : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (r : ℕ) (p : Sp Ω ⟶ PSpace ℚ r),
    ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' := by
  intro Ω _ _ r p
  let y0 : Sp Ω := (default : PrimeSpectrum Ω)
  obtain ⟨i, hi0⟩ := GlobalTheory.ProjSpace.exists_mem_chart ℚ r (p.base y0)
  have hi : ⊤ ≤ (TopologicalSpace.Opens.map p.base).obj (GlobalTheory.ProjSpace.chart ℚ r i) := by
    intro y _
    have hy : y = y0 := Subsingleton.elim (α := PrimeSpectrum Ω) y y0
    subst hy
    exact hi0
  set t : Fin (r + 1) → Ω := fun j => valR p (GlobalTheory.ProjSpace.chart ℚ r i) (GlobalTheory.ProjSpace.ratio ℚ r i j)
    with ht_def
  have hti : t i = 1 := by
    simp only [ht_def, valR_eq_valMap p _ hi]
    rw [show GlobalTheory.ProjSpace.ratio ℚ r i i = 1 from GlobalTheory.ProjSpace.ratioOn_self]
    exact map_one _
  have hti0 : t i ≠ 0 := by rw [hti]; exact one_ne_zero
  have htne : t ≠ 0 := fun h => hti0 (congr_fun h i)
  refine ⟨t, htne, ?_⟩
  have hq : ⊤ ≤ (TopologicalSpace.Opens.map (point ℚ t htne).base).obj (GlobalTheory.ProjSpace.chart ℚ r i) :=
    (GlobalTheory.TuplePoint.le_point_preimage_iff i).2 hti0
  refine GlobalTheory.Points.ext_of_valR (GlobalTheory.ProjSpace.isAffineOpen_chart ℚ r i) hi hq ?_
  intro f
  obtain ⟨P, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℚ r i f
  rw [valR_eq_valMap p _ hi, valR_eq_valMap _ _ hq]
  have key : (GlobalTheory.Points.valMap p _ hi).hom.comp (MvPolynomial.aeval (R := ℚ) (GlobalTheory.ProjSpace.ratio ℚ r i)).toRingHom
      = (GlobalTheory.Points.valMap (point ℚ t htne) _ hq).hom.comp
          (MvPolynomial.aeval (R := ℚ) (GlobalTheory.ProjSpace.ratio ℚ r i)).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
    intro j
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
    rw [← valR_eq_valMap p _ hi, ← valR_eq_valMap _ _ hq,
      GlobalTheory.TuplePoint.valR_point_ratio hti0 j, hti, div_one]
  exact RingHom.congr_fun key P

end GlobalTheory.CompanionTheory.Ar.TupleCoords
