import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorRadical
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.GermRegularParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinatePolynomialRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.RegularLocalRing
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))

private theorem le_one_of_not_two_le {a : ℕ∞} (h : ¬ ((2 : ℕ) : ℕ∞) ≤ a) : a ≤ 1 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · exact absurd le_top h
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
    have hm : ¬ (2 ≤ m) := fun hh => h (by exact_mod_cast hh)
    have hm1 : m ≤ 1 := by omega
    exact_mod_cast hm1

theorem germ_coord_notMem_maximalIdeal_sq {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (y : X) (hy : y ∈ V)
    (hmem : c.coord j ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) :
    (X.presheaf.germ V y hy).hom (c.coord j) ∉
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ 2 := by
  classical
  let instS : Algebra (CoordPolynomialRing k n) Γ(X, V) := c.algebra
  have instEt : Algebra.Etale (CoordPolynomialRing k n) Γ(X, V) :=
    EtaleChart.algebra_etale c hV
  let instAlg : Algebra Γ(X, V) (X.presheaf.stalk y) :=
    (X.presheaf.germ V y hy).hom.toAlgebra
  have hloc : IsLocalization (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      (X.presheaf.stalk y) := hV.isLocalization_stalk ⟨y, hy⟩
  have hreg : IsRegularLocalRing (X.presheaf.stalk y) :=
    isRegularLocalRing_of_isLocalization_etale k n Γ(X, V)
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal (X.presheaf.stalk y)
  have hcoord : ∀ i : Fin n, etaleChartCoord k n Γ(X, V) i = c.coord i := fun i =>
    EtaleChart.coordRingHom_X c i
  have hJ : ∀ i ∈ ({j} : Finset (Fin n)),
      etaleChartCoord k n Γ(X, V) i ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
    intro i hi
    have hij : i = j := Finset.mem_singleton.mp hi
    rw [hij, hcoord j]
    exact hmem
  have hJA : ∀ i ∈ ({j} : Finset (Fin n)),
      algebraMap Γ(X, V) (X.presheaf.stalk y) (etaleChartCoord k n Γ(X, V) i)
        ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
    intro i hi
    have hij : i = j := Finset.mem_singleton.mp hi
    rw [hij, hcoord j]
    exact (germ_mem_maximalIdeal_iff hV y hy (c.coord j)).mpr hmem
  have hli := linearIndependent_toCotangent_etaleChartCoord k n Γ(X, V)
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal (X.presheaf.stalk y) ({j} : Finset (Fin n)) hJ hJA
  have hnot := IsRegularLocalRing.notMem_maximalIdeal_sq
    (fun i : {x : Fin n // x ∈ ({j} : Finset (Fin n))} =>
      algebraMap Γ(X, V) (X.presheaf.stalk y) (etaleChartCoord k n Γ(X, V) (i : Fin n)))
    (fun i => hJA (i : Fin n) i.2) hli ⟨j, Finset.mem_singleton_self j⟩
  intro hcon
  have h2 : algebraMap Γ(X, V) (X.presheaf.stalk y) (etaleChartCoord k n Γ(X, V) j)
      ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ 2 := by
    rw [hcoord j]
    exact hcon
  exact hnot h2

private theorem orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal S) (y : X) (hy : y ∈ V) :
    orderAt D y ≤ 1 := by
  classical
  by_cases hys : y ∈ D.support
  · have hgerm : (X.presheaf.germ V y hy).hom (c.coord j) ∈ stalkIdeal D y := by
      refine germ_mem_stalkIdeal D y ⟨V, hV⟩ hy ?_
      rw [EtaleChart.ideal_eq_span_coord c hV D S hD]
      exact Ideal.subset_span ⟨j, Finset.mem_coe.mpr hj, rfl⟩
    have hmax : stalkIdeal D y ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
      (mem_support_iff_stalkIdeal_le_maximalIdeal D y).mp hys
    have hmem : c.coord j ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal :=
      (germ_mem_maximalIdeal_iff hV y hy (c.coord j)).mp (hmax hgerm)
    refine le_one_of_not_two_le ?_
    intro h2
    rw [le_orderAt_iff] at h2
    exact germ_coord_notMem_maximalIdeal_sq p hV c j y hy hmem (h2 hgerm)
  · rw [(orderAt_eq_zero_iff_not_mem_support D y).mpr hys]
    exact zero_le_one

theorem orderAt_eq_one_of_restrictIdeal_eq_coordIdeal_singleton {V : X.Opens}
    (hV : IsAffineOpen V) {n : ℕ} (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (y : X) (hy : y ∈ V) (hys : y ∈ D.support) :
    orderAt D y = 1 :=
  le_antisymm (orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal p hV c {j} j (Finset.mem_singleton_self j) D hD y hy)
    ((one_le_orderAt_iff_mem_support D y).mpr hys)

theorem orderAt_le_one_of_restrictIdeal_eq_coordIdeal {V : X.Opens}
    (hV : IsAffineOpen V) {n : ℕ} (c : EtaleChart p V n) (S : Finset (Fin n)) (j : Fin n)
    (hj : j ∈ S) (D : X.IdealSheafData) (hD : restrictIdeal D V = c.coordIdeal S)
    (y : X) (hy : y ∈ V) :
    orderAt D y ≤ 1 :=
  orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal p hV c S j hj D hD y hy

theorem orderAt_eq_one_of_restrictIdeal_eq_coordIdeal {V : X.Opens}
    (hV : IsAffineOpen V) {n : ℕ} (c : EtaleChart p V n) (S : Finset (Fin n)) (j : Fin n)
    (hj : j ∈ S) (D : X.IdealSheafData) (hD : restrictIdeal D V = c.coordIdeal S)
    (y : X) (hy : y ∈ V) (hys : y ∈ D.support) :
    orderAt D y = 1 :=
  le_antisymm (orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal p hV c S j hj D hD y hy)
    ((one_le_orderAt_iff_mem_support D y).mpr hys)

end FunctorialResolution.EmbeddedResolution
