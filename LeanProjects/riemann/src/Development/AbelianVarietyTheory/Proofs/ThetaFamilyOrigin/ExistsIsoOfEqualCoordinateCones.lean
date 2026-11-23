import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClosedImmersionDensePoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.IsoCone
open GlobalTheory.ZH.CrdCalc GlobalTheory.ZH.ImmSep GlobalTheory.ZH.ToImm

theorem dense_points {K : Type} [Field K] [IsAlgClosed K] {Y : Scheme.{0}} (p : Y ⟶ Sp K)
    [LocallyOfFiniteType p] :
    Dense (⋃ a : {x : Sp K ⟶ Y // x ≫ p = 𝟙 _}, Set.range a.1) := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  have hd : Dense (closedPoints Y) := by
    rw [dense_iff_closure_eq, closure_closedPoints]
  refine hd.mono fun c hc => Set.mem_iUnion.2 ⟨⟨_, pointOfClosedPoint_comp p c hc⟩,
    IsLocalRing.closedPoint K, pointOfClosedPoint_apply p c hc _⟩

theorem exists_hom {K : Type} [Field K] [IsAlgClosed K] {X Y : Scheme.{0}} [IsReduced Y] (p : X ⟶ Sp K)
    (p' : Y ⟶ Sp K) [LocallyOfFiniteType p'] {H : LB X} {H' : LB Y} {J : Type} [Fintype J] {s : J → H.Sec}
    {s' : J → H'.Sec} (hH : H.IsLB) (hH' : H'.IsLB) (hI : ImmBy p H s Set.univ) (hI' : ImmBy p' H' s' Set.univ)
    (hc : cone p' H' s' ⊆ cone p H s) :
    ∃ g : Y ⟶ X, g ≫ p = p' ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y) (v : J → R),
      Crd H' s' y v → Crd H s (y ≫ g) v := by
  have hx : ∀ a : {x : Sp K ⟶ Y // x ≫ p' = 𝟙 _}, ∃ x' : Sp K ⟶ X, x' ≫ p = a.1 ≫ p' ∧
      ∃ v, Crd H' s' a.1 v ∧ Crd H s x' v := by
    intro a
    obtain ⟨v, hv⟩ := crd_exists hH' s' a.1
    obtain ⟨x', h1, h2⟩ := hc ⟨a.1, a.2, hv⟩
    exact ⟨x', h1.trans a.2.symm, v, hv, h2⟩
  choose x' hx' using hx
  have hcov : ⨆ j, Out.nonzeroLocus (s' j) = ⊤ := by simpa using hI'.1
  obtain ⟨g, h1, -, h3⟩ := exists_factor K X Y p p' H H' J s s' hH hH' hI hcov K _
    (fun a : {x : Sp K ⟶ Y // x ≫ p' = 𝟙 _} => a.1) x' (dense_points p') hx'
  exact ⟨g, h1, h3⟩

theorem eq_id {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {H : LB X} {J : Type} {s : J → H.Sec}
    (hH : H.IsLB) (hI : ImmBy p H s Set.univ) (g : X ⟶ X) (hg : g ≫ p = p)
    (h : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ X) (v : J → R),
      Crd H s y v → Crd H s (y ≫ g) v) : g = 𝟙 X := by
  refine ext_local _ _ fun R _ _ y => ?_
  obtain ⟨v, hv⟩ := crd_exists hH s y
  rw [Category.comp_id]
  exact eq_of_crd_eq k X p H J s _ hH hI R _ _ v (by rw [Category.assoc, hg]) (h R y v hv) hv

theorem exists_iso : ∀ (K : Type) [Field K] [IsAlgClosed K] (X X' : Over (Sp K)) [IsIntegral X.left] [IsIntegral X'.left] [IsProper X.hom] [IsProper X'.hom] (H : LB X.left) (H' : LB X'.left) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy X.hom H s Set.univ → ImmBy X'.hom H' s' Set.univ → cone X.hom H s = cone X'.hom H' s' → ∃ φ : X ≅ X', ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ X.left) (v : J → R), Crd H s y v → Crd H' s' (y ≫ φ.hom.left) v := by
  intro K _ _ X X' _ _ _ _ H H' J _ s s' hH hH' hI hI' hc
  obtain ⟨g, h1, h2⟩ := exists_hom X'.hom X.hom hH' hH hI' hI hc.le
  obtain ⟨g', h1', h2'⟩ := exists_hom X.hom X'.hom hH hH' hI hI' hc.ge
  have e : g ≫ g' = 𝟙 _ := eq_id X.hom hH hI _ (by rw [Category.assoc, h1', h1]) fun R _ _ y v hv => by
    rw [← Category.assoc]
    exact h2' R _ v (h2 R y v hv)
  have e' : g' ≫ g = 𝟙 _ := eq_id X'.hom hH' hI' _ (by rw [Category.assoc, h1, h1']) fun R _ _ y v hv => by
    rw [← Category.assoc]
    exact h2 R _ v (h2' R y v hv)
  exact ⟨Over.isoMk ⟨g, g', e, e'⟩ h1, h2⟩

end GlobalTheory.ZH.IsoCone
end
