import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.AbFibre

theorem isPullback_baseChange {S T : Scheme.{0}} (s : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback ((Over.pullback s).map f).left (pullback.fst X.hom s) (pullback.fst Y.hom s) f.left := by
  have h1 : ((Over.pullback s).map f).left ≫ pullback.snd Y.hom s = pullback.snd X.hom s := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_snd _ _ _
  have h2 : ((Over.pullback s).map f).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ f.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hX : f.left ≫ Y.hom = X.hom := Over.w f
  refine IsPullback.of_right ?_ h2 (IsPullback.of_hasPullback Y.hom s).flip
  rw [h1, hX]
  exact (IsPullback.of_hasPullback X.hom s).flip

theorem exists_geometric_point {S : Scheme.{0}} (Y : Over S) (y : Y.left) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (s : Spec (.of Ω) ⟶ S) (w : ↥(pullback Y.hom s)),
      pullback.fst Y.hom s w = y := by
  let Ω := AlgebraicClosure (Y.left.residueField y)
  let g : Spec (.of Ω) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) Ω)) ≫ Y.left.fromSpecResidueField y
  let L : Spec (.of Ω) ⟶ pullback Y.hom (g ≫ Y.hom) := pullback.lift g (𝟙 _) (by simp)
  let pt : ↥(Spec (.of Ω)) := IsLocalRing.closedPoint Ω
  refine ⟨Ω, inferInstance, inferInstance, g ≫ Y.hom, L pt, ?_⟩
  change (L ≫ pullback.fst Y.hom (g ≫ Y.hom)) pt = y
  rw [pullback.lift_fst]
  exact Scheme.fromSpecResidueField_apply y _

theorem finiteOfFibres : PositivityTheory.Tls2.Zar3.Ch1.FiniteOfFibres := by
  intro R _ A B _ _ l hA hB _ hfib
  haveI := hA
  haveI := hB
  have hcomp : l.left ≫ B.hom = A.hom := Over.w l
  haveI : IsProper A.hom := IsAbelianScheme.proper (A := A)
  haveI : IsProper B.hom := IsAbelianScheme.proper (A := B)
  haveI : IsProper (l.left ≫ B.hom) := by rw [hcomp]; infer_instance
  haveI : IsProper l.left := IsProper.of_comp l.left B.hom
  have lift : ∀ {T : Scheme.{0}} (s : T ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (x : ↥A.left)
      (w : ↥(pullback B.hom s)), pullback.fst B.hom s w = l.left x →
      ∃ v, ((Over.pullback s).map l).left v = w ∧ pullback.fst A.hom s v = x := by
    intro T s x w hxw
    have h := isPullback_baseChange s l
    obtain ⟨z, hz1, hz2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := pullback.fst B.hom s) (g := l.left) w x hxw
    refine ⟨h.isoPullback.inv z, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
    · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]
  have hfin : ∀ y : ↥B.left, (l.left ⁻¹' {y}).Finite := by
    intro y
    obtain ⟨Ω, _, _, s, w, hw⟩ := exists_geometric_point B y
    have hF : IsFinite ((Over.pullback s).map l).left := (hfib Ω s).1
    refine ((Scheme.Hom.finite_preimage_singleton ((Over.pullback s).map l).left w).image
      (pullback.fst A.hom s)).subset ?_
    intro x hx
    have hx' : l.left x = y := hx
    obtain ⟨v, hv1, hv2⟩ := lift s x w (by rw [hw, hx'])
    exact ⟨v, hv1, hv2⟩
  have hsurj : Surjective l.left := by
    refine ⟨fun y => ?_⟩
    obtain ⟨Ω, _, _, s, w, hw⟩ := exists_geometric_point B y
    have hS : Surjective ((Over.pullback s).map l).left := (hfib Ω s).2
    obtain ⟨v, hv⟩ := hS.surj w
    refine ⟨pullback.fst A.hom s v, ?_⟩
    have hsq := (isPullback_baseChange s l).w
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply, hv, hw]
  haveI : LocallyQuasiFinite l.left := LocallyQuasiFinite.of_finite_preimage_singleton l.left hfin
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite l.left, hsurj⟩

end GlobalTheory.CompanionTheory.AbFibre
