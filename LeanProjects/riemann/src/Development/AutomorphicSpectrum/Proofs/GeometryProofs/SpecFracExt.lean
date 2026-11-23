import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def tanW (Y : Model Xo c β) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (w : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left)
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x) :
    Spec (CommRingCat.of (DualNumber S)) ⟶ Y.t.G.left :=
  Y.m0.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) (by
    rw [hw, Category.assoc, Small.ptF_fst]) ≫ Y.m.φ

theorem isComb_cast {V : Type} [CommRing V] {G : CategoryTheory.Over (Spec (CommRingCat.of V))} [GrpObj G] {r m : ℕ} (h : r = m)
    (v : Fin m → (epsOver V V ⟶ G)) (cf : Fin m → V) (w : epsOver V V ⟶ G) (hc : IsComb v cf w) :
    IsComb (fun i => v (Fin.cast h i)) (fun i => cf (Fin.cast h i)) w := by
  subst h
  exact hc

theorem spec_frac_ext (T : CDVR) {B : Type} [CommRing B]
    {p q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of T.Fr)}
    (h : p ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) : p = q := by
  rw [← Spec.map_preimage p, ← Spec.map_preimage q] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  congr 1
  ext1
  refine IsLocalization.ringHom_ext (nonZeroDivisors T.V) ?_
  exact congrArg CommRingCat.Hom.hom h2

theorem base_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (T : CDVR)
    (G : SAB H (Spec (CommRingCat.of T.V))) (t' : SAB H (Spec (CommRingCat.of T.Fr)))
    (m2 : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))) (v : epsOver T.V T.V ⟶ G.G)
    (u' : Spec (CommRingCat.of (DualNumber T.Fr)) ⟶ t'.G.left)
    (h : u' ≫ m2.φ = Spec.map (CommRingCat.ofHom (dualMap (algebraMap T.V T.Fr))) ≫ v.left) :
    u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap T.Fr (DualNumber T.Fr))) := by
  apply spec_frac_ext T
  have e1 := m2.cart.1.w
  rw [Category.assoc, ← e1, ← Category.assoc, h, Category.assoc, Over.w v]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
