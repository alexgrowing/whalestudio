import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOnRescale
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.DivIso

theorem exists_isPullDeg_id : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ k, s k ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' iw s ε e' → ∃ hD : IsPullDeg (RingHom.id V) Q Q', (∀ y, e (hD.xe y) = e' y) ∧ (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (oQ.onB.act x)) := by
  intro E _ _ _ H D' l c L V _ _ _ Q _ oQ Q' _ oQ' iw I _ s ε e e' hs ⟨g, p, hg, hx, ha⟩ ⟨g', p', hg', hx', ha'⟩
  letI := H.starRing
  obtain ⟨q, q₁, q₂⟩ := GlobalTheory.PullDegTop.main.2.2.2 (RingHom.id_comp iw) p p' (fun y => L.gen (l.M' • y))
  have he : ∀ y : Q'.X, e (q.xe y) = e' y := fun y => (hx _).symm.trans ((q₂ y).trans (hx' y))
  obtain ⟨r, r₁, r₂⟩ := GlobalTheory.PullDegResc.main.2.1 g g' q s hs (fun y k => (l.M' : ℤ) * ε k (e y) (H.w0 • e y)) hg
    (fun x => (hg' x).trans (Finset.prod_congr rfl fun k _ => by rw [← he x]; rfl))
  refine ⟨r, fun y => (congrArg e (r₂ y)).trans (he y), fun x => (GlobalTheory.PullDegTop.main.2.1 r _ _).2 ?_⟩
  have r' : (r.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf (RingHom.id V))) ≫
      p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) = p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) :=
    (congrArg (· ≫ _) r₁).trans q₁
  have pb : IsPullback (p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) Q.P.A.hom L.D.P.A.hom (spMap iw) :=
    (pull_grp p).1
  have w : (r.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf (RingHom.id V))) ≫ Q.P.A.hom =
      Q'.P.A.hom ≫ spMap (RingHom.id V) := (pull_grp r).1.w
  have b : (oQ.onB.act x).left ≫ p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      (p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left :=
    (ha x).trans (Category.assoc _ _ _).symm
  have b' : (oQ'.onB.act x).left ≫ p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      (p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left :=
    (ha' x).trans (Category.assoc _ _ _).symm
  refine pb.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) r').trans (b'.trans (Eq.symm ?_)))
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) b).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) r')))
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) w).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Over.w (oQ'.onB.act x))).trans (Eq.symm ?_))))
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w (oQ.onB.act x))).trans w)

end GlobalTheory.UCanon.DivIso
