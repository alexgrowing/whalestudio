import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPullSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.pulled_lowObj_grp_ident : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] (ev : V →+* K), ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ev) π₁ → ∃ θ : o'.t.G.left ⟶ B'.left, IsGrpPullback o'.t.G B' (𝟙 _) θ ∧ LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) ∧ (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ ev o' m₁ B' _ π₁ hπ
  obtain ⟨g, hD, -, hxe, -⟩ := hDiv
  have hsp : spMap ev ≫ specOf iw = spMap (ev.comp iw) := by
    simp [spMap, specOf, ← Spec.map_comp]
  have hii : IsGrpPullback Q.P.A L.D.P.A (specOf iw) (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    GlobalTheory.UnifPullCompare.isGrpPullback_of_bc hD.e hD.e_hom
  have h₂ : IsGrpPullback B' L.D.P.A (spMap (ev.comp iw))
      (π₁ ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    (IsGrpPullback.comp hπ hii).congr hsp rfl
  have h₁ : IsGrpPullback o'.t.G L.D.P.A (spMap (ev.comp iw)) (m₁.toSABMap.φ ≫ L.φB) :=
    (IsGrpPullback.comp m₁.cart L.ab.1).congr (Category.comp_id _) rfl
  obtain ⟨θe, hθm, hθ⟩ := grpPullback_iso h₁ h₂
  refine ⟨θe.hom.left, ?_, ?_, ?_⟩
  · haveI := hθm
    exact isGrpPullback_of_iso θe
  · have A : LBIso o'.t.PP.L (L.o.t.PP.L.pull m₁.toSABMap.φ) := GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m₁.toSABMap
    have B : LBIso (L.o.t.PP.L.pull m₁.toSABMap.φ) (L.D.P.L.pull (m₁.toSABMap.φ ≫ L.φB)) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull L.ab.2.2 _ rfl
    have C : LBIso Q.P.L (L.D.P.L.pull (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw))) :=
      ⟨hD.w, hD.w_gen⟩
    have C' : LBIso (Q.P.L.pull (θe.hom.left ≫ π₁)) (L.D.P.L.pull (m₁.toSABMap.φ ≫ L.φB)) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull C _ (by rw [← hθ]; simp only [Category.assoc])
    exact LBIso.trans o'.t.PP.isLB (pull_isLB L.D.P.isLB _) (pull_isLB Q.P.isLB _)
      (LBIso.trans o'.t.PP.isLB (pull_isLB L.o.t.PP.isLB _) (pull_isLB L.D.P.isLB _) A B) C'.symm
  · intro x a hx hc
    apply hii.1.hom_ext
    · have hcp : (Q.c a).left ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
          specOf iw ≫ (L.D.c (l.M' • e a)).left := by
        have := hD.c_pr a
        rw [hxe a] at this
        exact this
      simp only [Category.assoc]
      rw [hθ, hc, hcp, ← Category.assoc, hsp]
    · have hq : (Q.c a).left ≫ Q.P.A.hom = 𝟙 _ := Over.w (Q.c a)
      have hB : θe.hom.left ≫ B'.hom = o'.t.G.hom := Over.w θe.hom
      simp only [Category.assoc]
      rw [hπ.1.w, ← Category.assoc θe.hom.left, hB, ← Category.assoc x, hx, hq]
      simp
