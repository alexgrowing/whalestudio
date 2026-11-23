import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartHomUniformisedGroups
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData

theorem cls_lam_proj {S : Scheme.{0}} {H : Over S} [GrpObj H] {L : LB H.left} (hL : L.IsLB) (h : (abelian₂ H L).IsLB) :
    cls (abelian₂ H L) h = lam (cls L hL) (fst H H) (snd H H) :=
  cls_cube_two hL (fst H H) (snd H H) h

theorem lbIso_iff_lam {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [GrpObj H₂] {L₁ : LB H₁.left} {L₂ : LB H₂.left}
    (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (f g : H₁ ⟶ H₂) :
    LBIso (abelian₂ H₁ L₁) ((abelian₂ H₂ L₂).pull (lift (fst H₁ H₁ ≫ f) (snd H₁ H₁ ≫ g) : G2 H₁ ⟶ G2 H₂).left) ↔
      ∀ (T : Over S) (x z : T ⟶ H₁), lam (cls L₁ h₁) x z = lam (cls L₂ h₂) (x ≫ f) (z ≫ g) := by
  have hA : (abelian₂ H₁ L₁).IsLB := LB.isLB_linComb h₁ _ _
  have hB : (abelian₂ H₂ L₂).IsLB := LB.isLB_linComb h₂ _ _
  rw [← cls_eq_iff hA (pull_isLB hB _), cls_pull hB, cls_lam_proj h₁, cls_lam_proj h₂, pull_lam, lift_fst, lift_snd]
  constructor
  · intro h T x z
    have e := congrArg (pull (lift x z).left) h
    simpa only [pull_lam, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using e
  · intro h
    exact h _ _ _

theorem lam_of_rosatiGen {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {a b : B ⟶ B} (u : LB.Gen (LB.LinComb M (rosatiφ B a b) rosatiε)) (hu : u.IsGen) {T : Over S} (x y : T ⟶ B) :
    lam (cls M hM) (x ≫ a) y = lam (cls M hM) x (y ≫ b) := by
  unfold lam
  rw [GlobalTheory.EndRosati.cls_of_rosati hM u hu x y]

end GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

set_option maxHeartbeats 1000000 in

theorem adjCls_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q r : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom q → IsMonHom r → IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → j ≫ r = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) r inc → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (jB : D₀.toPre.P.A ⟶ D.toPre.P.A), IsMonHom qB → IsMonHom jB → Over₀ U.toUnifPre U₀.toUnifPre q qB → Over₀ U₀.toUnifPre U.toUnifPre j jB → AdjCls (cls D.toPre.P.L D.toPre.P.isLB) (cls D₀.toPre.P.L D₀.toPre.P.isLB) qB jB := by
  intro R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG hG₀ U U₀ q r inc j hq hr hinc hj hiq hjr hqj hri qB jB hqB hjB hOq hOj
  obtain ⟨hAdm, hCZ⟩ := hR
  obtain ⟨incB, hincB, hOinc⟩ := exists_abelian_hom R _ hAdm D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre inc hinc
  obtain ⟨rB, hrB, hOr⟩ := exists_abelian_hom R _ hAdm D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre r hr
  have hjrB : jB ≫ rB = 𝟙 _ :=
    (over₀_onTorus_unique R _ hAdm D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre (j ≫ r)).1 _ _
      (FactorPol.over_comp hOj hOr) (by rw [hjr]; exact FactorPol.over_id)

  have h1 : ∀ (T : Over (Sp R)) (x z : T ⟶ G₀),
      lam (cls U₀.LG.L U₀.LG.isLB) x z = lam (cls U.LG.L U.LG.isLB) (x ≫ inc) (z ≫ j) := by
    intro T x z
    rw [hqj T (x ≫ inc) z, Category.assoc, hiq, Category.comp_id]
  have hI := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart R hAdm D₀ D A₀ A G₀ G hG₀ hG U₀ U inc j incB jB hinc hj hincB hjB hOinc hOj
    ((lbIso_iff_lam U₀.LG.isLB U.LG.isLB inc j).2 h1)
  have h1B := (lbIso_iff_lam D₀.toPre.P.isLB D.toPre.P.isLB incB jB).1 hI

  have hadj : ∀ (T : Over (Sp R)) (x z : T ⟶ G),
      lam (cls U.LG.L U.LG.isLB) (x ≫ q ≫ inc) z = lam (cls U.LG.L U.LG.isLB) x (z ≫ r ≫ j) := by
    intro T x z
    rw [lam_comm, ← Category.assoc x, hri T z (x ≫ q), lam_comm, ← hqj T x (z ≫ r), Category.assoc]
  have hiso : LBIso (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L)
      (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L) := by
    have ha : (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    have hb : (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    refine (cls_eq_iff ha hb).1 ?_
    rw [cls_cube_two U.LG.isLB _ _ ha, cls_cube_two U.LG.isLB _ _ hb]
    exact hadj _ _ _

  haveI : IsMonHom U.gen.hom := U.gen_hom
  have hext : ∀ a : G ⟶ G, (Over.pullback (jK R)).map a ≫ U.gen.hom =
      U.gen.hom ≫ (U.gen.inv ≫ (Over.pullback (jK R)).map a ≫ U.gen.hom) := fun a => by simp
  obtain ⟨E, hE, -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (q ≫ inc) _ inferInstance inferInstance (hext _)
  obtain ⟨E', hE', -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (r ≫ j) _ inferInstance inferInstance (hext _)
  have hros := (rosatiAdjoint_and_linear_of_admissibleBase R _ hAdm D A G hG U E E' (by rw [hE, hE']; exact hiso)).2.1
  have hEB : E.aB = qB ≫ incB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E.aG).1 _ _ (lin_of_endU E).1.2.2.1
      (by rw [hE]; exact FactorPol.over_comp hOq hOinc)
  have hE'B : E'.aB = rB ≫ jB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E'.aG).1 _ _ (lin_of_endU E').1.2.2.1
      (by rw [hE']; exact FactorPol.over_comp hOr hOj)
  haveI := E.homB
  haveI := E'.homB
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.firstFiveLaws.1.globalFns D.toPre.P.isAb D.toPre.P.isLB E.aB E'.aB hros
  intro T x z
  rw [h1B T (x ≫ qB) z, Category.assoc, ← hEB, lam_of_rosatiGen D.toPre.P.isLB u hu, hE'B, Category.assoc,
    reassoc_of% hjrB]

end GlobalTheory.Mum.PowData
