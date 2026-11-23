import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem ellPull_exists_oAct {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {g : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f g) {O : Type} [CommRing O] (o : OAct O G) :
    ∃ o' : OAct O G', ∀ a, (o'.act a).left ≫ g = g ≫ (o.act a).left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : O → (G' ⟶ G') := fun a => Over.homMk (hg.1.lift (g ≫ (o.act a).left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ g = g ≫ (o.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G') a, pushPt hg.1.w (x ≫ act a) = pushPt hg.1.w x ≫ o.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨⟨act, fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a b => inj ?_, fun a b => inj ?_⟩, ha⟩
  · have := o.hom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act 1), pa, o.one, Category.comp_id]
  · rw [← Category.id_comp (act (a * b)), pa, pa, ← Category.id_comp (act a), pa, o.mul, Category.assoc]
  · refine Eq.trans ?_ (pm (act a) (act b)).symm
    rw [← Category.id_comp (act (a + b)), ← Category.id_comp (act a), ← Category.id_comp (act b), pa, pa, pa, o.add]
    exact MonObj.comp_mul _ _ _

theorem ellPull_prim {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {g : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f g) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (i : LBIso (L.pull g) L') {w : G ⟶ G} {w' : G' ⟶ G'} (hw : w'.left ≫ g = g ≫ w.left)
    (h : LBIso L (cubeLB G ![𝟙 G, w] L)) : LBIso L' (cubeLB G' ![𝟙 G', w'] L') := by
  let U : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk g hg.1.w
  have H₁ : LBIso (L.pull g) (cubeLB G' ![𝟙 G', w'] (L.pull g)) := by
    refine LBIso.chartPull (chartPullPull L g U.left rfl)
      (chartPullLinComb L g _ _ _ U.left fun I => lamBC_psum_push hg _ _ U (fun k => ?_) I.down) h
    fin_cases k
    · refine Over.OverMorphism.ext ?_
      show 𝟙 _ ≫ g = g ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    · exact Over.OverMorphism.ext hw
  have hLg : (L.pull g).IsLB := DVR.linComb_isLB _ hL _ _
  exact LBIso.trans hL' hLg (DVR.linComb_isLB _ hL' _ _) i.symm
    (LBIso.trans hLg (DVR.linComb_isLB _ hLg _ _) (DVR.linComb_isLB _ hL' _ _) H₁
      (PowPrimitive.lbIso_linComb i _ _))

theorem exists_ellMap : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (R' : Type) [CommRing R'] (f : R →+* R'), ∃ (C' : Ell H R' (f ω)) (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ := by
  intro hB E _ _ _ H R _ ω C R' _ f
  obtain ⟨P', φ, hP⟩ := exists_isPolFibre hB f C.P
  obtain ⟨hdim, hg, hi⟩ := id hP
  obtain ⟨o', ho⟩ := ellPull_exists_oAct hg C.act
  have : IsCommMonObj P'.A := P'.isAb.comm
  have := C.P.smoothDim
  obtain ⟨v', hv', hv⟩ := exists_isLieBasis_baseChange R R' f C.P.A P'.A φ hg
    (SmoothOfRelativeDimension.smooth C.P.g C.P.A.hom) 1 ![C.v] C.basis
  have ev : ![v' 0] = v' := by
    funext i
    fin_cases i
    rfl
  have hv0 : (v' 0).left ≫ φ = spMap (Chart.dualMapR f) ≫ C.v.left := hv 0
  refine ⟨⟨P', hdim.trans C.dim, o', v' 0, ev ▸ hv', ?_, fun a b hab => ?_,
    ellPull_prim hg C.P.isLB P'.isLB hi (ho _) C.prim⟩, φ, rfl, hP, hv0, ho⟩
  · have e : (fun i => f (![ω] i)) = ![f ω] := by
      funext i
      fin_cases i
      rfl
    rw [ev, ← e]
    refine (lieComb_baseChange R R' f C.P.A P'.A φ hg 1 ![C.v] _ ![ω] v' _ hv C.eig).1 ?_
    show ((v' 0).left ≫ (o'.act (wK H)).left) ≫ φ = _ ≫ C.v.left ≫ (C.act.act (wK H)).left
    rw [Category.assoc, ho, ← Category.assoc, hv0, Category.assoc]
  · have e1 : (𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ = φ ≫ (𝟙 C.P.A : C.P.A ⟶ C.P.A).left := by
      show 𝟙 _ ≫ φ = φ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    exact lamEq_baseChange _ _ (spMap f) _ _ _ _ _ _ _ _ φ φ φ φ hg.1.w hg.1.w hg hg _ _ _ _ C.P.isLB C.P.isLB
      P'.isLB P'.isLB hi hi _ _ _ _ _ _ _ _ (ho a) e1 e1 (ho b) (C.adj a b hab)

end GlobalTheory.CM

end
