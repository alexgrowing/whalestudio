import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValTorusPointAndTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullLinear

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusCoord

theorem map_left_fst {S T : Scheme.{0}} (f : S ⟶ T) {A B : Over T} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

theorem ext_of_iso_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {A' Z : Over S'}
    (e : A' ≅ (Over.pullback f).obj A) {a b : Z ⟶ A'}
    (h : a.left ≫ e.hom.left ≫ pullback.fst A.hom f = b.left ≫ e.hom.left ≫ pullback.fst A.hom f) :
    a = b := by
  rw [← cancel_mono e.hom]
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · simpa only [Over.comp_left, Category.assoc] using h
  · exact (Over.w (a ≫ e.hom)).trans (Over.w (b ≫ e.hom)).symm

theorem ext_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {Z : Over S'}
    {a b : Z ⟶ (Over.pullback f).obj A}
    (h : a.left ≫ pullback.fst A.hom f = b.left ≫ pullback.fst A.hom f) : a = b :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w a).trans (Over.w b).symm))

theorem act_proj {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {A' : Over S'}
    (e : A' ⟶ (Over.pullback f).obj A) {u : A ⟶ A} {u' : A' ⟶ A'}
    (h : u' ≫ e = e ≫ (Over.pullback f).map u) :
    u'.left ≫ e.left ≫ pullback.fst A.hom f = (e.left ≫ pullback.fst A.hom f) ≫ u.left := by
  have h1 : u'.left ≫ e.left = e.left ≫ ((Over.pullback f).map u).left := congrArg (·.left) h
  rw [← Category.assoc, h1, Category.assoc, map_left_fst, Category.assoc]

section One

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem pG_left : g.pG.left = g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) := rfl

theorem im_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ WeightPf.Te D I e) :
    im g (τ ≫ g.i) = 1 := by
  have := g.q_hom
  rw [← im_one g]
  refine im_congr g ?_
  rw [Category.assoc, g.isKernel.w, MonObj.one_comp, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

theorem exists_torus_of_im {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (y : Z ⟶ thickObj R I e G) (h : im g y = 1) : ∃ τ : Z ⟶ WeightPf.Te D I e, τ ≫ g.i = y := by
  have h1 : y ≫ g.q = (1 : Z ⟶ thickObj R I e G) ≫ g.q := by
    refine ext_of_pullback _ ?_
    have := congrArg (·.left) (h.trans (im_one g).symm)
    exact ((Category.assoc _ _ _).trans this).trans (Category.assoc _ _ _).symm
  obtain ⟨τ, hτ⟩ := exists_torus g y 1 h1
  exact ⟨τ, by rw [hτ, _root_.mul_one]⟩

theorem prod_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ WeightPf.Te D I e)
    (χ : D.X) {U : Type} [CommGroup U] (f : (Z.left ⟶ D.P.A.left) → U) :
    ∏ k, f ((τ ≫ g.i).left ≫ D.Oφ g.pG χ k) ^ Oinvε k = 1 := by
  have e0 : ∀ k, (τ ≫ g.i).left ≫ D.Oφ g.pG χ k = D.Oφ (im g (τ ≫ g.i)) χ k := fun k =>
    WeightPf.Oφ_comp ((Over.map (thick R I e)).map (τ ≫ g.i)) g.pG χ k
  simp only [e0]
  rw [Fin.prod_univ_four, im_torus]
  change f ((1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A) * cPt Z χ).left ^ (-1 : ℤ) *
    f (cPt Z χ).left ^ (1 : ℤ) * f (1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A).left ^ (1 : ℤ) *
    f (1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A).left ^ (-1 : ℤ) = 1
  rw [_root_.one_mul, zpow_neg_one, zpow_neg_one, zpow_one, zpow_one, inv_mul_cancel, _root_.one_mul,
    mul_inv_cancel]

theorem torusEndOf_iff {S : Scheme.{0}} (X : Type) [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) :
    TorusEndOf X h t ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X),
      gm (r ≫ t.left) z ⊤ (charUnit S X χ) = gm r z ⊤ (charUnit S X (h χ)) := by
  constructor
  · intro H Z r z χ
    rw [← H χ]
    exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm
  · intro H χ
    refine unit_ext fun z _ => ?_
    rw [← H]
    exact (gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)

end One

section Two

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
  {I' : Ideal R'} {D : DegPre R} {D' : DegPre R'} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  (g : GtCoord I D e G) (g' : GtCoord I' D' e G') {F : D'.P.A.left ⟶ D.P.A.left}
  {h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left}

theorem char_eq (w : LB.Iso D'.P.L (D.P.L.pull F)) {x' : D'.X} {x : D.X}
    (hψ : ∀ κ : Fin 4, D'.Oφ g'.pG x' κ ≫ F = h ≫ D.Oφ g.pG x κ)
    (hm : PMaps w (D'.Oφ g'.pG x') (D.Oφ g.pG x) Oinvε (g'.t x') (g.t x) h)
    {Z' : Over (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))))}
    {s : Z'.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))}
    (τ' : Z' ⟶ WeightPf.Te D' I' e) (τ : Over.mk s ⟶ WeightPf.Te D I e)
    (hτ : (τ ≫ g.i).left = (τ' ≫ g'.i).left ≫ h) (z : Z'.left) :
    gm (Y := Z'.left) τ.left z ⊤ (charUnit _ D.X x) = gm τ'.left z ⊤ (charUnit _ D'.X x') := by
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.P.L D.P.isLB z
  obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB z
  have h₁ := (val_torus_point_and_translate R I D e G g (Over.mk s) τ 1 z J hJ x).1
  have h₂ := (val_torus_point_and_translate R' I' D' e G' g' Z' τ' 1 z J' hJ' x').1
  have h₃ := hm Z'.left (τ' ≫ g'.i).left z
    (fun k => J (((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k) ≫ F))
    (fun k => J' ((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k))
    (fun k => hJ (((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k) ≫ F))
    (fun k => hJ' ((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k))
  rw [prod_torus g' τ' x' (fun ψ => gw w ψ z (J (ψ ≫ F)) (J' ψ)), _root_.one_mul] at h₃
  refine h₁.symm.trans (Eq.trans ?_ (h₃.trans h₂))
  rw [hτ]
  exact val_of (g.t x) ((τ' ≫ g'.i).left ≫ h) z J _ (fun k => by
    rw [Category.assoc, Category.assoc, hψ k])

theorem exists_point {x' : D'.X} {x : D.X} (hp : g'.pG.left ≫ F = h ≫ g.pG.left)
    (hψ : ∀ κ : Fin 4, D'.Oφ g'.pG x' κ ≫ F = h ≫ D.Oφ g.pG x κ)
    {Z' : Over (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))))} (τ' : Z' ⟶ WeightPf.Te D' I' e) :
    ∃ (s : Z'.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (τ : Over.mk s ⟶ WeightPf.Te D I e),
      (τ ≫ g.i).left = (τ' ≫ g'.i).left ≫ h := by
  let y : Over.mk (((τ' ≫ g'.i).left ≫ h) ≫ (thickObj R I e G).hom) ⟶ thickObj R I e G :=
    Over.homMk ((τ' ≫ g'.i).left ≫ h) rfl
  have h1 : (τ' ≫ g'.i).left ≫ g'.pG.left = (τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' 3 := by
    refine (congrArg (·.left) (im_torus g' τ')).trans ?_
    exact (WeightPf.Oφ_comp ((Over.map (thick R' I' e)).map (τ' ≫ g'.i)) g'.pG x' 3).symm
  have h2 : im g y = 1 := by
    refine Over.OverMorphism.ext ?_
    refine Eq.trans ?_ (WeightPf.Oφ_comp ((Over.map (thick R I e)).map y) g.pG x 3)
    change ((τ' ≫ g'.i).left ≫ h) ≫ g.pG.left = ((τ' ≫ g'.i).left ≫ h) ≫ D.Oφ g.pG x 3
    rw [Category.assoc, Category.assoc, ← hp, ← hψ, ← Category.assoc, h1, Category.assoc]
  obtain ⟨τ, hτ⟩ := exists_torus_of_im g y h2
  exact ⟨_, τ, congrArg (·.left) hτ⟩

end Two

theorem oLinear_of_isPullUnif : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → (∀ a, (ιG'.act a) ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf φ)).map (ιG.act a)) → (∀ a, (Over.pullback (jK R')).map (ιG'.act a) ≫ U'.gen.hom = U'.gen.hom ≫ ιA'.act a) → (∀ (a : O) (y : D'.toPre.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) → U'.OLinear O ιD' ιA' ιG' := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ U U' hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    hlin hG hgen hx hB
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  choose h hf hpt _hw using H
  have hact : ∀ (e : ℕ) (a : O), ((Over.pullback (thick R' I' e)).map (ιG'.act a)).left ≫ h e =
      h e ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left := by
    intro e a
    have hf' : h e ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ) := hf e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G.hom (thick R I e)), Category.assoc, Category.assoc, map_left_fst,
      ← Category.assoc (h e), hf', ← Category.assoc, map_left_fst, Category.assoc,
      act_proj _ bc.hom (hG a), Category.assoc, Category.assoc, Category.assoc]
  have hq : ∀ (e : ℕ) (a : O), (Over.pullback (thick R' I' e)).map (ιG'.act a) ≫ (U'.gt e).q =
      (U'.gt e).q ≫ (Over.pullback (thick R' I' e)).map (ιD'.onB.act a) := by
    intro e a
    have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S}
        {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (g : GtCoord J E e K)
        (u : E.P.A ⟶ E.P.A), (g.q ≫ (Over.pullback (thick S J e)).map u).left ≫
          pullback.fst E.P.A.hom (thick S J e) = g.pG.left ≫ u.left := by
      intro S _ _ J E K _ _ g u
      rw [Over.comp_left, Category.assoc, map_left_fst, pG_left, Category.assoc]
    have k₁ : ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ (U.gt e).pG.left =
        (U.gt e).pG.left ≫ (ιD.onB.act a).left := by
      rw [← k, ← hlin.q_lin e a]
      exact (Category.assoc _ _ _).symm
    have k₂ : (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map (ιG'.act a)) ≫
        (U'.gt e).pG = (U'.gt e).pG ≫ ιD'.onB.act a := by
      refine ext_of_iso_pullback _ hD.e ?_
      change (((Over.pullback (thick R' I' e)).map (ιG'.act a)).left ≫ (U'.gt e).pG.left) ≫ _ =
        ((U'.gt e).pG.left ≫ (ιD'.onB.act a).left) ≫ _
      rw [Category.assoc, Category.assoc, act_proj _ hD.e.hom (hB a), (hpt e).1,
        ← Category.assoc (U'.gt e).pG.left, (hpt e).1, ← Category.assoc, hact, Category.assoc,
        Category.assoc, k₁]
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) k₂
  refine ⟨hgen, hq, fun e a => ?_⟩
  obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
  have := ιD'.onB.hom a
  have hk : ((U'.gt e).i ≫ (Over.pullback (thick R' I' e)).map (ιG'.act a)) ≫ (U'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U'.gt e).isKernel.lift_fst _ _ hk
  generalize (U'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U.gt e) (U'.gt e) (hpt e).1 ((hpt e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U.gt e).i).left = (t' ≫ (U'.gt e).i).left ≫ h e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 χ).1 ((hpt e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 (star a • χ)).1 ((hpt e).2 (star a • χ)).2
    (𝟙 _) τ hτ z
  have e₃ := (torusEndOf_iff _ _ t).1 ht _ τ.left z (hD.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

end GlobalTheory.PullLinear
