import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WtSecond

lemma left_eq {S : Scheme.{0}} {A B C : Over S} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C} (H : f ≫ g = h) :
    f.left ≫ g.left = h.left :=
  (Over.comp_left _ _ _ f g).symm.trans (congrArg (fun k => k.left) H)

lemma appLE_congr {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) {U : B.Opens} {W : A.Opens}
    (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ g ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W e' := by
  subst h; rfl

section Core

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def chg (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    WeightPf.Te D I e ⊗ thickObj R I e G ⟶ WeightPf.Te D' I e ⊗ thickObj R I e G :=
  lift (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ θ.inv) (snd (WeightPf.Te D I e) (thickObj R I e G))

lemma chg_fst (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ fst (WeightPf.Te D' I e) (thickObj R I e G) =
      fst (WeightPf.Te D I e) (thickObj R I e G) ≫ θ.inv :=
  lift_fst _ _

lemma chg_snd (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ snd (WeightPf.Te D' I e) (thickObj R I e G) = snd (WeightPf.Te D I e) (thickObj R I e G) :=
  lift_snd _ _

lemma chg_chg (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ chg (G := G) θ.symm = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, chg_fst, ← Category.assoc, chg_fst, Category.assoc, Iso.symm_inv, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · rw [Category.assoc, chg_snd, chg_snd, Category.id_comp]

lemma chg_act (g : GtCoord I D e G) (g' : GtCoord I D' e G) (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e)
    (hi : θ.hom ≫ g.i = g'.i) : chg θ ≫ WeightPf.act g' = WeightPf.act g := by
  have hgi : θ.inv ≫ g'.i = g.i := (Iso.inv_comp_eq θ).2 hi.symm
  have h1 : chg θ ≫ lift (fst (WeightPf.Te D' I e) (thickObj R I e G) ≫ g'.i) (snd _ _) =
      lift (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ g.i) (snd _ _) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, chg_fst, Category.assoc, hgi]
    · rw [Category.assoc, lift_snd, lift_snd, chg_snd]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ μ[thickObj R I e G]) h1)

end Core

section Weight

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma chg_weight (g : GtCoord I D e G) (g' : GtCoord I D' e G) (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e)
    (hi : θ.hom ≫ g.i = g'.i) (x₀ : D'.X → D.X)
    (hx : ∀ x, θ.hom.left.appTop.hom (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X (x₀ x)).val =
      (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.X x).val)
    (α' : D'.X) (jt : Fin 4 → D'.P.L.ι) (hjt : LB.Coh D'.P.L (D'.Oφ g'.pG α') jt)
    (W' : (WeightPf.Te D I e ⊗ thickObj R I e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt)
    (ha : W' ≤ (WeightPf.act g).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt) :
    ((WeightPf.act g).left.appLE _ W' ha).hom ((g'.t α').s jt).val =
      ((WeightPf.Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.X (thickObj R I e G) (x₀ α')) *
      ((snd (WeightPf.Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom ((g'.t α').s jt).val := by
  have hΨs : chg (G := G) θ.symm ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)) = (snd (WeightPf.Te D' I e) (thickObj R I e G)) := chg_snd θ.symm
  have hact' : chg (G := G) θ.symm ≫ WeightPf.act g = WeightPf.act g' :=
    chg_act g' g θ.symm (by rw [Iso.symm_hom, ← hi, Iso.inv_hom_id_assoc])
  have hs'' : (chg (G := G) θ.symm).left ⁻¹ᵁ W' ≤ (snd (WeightPf.Te D' I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt := by
    have h1 : (snd (WeightPf.Te D' I e) (thickObj R I e G)).left = (chg (G := G) θ.symm).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left :=
      (left_eq hΨs).symm
    rw [h1, Scheme.Hom.comp_preimage]
    exact fun y hy => hs hy
  have ha'' : (chg (G := G) θ.symm).left ⁻¹ᵁ W' ≤ (WeightPf.act g').left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt := by
    have h1 : (WeightPf.act g').left = (chg (G := G) θ.symm).left ≫ (WeightPf.act g).left :=
      (left_eq hact').symm
    rw [h1, Scheme.Hom.comp_preimage]
    exact fun y hy => ha hy
  have hΦW : W' ≤ (chg (G := G) θ).left ⁻¹ᵁ ((chg (G := G) θ.symm).left ⁻¹ᵁ W') := by
    have h2 : (chg (G := G) θ).left ≫ (chg (G := G) θ.symm).left = 𝟙 _ :=
      (left_eq (chg_chg θ)).trans (Over.id_left _)
    rw [← Scheme.Hom.comp_preimage, h2]
    exact fun y hy => hy
  have key := WeightPf.t_act g' α' jt hjt _ hs'' ha''
  have k2 := congrArg ((chg (G := G) θ).left.appLE _ W' hΦW).hom key
  have e0 : (chg (G := G) θ).left ≫ (WeightPf.act g').left = (WeightPf.act g).left :=
    left_eq (chg_act g g' θ hi)
  have e1 : (chg (G := G) θ).left ≫ (snd (WeightPf.Te D' I e) (thickObj R I e G)).left = (snd (WeightPf.Te D I e) (thickObj R I e G)).left :=
    left_eq (chg_snd θ)
  have L : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((WeightPf.act g').left.appLE _ _ ha'').hom x) =
      ((WeightPf.act g).left.appLE _ W' ha).hom x := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun φ => φ.hom x) (appLE_congr e0 _ ha)
  have S : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((snd (WeightPf.Te D' I e) (thickObj R I e G)).left.appLE _ _ hs'').hom x) =
      ((snd (WeightPf.Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom x := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun φ => φ.hom x) (appLE_congr e1 _ hs)
  have hres : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((WeightPf.Te D' I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom x) =
      ((WeightPf.Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom ((chg (G := G) θ).left.appTop.hom x) := by
    intro x
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    first | erw [Scheme.Hom.appLE_map] | rfl
  have hchi : (chg (G := G) θ).left.appTop.hom (TorusInj.chiP D'.X (thickObj R I e G) α') =
      TorusInj.chiP D.X (thickObj R I e G) (x₀ α') := by
    unfold TorusInj.chiP
    rw [← SplitTorusHom.appTop_comp, chg_fst, SplitTorusHom.appTop_comp, ← hx α',
      ← SplitTorusHom.appTop_comp θ.inv θ.hom, Iso.inv_hom_id, SplitTorusHom.appTop_id]
  rw [map_mul] at k2
  exact (L _).symm.trans (k2.trans (congrArg₂ (· * ·) ((hres _).trans (congrArg _ hchi)) (S _)))

end Weight

theorem wt_second : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (e : ℕ) (xe : D'.toPre.X ≃+ D.toPre.X), GlobalTheory.CharAgree.Match (U.gt e) (U'.gt e) xe → ∀ (α' : D'.toPre.X) (jt : Fin 4 → D'.toPre.P.L.ι), LB.Coh D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt → ∀ (W' : (WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt) (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt), ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom (((U'.gt e).t α').s jt).val = ((WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.toPre.X (thickObj R (maximalIdeal R) e G) (xe α')) * ((snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.appLE _ W' hs).hom (((U'.gt e).t α').s jt).val := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' e xe hM α' jt hjt W' hs ha
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  obtain ⟨hN, -, -, -⟩ := hR
  have hI : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  obtain ⟨θ, hθ, hi⟩ := CharAgree.exists_torus_iso hI (U.gt e) (U'.gt e)
  have := CharAgree.connected_thick hI e
  obtain ⟨x₀, hx⟩ := exists_addEquiv_of_splitTorus_iso _ D.toPre.X D'.toPre.X θ hθ

  have hM₀ : CharAgree.Match (U.gt e) (U'.gt e) x₀ := by
    intro Z r z J J' hJ hJ' _ h' x
    let FinalForm : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :=
      Over.mk (r ≫ (thickObj R (maximalIdeal R) e G).hom)
    let a : FinalForm ⟶ thickObj R (maximalIdeal R) e G := Over.homMk r rfl
    let τ := (U'.gt e).isKernel.lift a (toUnit _) ((CharAgree.comp_q_eq_one_iff (U'.gt e) a).2 h')
    have hτ : τ ≫ (U'.gt e).i = a := (U'.gt e).isKernel.lift_fst _ _ _
    have hτ' : (τ ≫ θ.hom) ≫ (U.gt e).i = a := by rw [Category.assoc, hi, hτ]
    have k := (TorusCoord.val_torus_point_and_translate R (maximalIdeal R) D.toPre e G (U.gt e) FinalForm
      (τ ≫ θ.hom) 1 z J hJ (x₀ x)).1
    have k' := (TorusCoord.val_torus_point_and_translate R (maximalIdeal R) D'.toPre e G (U'.gt e) FinalForm
      τ 1 z J' hJ' x).1
    rw [hτ'] at k
    rw [hτ] at k'
    refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
    rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
    refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
    exact (SplitTorusHom.appTop_comp τ θ.hom _).trans (congrArg τ.left.appTop.hom (hx x))
  have hxe : (xe : D'.toPre.X → D.toPre.X) = x₀ := CharAgree.match_unique hI _ _ hM hM₀
  rw [congrFun hxe α']
  exact chg_weight (U.gt e) (U'.gt e) θ hi x₀ hx α' jt hjt W' hs ha

end GlobalTheory.WtSecond
