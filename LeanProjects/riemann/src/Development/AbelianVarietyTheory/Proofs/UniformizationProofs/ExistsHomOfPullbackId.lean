import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfFibreConstOfSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProductUniformizationTorusIsPower

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LinearUnifIso

theorem exists_hom_of_pullback_id {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {f : S ⟶ S}
    (hf : f = 𝟙 S) (bc : G' ≅ (Over.pullback f).obj G) [IsMonHom bc.hom] :
    ∃ φ : G' ⟶ G, IsMonHom φ ∧ φ.left = bc.hom.left ≫ pullback.fst G.hom f := by
  have h₁ : IsGrpPullback G' G (𝟙 S) (bc.hom.left ≫ pullback.fst G.hom f) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G f)).congr ((Category.id_comp _).trans hf) rfl
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  obtain ⟨e, he, h⟩ := grpPullback_iso h₁ (isGrpPullback_of_iso (Iso.refl G))
  exact ⟨e.hom, he, (Category.comp_id _).symm.trans h⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  (g : GtCoord I D e G) (g' : GtCoord I D' e G')

theorem mono_torus : Mono g.i := by
  refine ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩

theorem hom_ext_torus (hG : GlobalFnsSt) (f₁ f₂ : thickObj R I e G' ⟶ thickObj R I e G) [IsMonHom f₁] [IsMonHom f₂]
    (hq : f₁ ≫ g.q = f₂ ≫ g.q) (hi : g'.i ≫ f₁ = g'.i ≫ f₂) : f₁ = f₂ := by
  obtain ⟨τ, hτ⟩ := TorusCoord.exists_torus g f₁ f₂ hq
  have := mono_torus g
  have := g.i_hom
  have := g'.q_flat
  have := g'.q_surj
  have := g'.q_affine
  have hc : ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (a : Z ⟶ thickObj R I e G'),
      a ≫ f₁ = (a ≫ τ ≫ g.i) * (a ≫ f₂) := fun Z a => by
    rw [← MonObj.comp_mul, ← hτ]
  have h1 : τ = 1 := by
    refine (splitTorusPointsEquiv _ D.X _).injective (MonoidHom.ext fun χ => Units.ext ?_)
    rw [map_one]
    refine (splitTorusPointsEquiv_val _ D.X _ τ χ.toAdd).trans ?_
    refine eq_one_of_fibre_const_of_section hG _ _ _ (TLinPf.isAb_pullback _ _ D'.P.isAb) g'.q _
      η[thickObj R I e G'] (fun Z a b hab => ?_) ?_
    · obtain ⟨σ, hσ⟩ := TorusCoord.exists_torus g' a b hab
      have e₁ : a ≫ τ = b ≫ τ := by
        rw [← cancel_mono g.i, Category.assoc, Category.assoc]
        have ha := hc Z a
        have hb := hc Z b
        have k₁ : a ≫ f₁ = (σ ≫ g'.i ≫ f₂) * (b ≫ f₁) := by
          rw [hσ, MonObj.mul_comp, Category.assoc, hi]
        have k₂ : a ≫ f₂ = (σ ≫ g'.i ≫ f₂) * (b ≫ f₂) := by
          rw [hσ, MonObj.mul_comp, Category.assoc]
        rw [k₁, k₂, hb, mul_left_comm] at ha
        rw [mul_left_comm] at ha
        rw [mul_left_comm (a ≫ τ ≫ g.i)] at ha
        exact (mul_right_cancel (mul_left_cancel ha)).symm
      rw [← FunDescent.comp_appTop_apply, ← FunDescent.comp_appTop_apply, ← Over.comp_left,
        ← Over.comp_left, e₁]
    · have e₁ : η[thickObj R I e G'] ≫ τ = 1 := by
        rw [← cancel_mono g.i, MonObj.one_comp, Category.assoc]
        have ha := hc _ η[thickObj R I e G']
        rw [IsMonHom.one_hom f₁, IsMonHom.one_hom f₂] at ha
        exact (mul_eq_right.1 ha.symm)
      rw [← FunDescent.comp_appTop_apply, ← Over.comp_left, e₁]
      refine (splitTorusPointsEquiv_val _ D.X _ 1 χ.toAdd).symm.trans ?_
      rw [map_one]
      rfl
  rw [hτ, h1, MonObj.one_comp, _root_.one_mul]

theorem exists_torus_map (h : thickObj R I e G' ⟶ thickObj R I e G)
    (b : thickObj R I e D'.P.A ⟶ thickObj R I e D.P.A) [IsMonHom b] (hq : h ≫ g.q = g'.q ≫ b)
    {F : D'.P.A.left ⟶ D.P.A.left} (w : LB.Iso D'.P.L (D.P.L.pull F)) (xe : D'.X → D.X)
    (hψ : ∀ x κ, D'.Oφ g'.pG x κ ≫ F = h.left ≫ D.Oφ g.pG (xe x) κ)
    (H : ∀ x, PMaps w (D'.Oφ g'.pG x) (D.Oφ g.pG (xe x)) Oinvε (g'.t x) (g.t (xe x)) h.left) :
    ∃ s : splitTorus _ D'.X ⟶ splitTorus _ D.X, s ≫ g.i = g'.i ≫ h ∧
      ∀ x z, gm s.left z ⊤ (charUnit _ D.X (xe x)) = gm (𝟙 _) z ⊤ (charUnit _ D'.X x) := by
  have hd : (g'.i ≫ h) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, g'.isKernel.w, Category.assoc, IsMonHom.one_hom]
  have hs := g.isKernel.lift_fst _ _ hd
  refine ⟨_, hs, fun x z => ?_⟩
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB z
  obtain ⟨J', hJ'⟩ := TorusCoord.exists_good' D'.P.isLB z
  have v₁ := PowTorus.val_on_torus g (xe x) hJ (g.isKernel.lift _ _ hd)
  have v₂ := PowTorus.val_on_torus g' x hJ' (𝟙 _)
  rw [hs] at v₁
  rw [Category.id_comp] at v₂
  have v₃ : val (g.t (xe x)) (g'.i.left ≫ h.left) z J =
      (∏ k, gw w (g'.i.left ≫ D'.Oφ g'.pG x k) z (J ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F))
        (J' (g'.i.left ≫ D'.Oφ g'.pG x k)) ^ Oinvε k) * val (g'.t x) g'.i.left z J' :=
    (val_of _ (g'.i.left ≫ h.left) z J (fun k => J ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F)) (fun k => by
      rw [Category.assoc, Category.assoc, hψ])).trans
    (H x _ g'.i.left z _ _ (fun k => hJ ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F))
      (fun k => hJ' (g'.i.left ≫ D'.Oφ g'.pG x k)))
  rw [PowTorus.prod_on_torus g' x (fun ψ => gw w ψ z (J (ψ ≫ F)) (J' ψ)), _root_.one_mul] at v₃
  exact v₁.symm.trans (v₃.trans v₂)

theorem gm_torusEnd {S : Scheme.{0}} {X : Type} [AddCommGroup X] {u : X → X}
    {t : splitTorus S X ⟶ splitTorus S X} (ht : TorusEndOf X u t) {Z : Scheme.{0}}
    (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X) :
    gm (r ≫ t.left) z ⊤ (charUnit S X χ) = gm r z ⊤ (charUnit S X (u χ)) := by
  rw [← ht χ]
  exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm

theorem gm_comp_of_id {X Y Z : Scheme.{0}} (s : Y ⟶ X) (a : Γ(X, ⊤)ˣ) (a' : Γ(Y, ⊤)ˣ)
    (h : ∀ y, gm s y ⊤ a = gm (𝟙 Y) y ⊤ a') (r : Z ⟶ Y) (z : Z) : gm (r ≫ s) z ⊤ a = gm r z ⊤ a' := by
  have e : pullU s ⊤ a = a' := unit_ext fun y _ =>
    (gm_pull (𝟙 Y) s y ⊤ trivial a).trans (by rw [Category.id_comp]; exact h y)
  rw [← e]
  exact (gm_pull r s z ⊤ trivial a).symm

end LinearUnifIso

open LinearUnifIso in

theorem act_comm_of_isPullUnif_id : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom bc.hom → IsPullUnif (RingHom.id R) hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG' → (∀ (x : O) (y : D'.toPre.X), hD.xe (x • y) = x • hD.xe y) → (∀ x, (ιD'.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ (ιD.onB.act x).left) → ∀ x, ιG'.act x ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (ιG.act x) := by
  intro hG R _ _ _ I _ hI D D' A A' G G' _ _ _ _ _ sG' U U' hD bc hbc hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    lin lin' hx hB a
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨φ, hφ, eφ⟩ := exists_hom_of_pullback_id hs bc
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').1 hU
  have P : ∀ (e : ℕ) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback (thick R I e)).map c).left ≫ pullback.fst Y.hom (thick R I e) =
        pullback.fst X.hom (thick R I e) ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : ιD'.onB.act a ≫ ψ = ψ ≫ ιD.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ]; exact hB a)
  have key : ιG'.act a ≫ φ = φ ≫ ιG.act a := by
    have := sG'.smooth
    have := sG'.geomConnected
    have := U.separated
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I
      (hI ▸ IsLocalRing.maximalIdeal_le_jacobson ⊥) G').2 G _ _ fun e => ?_
    obtain ⟨h, hf, ⟨hp, ht⟩, -⟩ := H e
    obtain rfl : h = ((Over.pullback (thick R I e)).map φ).left := by
      rw [← cancel_mono (pullback.fst G.hom (thick R I e)), P, eφ]
      exact hf
    have hq : (Over.pullback (thick R I e)).map φ ≫ (U.gt e).q =
        (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
      refine Over.OverMorphism.ext ?_
      rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
        Category.assoc, Category.assoc, P, eψ]
      exact hp.symm.trans (Category.assoc _ _ _)
    obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
      (fun x => (ht x).2)
    obtain ⟨t, tc, ti⟩ := lin.i_lin e a
    obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
    have := ιG.hom a
    have := ιG'.hom a
    have hts : t' ≫ s = s ≫ t := by
      refine PowTorus.torus_ext _ _ fun χ z => ?_
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
        ← gm_torusEnd tc', Category.id_comp]
    have E : (Over.pullback (thick R I e)).map (ιG'.act a) ≫ (Over.pullback (thick R I e)).map φ =
        (Over.pullback (thick R I e)).map φ ≫ (Over.pullback (thick R I e)).map (ιG.act a) := by
      refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
          ← Functor.map_comp, ← Functor.map_comp, hψa]
      · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]
    rw [← Functor.map_comp, ← Functor.map_comp] at E
    exact (P e _).symm.trans ((congrArg (fun c => c.left ≫ pullback.fst G.hom (thick R I e)) E).trans (P e _))
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (ιG.act a)).left ≫
      pullback.fst G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (ιG.act a).left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, ← eφ, ← Category.assoc, ← eφ,
    ← Over.comp_left, key, Over.comp_left]

end GlobalTheory
