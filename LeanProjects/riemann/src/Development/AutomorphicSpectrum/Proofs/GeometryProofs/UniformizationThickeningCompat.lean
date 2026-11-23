import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ResEqOfResEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.GtI

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity

section Units

variable {X Y Z : Scheme.{0}} (L : LB X)

def pullTop (f : Y ⟶ Z) (w : Γ(Z, ⊤)ˣ) : Γ(Y, ⊤)ˣ := res (le_top : ⊤ ≤ f ⁻¹ᵁ (⊤ : Z.Opens)) (pullU f ⊤ w)

def constGen (w : Γ(Y, ⊤)ˣ) : LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) :=
  ⟨fun _ => res le_top w⟩

theorem eq_of_corr_constGen {w w' : Γ(Y, ⊤)ˣ}
    (h : LB.Gen.Corr L _ _ _ _ (constGen L w) (constGen L w')) : w = w' := by
  have e := h PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim) (fun k => k.elim)
  have e2 := res_eq_of_res_eq _ _ (W := ⊤) (fun _ _ => Set.mem_iInter.2 fun k => k.elim)
    (fun _ _ => Set.mem_iInter.2 fun k => k.elim) e
  simp only [constGen] at e2
  erw [res_res', res_res'] at e2
  ext
  simpa [res] using congrArg Units.val e2

variable {K : Type} [Fintype K]

omit L in
theorem shape_const {U₁ U₂ O O' O₂ : Y.Opens} (h₀ : O' ≤ U₁) (h₁ : O' ≤ U₂) (o : O ≤ O') (o' : O ≤ O₂) (o₂ : O₂ ≤ ⊤)
    (a : Γ(Y, U₁)ˣ) (b : Γ(Y, U₂)ˣ) (w : Γ(Y, ⊤)ˣ) (ha : a = res le_top w) (hb : b = 1) :
    res o (res h₀ a * res h₁ b) = res o' (res o₂ w) := by
  subst ha hb
  rw [map_one, _root_.mul_one, res_res', res_res', res_res']

theorem corr_mulGen_const {φ₀ : PEmpty → (Y ⟶ X)} {ε₀ : PEmpty → ℤ} (c : LB.Gen (LB.LinComb L φ₀ ε₀)) (w : Γ(Y, ⊤)ˣ)
    (hc : ∀ j, c.s j = res le_top w) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L φ ε))
    (hu : LB.Gen.Corr L φ ε PEmpty.elim PEmpty.elim u (LB.oneGen L)) :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ c u) (constGen L w) := by
  intro j j' hj _ _
  have h1 := corr_one_alt L hu (j ∘ Sum.inr) (fun k₁ k₂ e => hj (Sum.inr k₁) (Sum.inr k₂) e)
  exact shape_const _ _ _ _ _ _ _ _ (hc _) h1

end Units

section Level

theorem shape_char {W Z' Y : Scheme.{0}} (h : Y ⟶ W) (g : W ⟶ Z') (d : Y ⟶ Z') (e : h ≫ g = d) (x : Γ(Z', ⊤)ˣ)
    {U : W.Opens} (hU : U ≤ g ⁻¹ᵁ ⊤) {V : Y.Opens} (hV : V ≤ h ⁻¹ᵁ U) :
    res hV (pullU h U (res hU (pullU g ⊤ x))) = res le_top (pullTop d x) := by
  subst e
  rw [pullU_res, res_res', pullTop]
  erw [res_res']
  rw [pullU_comp_eq_pullU_pullU]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem t_torus (g : GtCoord I D e G) (χ : D.X) {Y : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (δ : Y ⟶ splitTorus _ D.X) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) (δ ≫ g.i).left)
      (constGen D.P.L (pullTop δ.left (charUnit _ D.X χ))) := by
  have hL : D.P.L.IsLB := D.P.isLB
  let z : Y ⟶ thickObj R I e G := toUnit Y ≫ η[thickObj R I e G]
  let H : Y ⟶ splitTorus _ D.X ⊗ thickObj R I e G := lift δ z
  have hact : H.left ≫ (lift (fst (splitTorus _ D.X) (thickObj R I e G) ≫ g.i) (snd _ _) ≫
      μ[thickObj R I e G]).left = (δ ≫ g.i).left := by
    rw [← Over.comp_left]
    congr 1
    have : H ≫ lift (fst (splitTorus _ D.X) (thickObj R I e G) ≫ g.i) (snd _ _) = lift (δ ≫ g.i) z := by
      simp [H]
    rw [← Category.assoc, this]
    have h1 : z = 1 := (Hom.one_def).symm
    rw [← Hom.mul_def, h1, _root_.mul_one]
  have hsnd : H.left ≫ (snd (splitTorus _ D.X) (thickObj R I e G)).left =
      (toUnit Y).left ≫ eSec (thickObj R I e G) := by
    rw [← Over.comp_left, lift_snd]
    rfl
  have w := corr_pullGen (g.t_weight χ) H.left
  have a1 := corr_pull_comp D.P.L (g.t χ) _ H.left _ hact
  have a2 := corr_pullGen_mulGen (charGen D.X (thickObj R I e G) D.P.L χ)
    (LB.pullGen D.P.L _ _ (g.t χ) (snd (splitTorus _ D.X) (thickObj R I e G)).left) H.left
  have a3 : LB.Gen.Corr D.P.L _ _ PEmpty.elim PEmpty.elim
      (LB.pullGen D.P.L _ _ (LB.pullGen D.P.L _ _ (g.t χ) (snd (splitTorus _ D.X) (thickObj R I e G)).left) H.left)
      (LB.oneGen D.P.L) :=
    corr_trans hL (corr_pull_comp D.P.L (g.t χ) _ H.left _ hsnd)
      (corr_trans hL (corr_symm (corr_pull_comp D.P.L (g.t χ) _ (toUnit Y).left _ rfl))
        (corr_one_pull D.P.L (g.t_unit χ) (toUnit Y).left))
  have a4 := corr_mulGen_const D.P.L (LB.pullGen D.P.L _ _ (charGen D.X (thickObj R I e G) D.P.L χ) H.left)
    (pullTop δ.left (charUnit _ D.X χ))
    (fun j => shape_char _ _ _ (by rw [← Over.comp_left, lift_fst]) _ _ _) _ a3
  exact corr_trans hL (corr_symm a1) (corr_trans hL w (corr_trans hL a2 a4))

theorem t_torus' (g : GtCoord I D e G) (χ : D.X) {Y : Scheme.{0}} (τ : Y ⟶ (splitTorus _ D.X).left) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) (τ ≫ g.i.left))
      (constGen D.P.L (pullTop τ (charUnit _ D.X χ))) :=
  t_torus g χ (Y := Over.mk (τ ≫ (splitTorus _ D.X).hom)) (Over.homMk τ (Over.mk_hom _).symm)

end Level

section Torus

open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

variable (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) (X : Type) [AddCommGroup X]

def tau : (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X).left ⟶
    (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1 + 1)))) X).left :=
  (GlobalTheory.Diag.baseChangeIso (thick R I e) X).inv.left ≫ thickMap R I e (splitTorus (Spec (CommRingCat.of R)) X) ≫
    (GlobalTheory.Diag.baseChangeIso (thick R I (e + 1)) X).hom.left

theorem tau_hom : tau R I e X ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1 + 1)))) X).hom =
    (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X).hom ≫ thickTrans R I e := by
  have h1 := Over.w (GlobalTheory.Diag.baseChangeIso (thick R I (e + 1)) X).hom
  have h2 := Over.w (GlobalTheory.Diag.baseChangeIso (thick R I e) X).inv
  have hs : thickMap R I e (splitTorus (Spec (CommRingCat.of R)) X) ≫
      pullback.snd (splitTorus (Spec (CommRingCat.of R)) X).hom (thick R I (e + 1)) =
      pullback.snd (splitTorus (Spec (CommRingCat.of R)) X).hom (thick R I e) ≫ thickTrans R I e :=
    pullback.lift_snd _ _ _
  simp only [tau, Category.assoc]
  rw [h1, ← h2, Category.assoc]
  exact congrArg (_ ≫ ·) hs

theorem tau_fst : tau R I e X ≫ torusFst (Spec (CommRingCat.of (R ⧸ I ^ (e + 1 + 1)))) X =
    torusFst (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X := by
  have h := GlobalTheory.Diag.baseChangeIso_hom_torusFst (thick R I e) X
  have h' := GlobalTheory.Diag.baseChangeIso_hom_torusFst (thick R I (e + 1)) X
  have hι : thickMap R I e (splitTorus (Spec (CommRingCat.of R)) X) ≫
      pullback.fst (splitTorus (Spec (CommRingCat.of R)) X).hom (thick R I (e + 1)) =
      pullback.fst (splitTorus (Spec (CommRingCat.of R)) X).hom (thick R I e) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hinv : (GlobalTheory.Diag.baseChangeIso (thick R I e) X).inv.left ≫
      (GlobalTheory.Diag.baseChangeIso (thick R I e) X).hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  simp only [tau, Category.assoc]
  rw [h', reassoc_of% hι, ← h, reassoc_of% hinv]

theorem tau_chi (a : X) : (tau R I e X).appTop.hom (chi (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1 + 1)))) X a) =
    chi (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X a := by
  rw [chi, chi, coord, coord]
  simp only [Over.id_left, Category.id_comp]
  conv_rhs => rw [← tau_fst R I e X]
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, appTop_comp_apply]

end Torus

section Main

open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

theorem pullTop_val {Y Z : Scheme.{0}} (f : Y ⟶ Z) (w : Γ(Z, ⊤)ˣ) :
    ((pullTop f w : Γ(Y, ⊤)ˣ) : Γ(Y, ⊤)) = f.appTop.hom (w : Γ(Z, ⊤)) :=
  map_rfl' _

theorem one_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B] (T : Over S') :
    (toUnit T ≫ η[(Over.pullback f).obj B]).left ≫ pullback.fst B.hom f = T.hom ≫ f ≫ η[B].left := by
  have e := congrArg (fun z => z.left) (map_one (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B f) T))
  have e₁ : (1 : T ⟶ (Over.pullback f).obj B) = toUnit T ≫ η[(Over.pullback f).obj B] := Hom.one_def
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[B]).left = _
  rw [Over.comp_left, toUnit_left]
  exact Category.assoc _ _ _

theorem one_fst' {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B] (T : Over S')
    (x : T ⟶ (Over.pullback f).obj B) (hx : x = toUnit T ≫ η[(Over.pullback f).obj B]) :
    x.left ≫ pullback.fst B.hom f = T.hom ≫ f ≫ η[B].left := by
  subst hx
  exact one_fst f B T

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

omit [IsDomain R] in
theorem exists_lift_pullback {S S' : Scheme.{0}} (B : Over S) (f : S' ⟶ S) (T : Over S') (b : T.left ⟶ B.left)
    (hb : b ≫ B.hom = T.hom ≫ f) : ∃ x : T ⟶ (Over.pullback f).obj B, x.left ≫ pullback.fst B.hom f = b :=
  ⟨Over.homMk (pullback.lift b T.hom hb) (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩

theorem pG_left {D₀ : DegPre R} {e : ℕ} (g : GtCoord I D₀ e G) :
    g.pG.left = g.q.left ≫ pullback.fst D₀.P.A.hom (thick R I e) := by
  simp only [GtCoord.pG, DegPre.prBe, Over.comp_left, Over.map_map_left, Over.homMk_left]

theorem tau_i (U : UnifPre I D A G) (e : ℕ) :
    tau R I e D.toPre.X ≫ (U.gt (e + 1)).i.left = (U.gt e).i.left ≫ thickMap R I e G := by
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  have hi' := Over.w (U.gt (e + 1)).i
  have hsnd : (tau R I e D.toPre.X ≫ (U.gt (e + 1)).i.left) ≫ pullback.snd G.hom (thick R I (e + 1)) =
      (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X).hom ≫ thickTrans R I e := by
    rw [Category.assoc]
    exact (congrArg (tau R I e D.toPre.X ≫ ·) hi').trans (tau_hom R I e D.toPre.X)
  obtain ⟨ii, hii⟩ := exists_lift_pullback G (thick R I e)
    (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X)
    ((tau R I e D.toPre.X ≫ (U.gt (e + 1)).i.left) ≫ pullback.fst G.hom (thick R I (e + 1))) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd, Category.assoc, thickTrans_comp])
  have hthick : ii.left ≫ thickMap R I e G = tau R I e D.toPre.X ≫ (U.gt (e + 1)).i.left := by
    apply pullback.hom_ext
    · have h : thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      rw [Category.assoc, h, hii]
    · have h : thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) =
          pullback.snd G.hom (thick R I e) ≫ thickTrans R I e := pullback.lift_snd _ _ _
      rw [Category.assoc, h, hsnd, ← Category.assoc]
      exact congrArg (· ≫ thickTrans R I e) (Over.w ii)
  have hq : ii ≫ (U.gt e).q = toUnit _ ≫ η[thickObj R I e D.toPre.P.A] := by
    apply Tors.hom_ext_pull
    have h1 : (ii ≫ (U.gt e).q).left ≫ pullback.fst D.toPre.P.A.hom (thick R I e) =
        ii.left ≫ (U.gt e).pG.left := by
      rw [pG_left, Over.comp_left, Category.assoc]
    have h2 : (U.gt (e + 1)).i.left ≫ (U.gt (e + 1)).pG.left =
        (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1 + 1)))) D.toPre.X).hom ≫ thick R I (e + 1) ≫
          η[D.toPre.P.A].left := by
      rw [pG_left, ← Category.assoc, ← Over.comp_left]
      exact one_fst' _ _ _ _ (U.gt (e + 1)).isKernel.w
    rw [h1, ← U.gt_q e, reassoc_of% hthick, h2, one_fst, reassoc_of% (tau_hom R I e D.toPre.X),
      reassoc_of% (thickTrans_comp R I e)]
  let δ := (U.gt e).isKernel.lift ii (toUnit _) hq
  have hδ : δ ≫ (U.gt e).i = ii := (U.gt e).isKernel.lift_fst _ _ _
  have hval : ∀ χ : D.toPre.X, GlobalTheory.SplitTorus.val δ χ = GlobalTheory.SplitTorus.val (𝟙 _) χ := fun χ => by
    have c1 := t_torus (U.gt e) χ δ
    have c2 := t_torus' (U.gt (e + 1)) χ (tau R I e D.toPre.X)
    have c3 := corr_pullGen (U.gt_t e χ) ii.left
    have c4 := corr_pull_comp D.toPre.P.L ((U.gt (e + 1)).t χ) (thickMap R I e G) ii.left _ hthick
    have c5 := corr_pullGen_of_eq ((U.gt e).t χ) ((U.gt e).t_gen χ) (δ ≫ (U.gt e).i).left ii.left
      (congrArg (fun z => z.left) hδ)
    have e1 := eq_of_corr_constGen D.toPre.P.L (corr_trans hL (corr_symm c1) (corr_trans hL c5
      (corr_trans hL (corr_symm c3) (corr_trans hL c4 c2))))
    have e2 := congrArg Units.val e1
    rw [pullTop_val, pullTop_val, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val, tau_chi] at e2
    rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_id, e2]
  have hδ1 : δ = 𝟙 _ := GlobalTheory.SplitTorus.hom_ext hval
  rw [hδ1, Category.id_comp] at hδ
  rw [hδ, hthick]

end Main

theorem gt_i : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ), thickMap R I e (splitTorus (Spec (CommRingCat.of R)) D.toPre.X) ≫ (GlobalTheory.Diag.baseChangeIso (thick R I (e + 1)) D.toPre.X).hom.left ≫ (U.gt (e + 1)).i.left = (GlobalTheory.Diag.baseChangeIso (thick R I e) D.toPre.X).hom.left ≫ (U.gt e).i.left ≫ thickMap R I e G := by
  intro R _ _ I D A G _ _ U e
  have h := tau_i U e
  have hb : (GlobalTheory.Diag.baseChangeIso (thick R I e) D.toPre.X).hom.left ≫
      (GlobalTheory.Diag.baseChangeIso (thick R I e) D.toPre.X).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  rw [← h, tau]
  simp only [Category.assoc]
  rw [reassoc_of% hb]

end GlobalTheory.CompanionTheory.Ar.BT.GtI
