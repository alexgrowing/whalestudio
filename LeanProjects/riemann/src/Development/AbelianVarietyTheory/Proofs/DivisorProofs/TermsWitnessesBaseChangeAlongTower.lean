import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.GSep.TermsTrans

open GlobalTheory.TermsMove GlobalTheory.FieldBaseChange GlobalTheory.TorsionExt GlobalTheory.ArcPull

theorem tfk_hom (V : Type) [CommRing V] [IsDomain V] : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

theorem gw_stalk {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (r : Z ⟶ Y)
    (g : Y ⟶ X') (z : Z) {j : L.ι} {k : L'.ι} (hj : F (g (r z)) ∈ L.U j) (hk : g (r z) ∈ L'.U k) :
    (Geo.Tor.gw w (r ≫ g) z j k).val = (r.stalkMap z).hom (Geo.Tor.gw w g (r z) j k).val := by
  have hm : g (r z) ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  exact (gs_unit (r ≫ g) z _ hm _).symm.trans ((LiftTest.gs_comp r g z _ hm _).trans
    (congrArg _ (gs_unit g (r z) _ hm _)))

theorem exists_theta {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type} [CommRing V]
    [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {t : X → V}
    {δ : I → X → X} (𝔪 : GMem X₁ z₁ act V ev X t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A))
    (fr : ∀ a, FrAt (x a)) (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left)
    (hfr : ∀ a z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) :
    ∃ th : SecA 𝔪.A (FractionRing V) 1, ∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) := by
  have gp := 𝔪.cart
  have hτ : (spMap 𝔪.yK : (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left) ≫
      (baseOver (Sp X₁.S.R)).hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    rw [tfk_hom]; simp
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB (a := 1) X₁.ρ.th₁
  refine ⟨th, fun a => ?_⟩
  have H : GlobalTheory.ThetaPtMove.GenThrough 𝔪.wl _ _ _ (fr a) (X₁.ρ.fr a)
      (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) := by
    intro Z r z J J' hJ hJ'
    have e := congrArg (fun u => (r.stalkMap z).hom (Units.val u))
      (hfr a (r z) _ _ (LevelExpansion.good_comp r hJ) (LevelExpansion.good_comp r hJ'))
    rw [Fin.prod_univ_one, zpow_one]
    refine Units.ext ((LevelExpansion.val_comp _ r _ hJ).trans (e.symm.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ?_ ?_))))
    · refine (gw_stalk 𝔪.wl r (x a).left z (hJ (r ≫ (x a).left ≫ 𝔪.φ)) (hJ' (r ≫ (x a).left))).symm.trans ?_
      rw [← Category.assoc]
      rfl
    · exact (LevelExpansion.val_comp _ r (𝟙 _) hJ').symm.trans (by rw [Category.comp_id])
  have hv := GlobalTheory.ThetaPtMove.isValueAt_move (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) X₁.ρ.P.isLB 𝔪.A.isLB (a := 1)
    (x := x a) (x₀ := X₁.ρ.pt a) (hx a).symm (ρ₀ := X₁.ρ.fr a) (ρ := fr a) H (s₀ := X₁.ρ.th₁) (s := th) hth
    (X₁.ρ.th_val a)
  intro z J hJ
  have e := GlobalTheory.FrameMove.sval_valueAt hv (𝟙 _) hJ
  rw [Category.id_comp] at e
  refine e.trans ?_
  rw [GlobalTheory.FrameMove.val_powFrame, Nat.cast_one, zpow_one]
  congr 1
  exact (gs_pull (𝟙 _) (spMap 𝔪.yK) z ⊤ trivial _).trans
    ((congrArg (fun q => gs q z ⊤ _) (Category.id_comp _)).trans (GlobalTheory.FrameMove.gs_spMap 𝔪.yK z _))

theorem exists_moved {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    [Algebra (FractionRing R) (FractionRing R')] {I : Ideal R} {I' : Ideal R'} {D : DegData R I} {D' : DegData R' I'}
    {hD : IsPullDeg φ D.toPre D'.toPre} {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {Φ : A'.A.left ⟶ A.A.left} {v : LB.Iso A'.L (A.L.pull Φ)} {U : Unif I D A G} {U' : Unif I' D' A' G'}
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} (hI : I.map φ ≤ I') (hbc : IsMonHom bc.hom)
    (hU : IsPullUnif φ hD bc U U') (hF : Compat φ (FractionRing R'))
    (gΦ : IsPullback Φ A'.A.hom A.A.hom (spMap (algebraMap (FractionRing R) (FractionRing R')))) (hv : v.IsGen)
    (hΦ : U'.gen.hom.left ≫ Φ ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))
    {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) {th : SecA A (FractionRing R) 1} {s : Fam D.toPre (FractionRing R) 1}
    (hE : U.ExpandsF (FractionRing R) 1 w₀ th s) :
    ∃ (w₀' : W0 U'.toUnifPre) (th' : SecA A' (FractionRing R') 1) (s' : Fam D'.toPre (FractionRing R') 1),
      w₀'.IsGen ∧ U'.ExpandsF (FractionRing R') 1 w₀' th' s' ∧
      (∀ (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R') (FractionRing R') ⟶ A'.A)
        (fr' : FrAt x') (ρ : (FractionRing R')ˣ) (c : FractionRing R),
        x'.left ≫ Φ = spMap (algebraMap (FractionRing R) (FractionRing R')) ≫ x.left →
        FrPull v (algebraMap _ _) x' fr' x fr ρ → ValAt th x fr c →
        ValAt th' x' fr' (algebraMap (FractionRing R) (FractionRing R') c * (ρ⁻¹).val)) ∧
      ∀ (g : GtPtF D.toPre (FractionRing R)) (w : GlobalTheory.UT.Frm D.toPre (FractionRing R) 1 g.b) (ρ : (FractionRing R')ˣ),
        w.IsGen → ∃ (g' : GtPtF D'.toPre (FractionRing R')) (w' : GlobalTheory.UT.Frm D'.toPre (FractionRing R') 1 g'.b), w'.IsGen ∧
        (∀ n, (∃ o, GtPtF.IsNsmul n g o ∧ o.IsZero) → ∃ o, GtPtF.IsNsmul n g' o ∧ o.IsZero) ∧
        (∀ α, coef s' g' w' α * ρ = algebraMap (FractionRing R) (FractionRing R') (coef s g w (hD.xe α))) ∧
        ∀ (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R') (FractionRing R') ⟶ A'.A)
          (fr' : FrAt x'), fr.IsGen → x'.left ≫ Φ = spMap (algebraMap (FractionRing R) (FractionRing R')) ≫ x.left →
          FrPull v (algebraMap _ _) x' fr' x fr ρ → LiesOver U.toUnifPre (FractionRing R) w₀ g w x fr →
          LiesOver U'.toUnifPre (FractionRing R') w₀' g' w' x' fr' := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  have hg₂ : jFK (R := R') (FractionRing R') ≫ spMap (algebraMap (FractionRing R) (FractionRing R')) =
      jFK (R := R) (FractionRing R') := by
    rw [show jFK (R := R') (FractionRing R') = 𝟙 _ from tfk_hom R']
    exact Category.id_comp _
  obtain ⟨w₀', hw₀', Ω, h₁, h₂, H⟩ := exists_expand hG hbc hU hF hg₂ gΦ hv hΦ hw₀ hκ
  obtain ⟨th', s', E', up, fup⟩ := (H 1 le_rfl).1 _ _ (expandsF_pull (F := FractionRing R') U.toUnifPre hG hE)
  have frup : ∀ {x : TFK (R := R) (FractionRing R) ⟶ A.A} {fr : FrAt x} {x' : TFK (R := R') (FractionRing R') ⟶ A'.A}
      {fr' : FrAt x'} {ρ : (FractionRing R')ˣ}, FrPull v (algebraMap _ _) x' fr' x fr ρ →
      FrUp v fr' (frExt (FractionRing R') fr) ρ := fun {x fr x' fr' ρ} h z J J' hJ hJ' => by
    refine (h z J J' hJ hJ').trans (congrArg₂ (· * ·) rfl (congrArg Units.val ?_))
    exact ((val_frExt fr (𝟙 _) hJ).trans (by rw [Category.id_comp])).symm
  refine ⟨w₀', th', s', hw₀', E', fun x fr x' fr' ρ c hx hp hc => ?_, fun g w ρ hw => ?_⟩
  · have := valAt_pull h₁ h₂ up (x := fieldMap (R := R) (FractionRing R) (FractionRing R') ≫ x) hx (frup hp)
      (valAt_ext hc)
    rwa [pow_one] at this
  obtain ⟨g₁, w₁, hw₁, t₁, c₁, l₁⟩ := exists_ext (F := FractionRing R') hG U hw₀ g hw
  obtain ⟨g', w', hw', t₂, c₂, l₂⟩ := exists_point hG hI hF hκ h₁ h₂ (fun k hk => (H k hk).2) g₁ hw₁ ρ
  refine ⟨g', w', hw', fun n h => t₂ n (t₁ n h), fun α => (c₂ _ _ fup α).trans (c₁ s _),
    fun x fr x' fr' gen hx hp hl => ?_⟩
  have a := l₁ x fr gen hl
  have b : (frExt (FractionRing R') fr).IsGen := pullGen_isGen _ _ _ _ gen _
  exact l₂ x' fr' (fieldMap (R := R) (FractionRing R) (FractionRing R') ≫ x) (frExt (FractionRing R') fr) b hx (frup hp) a

theorem terms_witnesses_baseChange : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  intro I X₁ act 𝔗 z₁ z₂ _ x₀ hdiv V _ _ _ ev X _ t δ 𝔪 C lab x fr th w₀ s g' w hx hfr hth hw₀ hE hc V' _ _ _ io f hf hinj hfin
    ev₂ 𝔪₂ ψ hD bc _ hy gψ wψ hwψ hφ hbc hU hxe hgen x₂ fr₂ hx₂ hfr₂ ρ hρ
  letI : Algebra (FractionRing V) (FractionRing V') := f.toAlgebra
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hI : (maximalIdeal V).map io ≤ maximalIdeal V' := by
    have := RingHom.IsIntegral.isLocalHom hfin.to_isIntegral hinj
    exact Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit io v hv
  obtain ⟨w₀₂, th', s', hw₀₂, E', hval, hpt⟩ := exists_moved (v := wψ) hI hbc hU hf gψ.1 hwψ hgen hw₀ hE
  have hxx : ∀ b, (x₂ (𝔗.lam b)).left ≫ ψ = spMap f ≫ (x b).left := fun b => by
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · have e : spMap 𝔪₂.yK ≫ spMap 𝔗.om = spMap f ≫ spMap 𝔪.yK :=
        (Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔪₂.yK)).symm.trans
          ((congrArg spMap hy).trans (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom f)))
      rw [Category.assoc, ← hφ, ← Category.assoc, hx₂, Category.assoc, Category.assoc, hx]
      exact (congrArg (_ ≫ ·) (𝔗.lam_pt b)).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans
        (Category.assoc _ _ _)))
    · rw [Category.assoc, gψ.1.w, ← Category.assoc, Over.w (x₂ (𝔗.lam b)), Category.assoc, Over.w (x b), tfk_hom, tfk_hom]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hv' := fun b => hval _ _ _ _ (ρ b) _ (hxx b) (hρ b) (hth b)
  have hne : (show AbSec 𝔪₂.A (FractionRing V') 1 from th') ≠ 0 := fun h => by
    have h₀ := hv' x₀
    rw [show th' = _ from h] at h₀
    exact mul_ne_zero ((map_ne_zero_iff f f.injective).2
      (GlobalTheory.GSep.GMem.yK_th_ne_zero I X₁ z₁ act V ev X t δ 𝔪 x₀ hdiv)) (Units.ne_zero _)
      (valAt_unique h₀ (valAt_zero _ _))
  obtain ⟨th₂, hth₂⟩ := exists_theta 𝔪₂ x₂ fr₂ hx₂ fun a => (hfr₂ a).2
  obtain ⟨K, hK⟩ := exists_eq_smul hne th₂
  choose g₂ w₂ hw₂ ht₂ hc₂ hl₂ using fun c => hpt (g' c) (w c) (ρ (lab c)) (hc c).2.1
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG 𝔪₂.U (FractionRing V') (k := 1) le_rfl w₀₂ hw₀₂
  refine ⟨th₂, w₀₂, K • s', g₂, w₂, K, hth₂, hw₀₂, (he _ _).2 ?_, fun c => ⟨?_, hw₂ c, ?_⟩, fun mu c => ?_, fun b => ?_⟩
  · exact (congrArg e hK).trans ((map_smul e K _).trans (congrArg (K • ·) ((he _ _).1 E')))
  · letI := @TorusExt.gtGroup
    obtain ⟨o, o₁, o₂⟩ := ht₂ c _ (hc c).1
    rw [TorusExt.isNsmul_iff_eq] at o₁
    rw [TorusExt.isZero_iff_eq] at o₂
    refine ⟨0, (TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (TorusExt.isZero_iff_eq _).2 rfl⟩
    rw [𝔗.lev, mul_nsmul, ← o₁, o₂, nsmul_zero]
  · exact hl₂ c _ _ _ _ (hfr _).1 (hxx _) (hρ _) (hc c).2.2
  · rw [coef_smul (hw₂ c), _root_.mul_assoc, hc₂, hxe]
    rfl
  · have a := valAt_lin (hv' b) (valAt_zero _ _) K
    rw [add_zero, add_zero, ← hK] at a
    rw [valAt_unique (hth₂ _) a, _root_.mul_assoc, Units.inv_mul_cancel_right]
    rfl

end GlobalTheory.GSep.TermsTrans
