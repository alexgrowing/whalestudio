import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginIffPullback
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceInt.FrameTie

open GermD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cube_points {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (a : Fin d → MvPowerSeries (Fin 1 × Fin d) S) (m : ℕ)
    (ha : x m ≫ t.act.act H.w0 =
      Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (a p.2)) ≫ x m)
    (I : ULift.{0} (Finset (Fin 2))) :
    (x m).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (Formalism.L2.Pj.homAt x0 (sL m a)).left ≫
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
  have hpt : (fun i => x m ≫ (![𝟙 t.G, t.act.act H.w0] : Fin 2 → (t.G ⟶ t.G)) i) =
      fun i => Formalism.L2.Pj.homAt x0 (sL m a) ≫
        (![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] : Fin 2 → (jOG x0 d m 2 ⟶ t.G)) i := by
    funext i
    fin_cases i
    · show x m ≫ 𝟙 t.G = Formalism.L2.Pj.homAt x0 (sL m a) ≫ Formalism.L2.Pj.homAt x0 (jetCopy d m (0 : Fin 2)) ≫ x m
      rw [Category.comp_id, ← Category.assoc, homAt_comp, sL_copy0, homAt_id, Category.id_comp]
    · show x m ≫ t.act.act H.w0 =
        Formalism.L2.Pj.homAt x0 (sL m a) ≫ Formalism.L2.Pj.homAt x0 (jetCopy d m (1 : Fin 2)) ≫ x m
      rw [← Category.assoc, homAt_comp, sL_copy1, ha]
  simp only [cφG, ← Over.comp_left]
  refine congrArg (fun f => Over.Hom.left f) ?_
  refine (psum_hom (preHom (x m)) _ I.down).trans
    (Eq.trans ?_ (psum_hom (preHom (Formalism.L2.Pj.homAt x0 (sL m a))) _ I.down).symm)
  exact congrArg (fun f => psum t.G f I.down) hpt

theorem prod_points {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (a : Fin d → MvPowerSeries (Fin 1 × Fin d) S) (m : ℕ)
    (ha : x m ≫ t.act.act H.w0 =
      Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (a p.2)) ≫ x m)
    {U : Type} [CommGroup U] (h : ((jOG x0 d m 1).left ⟶ t.G.left) → U) :
    (∏ k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)), h ((x m).left ≫ primφ t k) ^ primε k) *
      ∏ I : ULift.{0} (Finset (Fin 2)), h ((Formalism.L2.Pj.homAt x0 (sL m a)).left ≫
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I) ^ cε 2 I = h (x m).left := by
  simp only [Fintype.prod_sum_type, primφ, primε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id,
    cube_points t x0 d x a m ha]
  rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
  simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one, zpow_one]

theorem val_eLG_tie {X0 X1 : Scheme.{0}} (t : SAB H X0) (t' : SAB H X1) {S S' : Type} [CommRing S] [CommRing S']
    (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X1) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t'.G)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (act' : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S')
    (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' x1 d x' m) (wP : PrimTyG t) (wP' : PrimTyG t')
    (φ : t'.G.left ⟶ t.G.left) (w : LB.Iso t'.PP.L (t.PP.L.pull φ)) (m : ℕ)
    (ha : x' m ≫ t'.act.act H.w0 =
      Formalism.L2.Pj.homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act' H.w0 p.2)) ≫ x' m)
    (c : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' x1 d x' m (0 : Fin 2),
      jptG t' x1 d x' m (1 : Fin 2)] J ≫ φ) (cε 2)))
    (hc : LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' x1 d x' m (0 : Fin 2),
      jptG t' x1 d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L φ _ _ c))
    (cP : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ φ) primε))
    (hP₁ : LB.Gen.Corr t.PP.L _ _ _ _ cP (LB.pullGen t.PP.L _ _ wP φ))
    (hP₂ : LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L φ _ _ cP))
    {Z : Scheme.{0}} (r : Z ⟶ (jOG x1 d m 1).left) (s : Z ⟶ (jOG x0 d m 1).left) (z : Z)
    {J : (Z ⟶ t.G.left) → t.PP.L.ι} {J' : (Z ⟶ t'.G.left) → t'.PP.L.ι} (hJ : Good t.PP.L z J)
    (hJ' : Good t'.PP.L z J') (hx : s ≫ (x m).left = (r ≫ (x' m).left) ≫ φ)
    (he : val (φ := cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (ε := cε 2) (e m)
        (s ≫ (Formalism.L2.Pj.homAt x0 (sL m (act H.w0))).left) z J =
      val c (r ≫ (Formalism.L2.Pj.homAt x1 (sL m (act' H.w0))).left) z J) :
    val (eLG t x0 d x act e wP m) s z J =
      Geo.Tor.gw w (r ≫ (x' m).left) z (J ((r ≫ (x' m).left) ≫ φ)) (J' (r ≫ (x' m).left)) *
        val (eLG t' x1 d x' act' e' wP' m) r z J' := by
  have p₁ := (congrArg (fun q => val wP q z J) hx).trans ((val_pull hJ wP φ _).symm.trans
    ((val_corr hJ hP₁ _).symm.trans (GlobalTheory.RigOriginPull.val_tie w _ _ wP' cP hP₂ _ z hJ hJ')))
  have p₂ := he.trans (GlobalTheory.RigOriginPull.val_tie w _ _ (e' m) c hc _ z hJ hJ')
  have q := prod_points t' x1 d x' (act' H.w0) m ha
    (fun f => Geo.Tor.gw w (r ≫ f) z (J ((r ≫ f) ≫ φ)) (J' (r ≫ f)))
  refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans p₁)
    ((val_pull hJ _ _ _).trans p₂)).trans ((_root_.mul_mul_mul_comm _ _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · refine Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_)) q
    · exact congrArg (fun f => Geo.Tor.gw w f z (J (f ≫ φ)) (J' f) ^ primε k) (Category.assoc _ _ _)
    · exact congrArg (fun f => Geo.Tor.gw w f z (J (f ≫ φ)) (J' f) ^ cε 2 k) (Category.assoc _ _ _)
  · exact ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ' _ _ _) (val_pull hJ' _ _ _))).symm

theorem exists_frame {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) (m : ℕ) (he : (e m).IsGen) (hP : wP.IsGen)
    (ha : x m ≫ t.act.act H.w0 =
      Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act H.w0 p.2)) ≫ x m) :
    ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left) fun _ => (1 : ℤ)),
      τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 1).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι),
        Good t.PP.L z J → val τ r z J = val (eLG t x0 d x act e wP m) r z J := by
  refine exists_gen t.PP.isLB ?_ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen t.PP.L _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ hP _) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ he _))
  intro U _ hU
  rw [Fintype.prod_sum_type, Fin.prod_univ_one, zpow_one]
  exact prod_points t x0 d x (act H.w0) m ha hU

theorem act_of_map {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S))
    (mp : SABMap t' t x0) {A : Type} [CommRing A] [Algebra S A] (x : overAt x0 A ⟶ t.G)
    (x' : overAt (𝟙 (Sp S)) A ⟶ t'.G) (hx : x'.left ≫ mp.φ = x.left) (a : 𝓞 E) (σ : A →ₐ[S] A)
    (h : x ≫ t.act.act a = Formalism.L2.Pj.homAt x0 σ ≫ x) :
    x' ≫ t'.act.act a = Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ ≫ x' := by
  apply Over.OverMorphism.ext
  refine mp.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
  have h' : x.left ≫ (t.act.act a).left = (Formalism.L2.Pj.homAt x0 σ).left ≫ x.left := congrArg (fun q => q.left) h
  have hx' : x'.left ≫ mp.cm.F = x.left := hx
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, mp.act a, ← Category.assoc, hx']
  exact h'

end GlobalTheory.PlaceInt.FrameTie

open GlobalTheory.PlaceInt.FrameTie GermD in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.PlaceInt.frameTie_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ReciprocityTheory.ChartRestriction.G.PullbackSections.FrameTieSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ _ Tc io yI C
  letI := io.toAlgebra
  obtain ⟨⟨-, hact, -⟩, x', hx2, hx1, ⟨e', he'⟩, wP', hPg, ⟨cP₂, hP₂, hP₂'⟩, cP₁, hP₁, hP₁'⟩ := C.gen
  have ha : ∀ m, x' m ≫ C.I.t'.act.act H.w0 = Formalism.L2.Pj.homAt (𝟙 (Sp Tc.Fr))
      (jetSubstP m fun p : Fin 1 × Fin C.ch.d => psTrunc m (C.ch.B.A.act H.w0 p.2)) ≫ x' m := fun m =>
    act_of_map Xo.univ.t yI.1.x C.I.t' C.I.m1 (C.ch.x m) (x' m) (hx1 m) H.w0 _ (C.ch.chart.act m H.w0)
  choose τ _ hτ using fun m => exists_frame C.I.t' (𝟙 (Sp Tc.Fr)) C.ch.d x' C.ch.B.A.act e' wP' m (he' m).1 hPg (ha m)
  refine ⟨x', hx1, hx2, τ, fun m Z r z J J' J'' hJ hJ' hJ'' => ?_⟩
  obtain ⟨-, ⟨c₂, hc₂, hc₂'⟩, c₁, hc₁, hc₁'⟩ := he' m
  rw [Category.comp_id, hτ m Z r z J' hJ']
  constructor
  · refine val_eLG_tie Xo.univ.t C.I.t' yI.1.x (𝟙 (Sp Tc.Fr)) C.ch.d C.ch.x x' C.ch.B.A.act C.ch.B.A.act C.ch.e e'
      C.ch.wP wP' C.I.m1.φ C.I.w1 m (ha m) c₁ hc₁' cP₁ hP₁ hP₁' r r z hJ hJ' ?_ (val_corr hJ hc₁ _).symm
    exact (congrArg (r ≫ ·) (hx1 m).symm).trans (Category.assoc _ _ _).symm
  · refine val_eLG_tie C.I.G C.I.t' (𝟙 (Sp Tc.V)) (𝟙 (Sp Tc.Fr)) C.ch.d C.xT x' C.actT C.ch.B.A.act C.eT e'
      C.wPT wP' C.I.m2.φ C.I.w2 m (ha m) c₂ hc₂' cP₂ hP₂ hP₂' r _ z hJ'' hJ' ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (hx2 m).symm).trans (Category.assoc _ _ _).symm)
    · refine Eq.symm ((val_corr hJ'' hc₂ _).trans ((val_pull hJ'' _ _ _).trans ?_))
      refine congrArg (fun q => val (C.eT m) q z J'') ?_
      refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      refine congrArg (r ≫ ·) (GlobalTheory.ChartRigBC.subst_jetCoef (algebraMap Tc.V Tc.Fr) (𝟙 _)
        (spMap (algebraMap Tc.V Tc.Fr)) C.ch.d m 2 1 _ _ ?_)
      rintro ⟨i, j⟩
      fin_cases i
      · exact (MvPolynomial.map_X _ _).symm
      · exact (congrArg (psIn C.ch.d m ![0]) (hact H.w0 j)).trans (GlobalTheory.RawChartGermBC.map_psIn _ C.ch.d m _ _).symm
