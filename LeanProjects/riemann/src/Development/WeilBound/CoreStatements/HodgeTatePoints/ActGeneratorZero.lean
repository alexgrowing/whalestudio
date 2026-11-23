import Development.WeilBound.CoreStatements.HodgeTatePoints.CdUniv
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio

noncomputable section
namespace PositivityTheory.HtPt.Cd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Gen
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw comp1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X0 : Scheme.{0}}
  {t : SAB H X0} {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d n : ℕ}

theorem aug_psJet {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    (jetAug : Jet S κ m →ₐ[S] S) (psJet m f) = MvPowerSeries.constantCoeff f := by
  show MvPolynomial.aeval (fun _ => (0 : S)) (psTrunc m f) = _
  rw [MvPolynomial.aeval_zero', ← FBIdPh.cc_psTrunc m f]; rfl

theorem aug_jQ {k : ℕ} (m : ℕ) (b : Fin k → Q S d n) :
    (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S).comp (jQ m b) = jetAug :=
  jet_hom_ext fun s => by
    rw [AlgHom.comp_apply, jQ_X, aug_psJet, GermB.jetAug_X]; exact (b s.1).2 s.2

theorem trunc_jQ {k : ℕ} (m : ℕ) (b : Fin k → Q S d n) :
    (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _).comp (jQ (m + 1) b) = (jQ m b).comp jetTrunc :=
  jet_hom_ext fun s => by
    rw [AlgHom.comp_apply, jQ_X, FrRatio.psJet_trunc, AlgHom.comp_apply, jetTrunc_mk, jQ_X]

theorem act_generator_zero (A : Q S d 1) : ac A (gen 0) = A :=
  Subtype.ext (funext fun i => (congrArg (sb · (A.1 i)) (funext fun j => by fin_cases j; rfl)).trans (sb_gen _))

theorem ac_zero (A : Q S d 1) : ac A (0 : Q S d n) = 0 := Subtype.ext (funext fun i => by
  have e := TB.LogPf.ev_zeroFam (n := n) (A.1 i)
  rw [A.2 i, map_zero] at e
  exact ((sb_apply _ _).trans (congrArg (ev · (A.1 i)) (funext fun j => by fin_cases j; rfl))).trans e)

variable (g g₂ : GermAt t x d)

theorem PP_inj {u v : Q S d n} (h : ∀ m, PP m g.x u = PP m g.x v) : u = v := by
  refine Subtype.ext (funext fun i => ps_ext fun m => ?_)
  have := (coord_aug g (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) (ker_aug_pow _ m) (PP m g.x u) (by
    rw [PP, ← Category.assoc, homAt_comp, aug_jQ, g.chart.zero])).unique ⟨aug_jQ m ![u], rfl⟩ ⟨aug_jQ m ![v], h m⟩
  have e := AlgHom.congr_fun this (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
  rwa [jQ_X, jQ_X] at e

theorem exists_coord : ∃ φ : Q S d 1, ∀ m, g₂.x m = PP m g.x φ := by
  choose χ hχ using fun m => (coord_aug g (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (ker_aug_pow _ m) (g₂.x m)
    (g₂.chart.zero m)).exists
  have tr : ∀ m, (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S).comp jetTrunc = jetAug := fun m =>
    jet_hom_ext fun s => by rw [AlgHom.comp_apply, jetTrunc_mk, GermB.jetAug_X, GermB.jetAug_X]
  have hc : ∀ m, (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _).comp (χ (m + 1)) = (χ m).comp jetTrunc := fun m => by
    refine (coord_aug g (m := m + 1) (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S)
      (le_bot_iff.1 ((Ideal.pow_le_pow_right (Nat.le_succ _)).trans (ker_aug_pow _ m).le)) (g₂.x m) (g₂.chart.zero m)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [← AlgHom.comp_assoc, tr, (hχ (m + 1)).1]
    · rw [← homAt_comp, Category.assoc, ← (hχ (m + 1)).2, g₂.chart.trunc]
    · rw [← AlgHom.comp_assoc, (hχ m).1, tr]
    · rw [← homAt_comp, Category.assoc, g.chart.trunc, ← (hχ m).2]
  choose φ hφ using fun i : Fin d => exists_ps_of_jets
    (fun m => χ m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))) (fun m => AlgHom.congr_fun (hc m) _)
  have h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := fun i => by
    rw [← aug_psJet 0, hφ, ← AlgHom.comp_apply, (hχ 0).1, GermB.jetAug_X]
  refine ⟨⟨φ, h0⟩, fun m => (hχ m).2.trans ?_⟩
  rw [PP]
  congr 2
  refine jet_hom_ext fun s => ?_
  obtain ⟨j, s⟩ := s
  obtain rfl := Subsingleton.elim j 0
  rw [jQ_X]
  exact (hφ s m).symm

variable {g g₂} {φ : Q S d 1} (hφ : ∀ m, g₂.x m = PP m g.x φ)
include hφ

theorem PP_coord (m : ℕ) (u : Q S d n) : PP m g₂.x u = PP m g.x (ac φ u) := by
  rw [PP, hφ, PP_sq]; rfl

theorem coord_op (u v : Q S d n) : ac φ (op (FQ g₂.B.G) u v) = op (FQ g.B.G) (ac φ u) (ac φ v) :=
  PP_inj g fun m => by rw [← PP_coord hφ, PP_op g₂.chart, PP_op g.chart, PP_coord hφ, PP_coord hφ]

theorem coord_ac (a : 𝓞 E) (u : Q S d n) : ac φ (ac (AQ g₂.B.A a) u) = ac (AQ g.B.A a) (ac φ u) :=
  PP_inj g fun m => by rw [← PP_coord hφ, PP_ac g₂.chart, PP_ac g.chart, PP_coord hφ]

theorem coord_inv {ψ : Q S d 1} (hψ : ∀ m, g.x m = PP m g₂.x ψ) : comp1 φ.1 ψ.1 = pt S (n := 1) d 0 := by
  have : ac φ (ac ψ (gen 0)) = (gen 0 : Q S d 1) := PP_inj g fun m => by rw [← PP_coord hφ, ← PP_coord hψ]
  rw [act_generator_zero] at this
  exact (ac_val φ ψ).symm.trans (congrArg Subtype.val this)

theorem coord_tan (l : Fin d) : IsCombAtG t x g.tg (fun j => lin φ.1 1 j l) (g₂.tg l) := by
  have e : jetSubstP 1 (fun p : Fin 1 × Fin d => psTrunc 1 (φ.1 p.2)) = jQ 1 ![φ] :=
    subst_eq 1 _ ![φ] (fun s => by obtain ⟨j, s⟩ := s; fin_cases j; rfl)
      (fun s => (FBIdPh.cc_psTrunc 1 _).trans (φ.2 _))
  have e₂ : (fun j => lin φ.1 1 j l) = (lin φ.1 1).mulVec (Pi.single l 1) := by
    funext j; simp
  rw [comb_iff, tg_eq, tv_gd, tv_gd, hφ, PP, ← e, GlobalTheory.ChartCompare.hcomp, vec_subst, e₂]

theorem exists_lam : ∃ lam : PS S 2 d, ∀ {n m} {y : (jOG x d m n).left} {J}, Good t.PP.L y J → ∀ u v : Q S d n,
    VV m y (E2 lam u v) = (ee g₂.x g₂.e y J u v * (ee g.x g.e y J (ac φ u) (ac φ v))⁻¹).val := by
  let b : Fin 2 → Q S d 2 := ![ac φ (gen 0), ac φ (gen 1)]
  have hb : ∀ m (i : Fin 2), homAt x (jQ m b) ≫ jptG t x d g.x m i = jptG t x d g₂.x m i := fun m i => by
    rw [PP_gen, PP_gen, PP_sq, sq_gen, PP_coord hφ]
    fin_cases i <;> rfl
  obtain ⟨lam, hlam⟩ := GermB.exists_series t x d (n := 2)
    (fun m => cφG t ![jptG t x d g₂.x m (0 : Fin 2), jptG t x d g₂.x m (1 : Fin 2)]) (cε 2) _ (cε 2)
    (fun m => g₂.e m) g₂.frame.gen
    (fun m => LB.pullGen t.PP.L (cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (cε 2) (g.e m)
      (homAt x (jQ m b)).left)
    (fun m => pullGen_isGen _ _ _ _ (g.frame.gen m) _)
    (fun m U _ h => Finset.prod_congr rfl fun I _ => by rw [GermB.pe_pt, hb, hb]; rfl)
    (fun m y J hJ => (congrArg (fun r => val (g₂.e (m + 1)) r y J) (Category.id_comp _).symm).trans
      ((val_pull hJ _ _ _).symm.trans (val_corr hJ (g₂.trunc m) _)))
    (fun m y J hJ => by
      have hs : (GermB.ρn x d 2 m).left ≫ (homAt x (jQ (m + 1) b)).left =
          (𝟙 _ ≫ (homAt x (jQ m b)).left) ≫ (GermB.ρn x d 2 m).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp, trunc_jQ]
      exact (val_pull hJ (g.e (m + 1)) _ _).trans ((congrArg (fun r => val (g.e (m + 1)) r y J) hs).trans
        ((val_pull hJ (g.e (m + 1)) _ _).symm.trans ((val_corr hJ (g.trunc m) _).trans (val_pull hJ (g.e m) _ _).symm))))
  refine ⟨lam, fun {n m y J} hJ u v => ?_⟩
  obtain ⟨U, hU, h⟩ := hlam m
  have hc := gm_unit (y := y) U ![u, v] _ hU
  have e₀ : val (LB.pullGen t.PP.L (cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (cε 2) (g.e m)
      (homAt x (jQ m b)).left) (homAt x (jQ m ![u, v])).left y J = ee g.x g.e y J (ac φ u) (ac φ v) := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [← Over.comp_left, homAt_comp, jQ_comp]
    exact congrArg (fun a => val (L := t.PP.L)
      (φ := cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)])
      (ε := cε 2) (g.e m) (homAt x (jQ m a)).left y J) (funext fun j => by
        fin_cases j
        · exact (sq_ac _ _ _).trans (congrArg (ac φ) (sq_gen _ _))
        · exact (sq_ac _ _ _).trans (congrArg (ac φ) (sq_gen _ _)))
  have k : ee g₂.x g₂.e y J u v = _ * ee g.x g.e y J (ac φ u) (ac φ v) :=
    (val_corr hJ h _).trans ((FBIdAd.val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl e₀))
  exact hc.symm.trans (congrArg Units.val (eq_mul_inv_of_mul_eq k.symm))

omit hφ in
theorem exists_dA (hs : ∀ a : 𝓞 E, star a = H.bar a) (g : GermAt t x d) (a : 𝓞 E) :
    ∃ wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
      (∀ {n m} {y : (jOG x d m n).left} {J}, Good t.PP.L y J → ∀ u v : Q S d n, VV m y (E2 (g.B.ad a) u v) =
        (val₂ wL y J (PP m g.x u) (PP m g.x v) * ee g.x g.e y J (ac (AQ g.B.A a) u) v *
          (ee g.x g.e y J u (ac (AQ g.B.A (star a)) v))⁻¹).val) ∧
      ∀ {n m} {y : (jOG x d m n).left} {J}, Good t.PP.L y J → val₂ wL y J (1 : jOG x d m n ⟶ t.G) 1 = 1 := by
  obtain ⟨wL, hw, hU⟩ := g.frame.ad a
  have dA : ∀ {n m} {y : (jOG x d m n).left} {J}, Good t.PP.L y J → ∀ u v : Q S d n, VV m y (E2 (g.B.ad a) u v) =
        (val₂ wL y J (PP m g.x u) (PP m g.x v) * ee g.x g.e y J (ac (AQ g.B.A a) u) v *
          (ee g.x g.e y J u (ac (AQ g.B.A (star a)) v))⁻¹).val := fun {n m y J} hJ u v => by
    obtain ⟨U, h₁, h₂⟩ := hU m
    rw [hs]; exact dict_ad hJ a wL U h₁ h₂ u v
  refine ⟨wL, hw, dA, fun {n m y J} hJ => ?_⟩
  have k := dA hJ 0 0
  have z : E2 (g.B.ad a) (0 : Q S d n) 0 = 1 := by
    have e : E2 (g.B.ad a) (0 : Q S d 1) (gen 0) = 1 := (formalSeriesValueAtTwoPoints_eq_ev _ _ _).trans (g.B.adjoint_zero_fst a)
    have := congrArg (sb ![(0 : Q S d n)]) e
    rwa [formalPointSubstitutionSeries_valueAtTwoPoints, map_one, map_zero, sq_gen] at this
  rw [z, VV_one, ac0, ac0, mul_inv_cancel_right, PP_zero g.chart] at k
  exact Units.ext k.symm

omit hφ in
theorem val₂_eq (hp : PowFns t) {K : Type} [Fintype K] {ξ : K → ((t.G ⊗ t.G).left ⟶ t.G.left)} {ε : K → ℤ}
    {w w' : LB.Gen (LB.LinComb t.PP.L ξ ε)} (hw : w.IsGen) (hw' : w'.IsGen) {T : Over X0} {z : T.left} {J}
    (hJ : Good t.PP.L z J) (h : val₂ w z J (1 : T ⟶ t.G) 1 = 1) (h' : val₂ w' z J (1 : T ⟶ t.G) 1 = 1)
    (p q : T ⟶ t.G) : val₂ w z J p q = val₂ w' z J p q := by
  have key := ratio_pow (hp 3).2 t.PP.isLB (fun U _ h => rfl)
    (pullGen_isGen _ _ _ _ hw (lift (powPr t.G (0 : Fin 3)) (powPr t.G (2 : Fin 3))).left)
    (pullGen_isGen _ _ _ _ hw' (lift (powPr t.G (0 : Fin 3)) (powPr t.G (2 : Fin 3))).left) p p q hJ
  simpa only [val_ros _ _ hJ, tup_0, tup_2, h, h', _root_.mul_one] using key

set_option maxHeartbeats 2000000 in
theorem iso_of_coord (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {ψ : Q S d 1}
    (hψ : ∀ m, g.x m = PP m g₂.x ψ) : ∃ lam, GlobalTheory.CompanionTheory.Ar.Conj.IsIso g.B g₂.B φ.1 ψ.1 lam := by
  have hL := t.PP.isLB
  obtain ⟨lam, dL⟩ := exists_lam hφ
  have g2 : ∀ f : PS S 2 d, ev (n := 2) ![pt S d 0, pt S d 1] f = f := fun f =>
    (formalSeriesValueAtTwoPoints_eq_ev f (gen 0) (gen 1)).symm.trans (formalSeriesValueAtTwoPoints_genericPoints f)
  have g3 : ∀ f : PS S 3 d, ev (n := 3) ![pt S d 0, pt S d 1, pt S d 2] f = f := fun f =>
    (formalSeriesValueAtThreePoints_eq_ev f (gen 0) (gen 1) (gen 2)).symm.trans (formalSeriesValueAtThreePoints_genericPoints f)
  refine ⟨lam, φ.2, ψ.2, coord_inv hφ hψ, coord_inv hψ hφ, ⟨?_, ?_⟩, ?_, fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
  · have : E2 lam (0 : Q S d 1) (gen 0) = 1 := VV_ext (x0 := x) hL fun m y J hJ => by
      rw [dL hJ, VV_one, ac_zero, (dict_ax hJ g.axes _).1, (dict_ax hJ g₂.axes _).1]; simp
    exact (formalSeriesValueAtTwoPoints_eq_ev lam (0 : Q S d 1) (gen 0)).symm.trans this
  · have : E2 lam (gen 0 : Q S d 1) 0 = 1 := VV_ext (x0 := x) hL fun m y J hJ => by
      rw [dL hJ, VV_one, ac_zero, (dict_ax hJ g.axes _).2, (dict_ax hJ g₂.axes _).2]; simp
    exact (formalSeriesValueAtTwoPoints_eq_ev lam (gen 0 : Q S d 1) 0).symm.trans this
  · have := congrArg Subtype.val (coord_op hφ (gen 0 : Q S d 2) (gen 1))
    simpa only [op_val, ac_val, gen_val] using this
  · have := coord_ac hφ a (gen 0 : Q S d 1)
    rw [act_generator_zero, act_generator_zero] at this
    simpa only [ac_val] using congrArg Subtype.val this
  · have : E3 g₂.B.ph1 (gen 0 : Q S d 3) (gen 1) (gen 2) * E2 lam (op (FQ g₂.B.G) (gen 0) (gen 1)) (gen 2) =
        E2 lam (gen 0) (gen 2) * E2 lam (gen 1) (gen 2) *
          E3 g.B.ph1 (ac φ (gen 0)) (ac φ (gen 1)) (ac φ (gen 2)) := VV_ext (x0 := x) hL fun m y J hJ => by
      simp only [VV_mul, frame_biext_dictionary_first_partial_law hJ g.frame, frame_biext_dictionary_first_partial_law hJ g₂.frame, dL hJ, ← Units.val_mul]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [PP_coord hφ, coord_op hφ, ofMul_mul, ofMul_inv]
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, g3] using this
  · have : E3 g₂.B.ph2 (gen 0 : Q S d 3) (gen 1) (gen 2) * E2 lam (gen 0) (op (FQ g₂.B.G) (gen 1) (gen 2)) =
        E2 lam (gen 0) (gen 1) * E2 lam (gen 0) (gen 2) *
          E3 g.B.ph2 (ac φ (gen 0)) (ac φ (gen 1)) (ac φ (gen 2)) := VV_ext (x0 := x) hL fun m y J hJ => by
      simp only [VV_mul, frame_biext_dictionary_second_partial_law hJ g.frame, frame_biext_dictionary_second_partial_law hJ g₂.frame, dL hJ, ← Units.val_mul]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [PP_coord hφ, coord_op hφ, ofMul_mul, ofMul_inv]
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, g3] using this
  · have : E2 g₂.B.sy (gen 0 : Q S d 2) (gen 1) * E2 lam (gen 0) (gen 1) =
        E2 g.B.sy (ac φ (gen 0)) (ac φ (gen 1)) * E2 lam (gen 1) (gen 0) := VV_ext (x0 := x) hL fun m y J hJ => by
      simp only [VV_mul, dict_sy hJ g.frame, dict_sy hJ g₂.frame, dL hJ, ← Units.val_mul]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [ofMul_mul, ofMul_inv]
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, g2] using this
  · obtain ⟨w, hw, dA, h1⟩ := exists_dA hs g a
    obtain ⟨w₂, hw₂, dA₂, h1₂⟩ := exists_dA hs g₂ a
    have : E2 (g₂.B.ad a) (gen 0 : Q S d 2) (gen 1) * E2 lam (gen 0) (ac (AQ g₂.B.A (star a)) (gen 1)) =
        E2 lam (ac (AQ g₂.B.A a) (gen 0)) (gen 1) * E2 (g.B.ad a) (ac φ (gen 0)) (ac φ (gen 1)) :=
      VV_ext (x0 := x) hL fun m y J hJ => by
        simp only [VV_mul, dA hJ, dA₂ hJ, dL hJ, ← Units.val_mul]
        refine congrArg Units.val (Additive.ofMul.injective ?_)
        simp only [PP_coord hφ, coord_ac hφ, ofMul_mul, ofMul_inv]
        rw [val₂_eq hp hw₂ hw hJ (h1₂ hJ) (h1 hJ)]
        abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, g2] using this

end Gen

theorem germ_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g g₂ : GermAt t x d), ∃ (φ ψ : Germ.Pt S 1 d) (lam : Germ.PS S 2 d), IsIso g.B g₂.B φ ψ lam ∧ ∀ l, IsCombAtG t x g.tg (fun j => lin φ 1 j l) (g₂.tg l) := by
  intro E _ _ _ H _ hs X0 t hp S _ _ x d g g₂
  obtain ⟨φ, hφ⟩ := exists_coord g g₂
  obtain ⟨ψ, hψ⟩ := exists_coord g₂ g
  obtain ⟨lam, h⟩ := iso_of_coord hφ hs hp hψ
  exact ⟨φ.1, ψ.1, lam, h, coord_tan hφ⟩

end PositivityTheory.HtPt.Cd
