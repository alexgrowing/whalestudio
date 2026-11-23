import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetFramesDifferByUnitEachOrder
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioFirstPartialLaw
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioAdjointnessSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh GlobalTheory.FrameBiextId

namespace GlobalTheory.ChartField

section Sections
variable {X Z : Scheme.{0}} {A : Over X} [GrpObj A] {L : LB A.left} {T T' : Over X}

theorem sval_valueAt {a : ℤ} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s x τ v) (r : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ (ptSecT A x).left) z J =
      gs r z ⊤ v * (val τ r z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) r
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ (ptSecT A x).left) z J
    (fun _ => J (r ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])]
  refine Eq.trans ?_ ((congrArg (gs r z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull r (ptSecT A x).left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (r ≫ x.left))) (val_le A L x _ hy) _)).symm

theorem sval_pull {a : ℤ} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A} {s : LB.Sec (LPow A L a T)}
    {s' : LB.Sec (LPow A L a T')} (H : IsPullSec A L a h hh s s') (r : Z ⟶ (T' ⊗ A).left) {z : Z} {J}
    (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T' A).left) (ε := fun _ => a) s' r z J =
      sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ h.left) z J := by
  have hy := hJ.mem (fun _ : Fin 1 => (snd T' A).left) r
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ h.left) z J
    (fun _ => J (r ≫ (snd T' A).left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, hh])]
  refine (congrArg (gs r z _) (H _)).trans ((gs_res _ z _ hy _).trans ?_)
  exact gs_pull r h.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (r ≫ (snd T' A).left)))
    (chart_le_res A L h hh a _ hy) _

end Sections

variable {S : Type} [CommRing S] {d : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
  {x0 : Sp S ⟶ X0} {x x' : ∀ m, jOG x0 d m 1 ⟶ t.G}

theorem germ_val {G : FGLaw S d} (A : Germ.OAct (𝓞 E) G) {e : ∀ m, FrTyG t x0 d x m} {wP : PrimTyG t} {k : ℕ}
    {F : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))} {f : PS S 1 d} (h : IsGermG t x0 d x A.act e wP k F f)
    {m n : ℕ} {y : (jOG x0 d m n).left} {J} (hJ : Good t.PP.L y J) (u : Q S d n) :
    sval (φ := fun _ : Fin 1 => (snd (Over.mk x0) t.G).left) (ε := fun _ => (k : ℤ)) F
        (lift (jBaseG x0 d m n) (PP m x u)).left y J =
      VV m y (sb ![u] f) * ((val wP (PP m x u).left y J * ee x e y J u (ac (AQ A H.w0) u)) ^ k).val := by
  obtain ⟨F', τ, h1, h2, h3⟩ := h m
  have v := sval_valueAt h3 (Formalism.L2.Pj.homAt x0 (jQ m ![u])).left hJ
  rw [sval_pull h1 _ hJ] at v
  have e1 : ((Formalism.L2.Pj.homAt x0 (jQ m ![u])).left ≫ (ptSecT t.G (x m)).left) ≫ (jBaseG x0 d m 1 ▷ t.G).left =
      (lift (jBaseG x0 d m n) (PP m x u)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext1
    · simp only [Category.assoc, whiskerRight_fst, ptSecT, lift_fst_assoc, Category.id_comp, lift_fst]
      exact Over.OverMorphism.ext (spMap_comp_alg _)
    · simp only [Category.assoc, whiskerRight_snd, ptSecT, lift_snd, PP]
  rw [e1] at v
  have e₀ := val_peG x hJ e ![u] ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (A.act H.w0 j)]
    (gen 0) (ac (AQ A H.w0) (gen 0)) (by rintro ⟨l, j⟩; fin_cases l; exacts [hX 0 j, hA _ 0 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [MvPolynomial.constantCoeff_X _ _, (cc_psIn d m _ _).trans (A.const _ j)])
  rw [sq_ac, sq_gen] at e₀
  refine v.trans (congrArg₂ (· * ·) ?_ (congrArg Units.val ((val_corr hJ h2 _).trans ((map_pow _ _ _).trans
    (congrArg (· ^ k) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) e₀)))))))
  rw [VV, ← jQ_psJet]
  refine Eq.trans ?_ (cst_comp (𝟙 _) (jQ m ![u] : Jet S (Fin 1 × Fin d) m →+* Jet S (Fin n × Fin d) m) y _)
  rw [Category.id_comp]; rfl

theorem exists_ratio (Φ : Q S d 1) (hco : ∀ m n (u : Q S d n), PP m x' u = PP m x (ac Φ u))
    (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x0 d x' m) (he : ∀ m, (e m).IsGen) (he' : ∀ m, (e' m).IsGen)
    (m : ℕ) : ∃ ε : PS S 2 d, IsUnit (MvPowerSeries.constantCoeff ε) ∧
      ∀ n (y : (jOG x0 d m n).left) J, Good t.PP.L y J → ∀ u v : Q S d n,
        VV m y (E2 ε u v) = (ee x' e' y J u v * (ee x e y J (ac Φ u) (ac Φ v))⁻¹).val := by
  let b : Fin 2 → Q S d 2 := ![ac Φ (gen 0), ac Φ (gen 1)]
  have hfam : cφG t ![jptG t x0 d x' m (0 : Fin 2), jptG t x0 d x' m (1 : Fin 2)] =
      fun I => (Formalism.L2.Pj.homAt x0 (jQ m b)).left ≫
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
    funext I
    rw [cφG, cφG, ← Over.comp_left, FrameRatio.comp_psum']
    congr 2
    funext k
    fin_cases k
    · show jptG t x0 d x' m 0 = _ ≫ jptG t x0 d x m 0
      rw [PP_gen, PP_gen, PP_sq, sq_gen, hco]; rfl
    · show jptG t x0 d x' m 1 = _ ≫ jptG t x0 d x m 1
      rw [PP_gen, PP_gen, PP_sq, sq_gen, hco]; rfl
  obtain ⟨U, hU⟩ := FrameRatio.exists_corr_scaled t.PP.L t.PP.isLB _ _ hfam (cε 2) (e' m)
    (LB.pullGen t.PP.L _ _ (e m) (Formalism.L2.Pj.homAt x0 (jQ m b)).left) (he' m) (DVR.pullGen_isGen _ _ _ _ (he m) _)
  obtain ⟨u, rfl⟩ := FrameRatio.unitΓ_surj U
  obtain ⟨ε, hε⟩ := FrameRatio.psJet_surj m (u : Jet S (Fin 2 × Fin d) m)
  refine ⟨ε, ?_, fun n y J hJ p q => ?_⟩
  · rw [← GaugeR.jetAug_psJet m ε, hε]
    exact u.isUnit.map _
  · have e₀ : val (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (Formalism.L2.Pj.homAt x0 (jQ m b)).left) (Formalism.L2.Pj.homAt x0 (jQ m ![p, q])).left y J =
        ee x e y J (ac Φ p) (ac Φ q) := by
      refine (val_pull hJ _ _ _).trans ?_
      rw [← Over.comp_left, GermD.homAt_comp, jQ_comp]
      refine congrArg (fun a => val (L := t.PP.L)
        (φ := cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (ε := cε 2) (e m)
        (Formalism.L2.Pj.homAt x0 (jQ m a)).left y J) (funext fun j => ?_)
      fin_cases j
      · exact (sq_ac _ _ _).trans (congrArg (ac Φ) (sq_gen _ _))
      · exact (sq_ac _ _ _).trans (congrArg (ac Φ) (sq_gen _ _))
    have k : ee x' e' y J p q = _ := (val_corr hJ hU (Formalism.L2.Pj.homAt x0 (jQ m ![p, q])).left).trans
      ((val_scale hJ (unitΓ u) _ _).trans (congrArg₂ (· * ·) rfl e₀))
    exact (gm_unit (y := y) u ![p, q] _ hε.symm).symm.trans (congrArg Units.val (eq_mul_inv_of_mul_eq k.symm))

theorem jeq_of_VV (t : SAB H X0) (x0 : Sp S ⟶ X0) {m n : ℕ} {f g : PS S n d}
    (h : ∀ (y : (jOG x0 d m n).left) J, Good t.PP.L y J → VV m y f = VV m y g) : JEq m f g :=
  RatioPh1.jeq_of_psJet (cst_ext fun y => by
    choose J hJ using fun ψ : (jOG x0 d m n).left ⟶ t.G.left => exists_chart t.PP.isLB (ψ y)
    exact h y J hJ)

theorem exists_jRel [StarRing (𝓞 E)] (hstar : ∀ a : 𝓞 E, star a = H.bar a)
    (hs : Function.Surjective (t.G ⊗ t.G).hom.appTop.hom) (B B' : FB S d (𝓞 E)) {κ : Type} [Fintype κ]
    {tg tg' : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uv uv' : κ → Fin d → S}
    (hc : IsChartG t x0 d B.G.F B.A.act tg uv x) (hc' : IsChartG t x0 d B'.G.F B'.A.act tg' uv' x')
    {e : ∀ m, FrTyG t x0 d x m} {e' : ∀ m, FrTyG t x0 d x' m}
    (hf : IsFrameG t x0 d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e)
    (hf' : IsFrameG t x0 d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e')
    (Φ Ψ : Q S d 1) (hinv : IsInvPair Φ.1 Ψ.1) (hco : ∀ m n (u : Q S d n), PP m x' u = PP m x (ac Φ u))
    (hl : ∀ i, B'.G.F i = transF B.G.F Φ.1 Ψ.1 i) (hact : ∀ a, B'.A.act a = comp1 Ψ.1 (comp1 (B.A.act a) Φ.1))
    (wP : PrimTyG t) (m : ℕ) :
    ∃ ε : PS S 2 d, JRel m B B' Φ.1 Ψ.1 ε ∧
      ∀ (k : ℕ) (F : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))) (f f' : PS S 1 d),
        IsGermG t x0 d x B.A.act e wP k F f → IsGermG t x0 d x' B'.A.act e' wP k F f' →
        JEq m (ev ![Φ.1] f) (f' * ev (n := 1) ![pt S d 0, comp1 (B'.A.act H.w0) (pt S d 0)] ε ^ k) := by
  obtain ⟨ε, hε, hE⟩ := exists_ratio Φ hco e e' hf.gen hf'.gen m
  have hΦΨ : ac Φ Ψ = gen 0 := Subtype.ext ((ac_val Φ Ψ).trans hinv.2.2.1)
  have hA : ∀ (b : 𝓞 E) {n} (u : Q S d n), ac Φ (ac (AQ B'.A b) u) = ac (AQ B.A b) (ac Φ u) := fun b n u => by
    have : AQ B'.A b = ac Ψ (ac (AQ B.A b) Φ) := Subtype.ext (by rw [ac_val, ac_val]; exact hact b)
    rw [this, FrameRatioAdj.ac_ac, FrameRatioAdj.ac_ac, ← FrameRatioAdj.ac_ac Φ Ψ, hΦΨ]
    exact sq_gen _ _
  have g2 : ∀ f : PS S 2 d, ev (n := 2) ![pt S d 0, pt S d 1] f = f := fun f =>
    (formalSeriesValueAtTwoPoints_eq_ev f (gen 0) (gen 1)).symm.trans (formalSeriesValueAtTwoPoints_genericPoints f)
  refine ⟨ε, ⟨hinv, hε, hl, hact, ?_, ?_, ?_, fun a => ?_⟩, fun k F f f' hg hg' => ?_⟩
  · have := jeq_of_VV t x0 (m := m)
      (f := E3 B'.ph1 (gen 0 : Q S d 3) (gen 1) (gen 2) * E2 ε (op (FQ B'.G) (gen 0) (gen 1)) (gen 2))
      (g := E3 B.ph1 (ac Φ (gen 0 : Q S d 3)) (ac Φ (gen 1)) (ac Φ (gen 2)) *
        (E2 ε (gen 0) (gen 2) * E2 ε (gen 1) (gen 2))) fun y J hJ => by
      simp only [VV_mul, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_first_partial_law hJ hf', hE _ y J hJ, ← Units.val_mul, hco,
        RatioPh1.ac_op_trans Φ Ψ hinv.2.2.1 hl]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [formalSeriesValueAtThreePoints_genericPoints] at this
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val] using this
  · have := jeq_of_VV t x0 (m := m)
      (f := E3 B'.ph2 (gen 0 : Q S d 3) (gen 1) (gen 2) * E2 ε (gen 0) (op (FQ B'.G) (gen 1) (gen 2)))
      (g := E3 B.ph2 (ac Φ (gen 0 : Q S d 3)) (ac Φ (gen 1)) (ac Φ (gen 2)) *
        (E2 ε (gen 0) (gen 1) * E2 ε (gen 0) (gen 2))) fun y J hJ => by
      simp only [VV_mul, frame_biext_dictionary_second_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf', hE _ y J hJ, ← Units.val_mul, hco,
        RatioPh1.ac_op_trans Φ Ψ hinv.2.2.1 hl]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [formalSeriesValueAtThreePoints_genericPoints] at this
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val] using this
  · have := jeq_of_VV t x0 (m := m) (f := E2 B'.sy (gen 0 : Q S d 2) (gen 1) * E2 ε (gen 0) (gen 1))
      (g := E2 B.sy (ac Φ (gen 0 : Q S d 2)) (ac Φ (gen 1)) * E2 ε (gen 1) (gen 0)) fun y J hJ => by
      simp only [VV_mul, dict_sy hJ hf, dict_sy hJ hf', hE _ y J hJ, ← Units.val_mul]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtTwoPoints_eq_ev, ac_val, ac_val] at this
    exact this
  · obtain ⟨w, hw, hU⟩ := hf.ad a
    obtain ⟨w', hw', hU'⟩ := hf'.ad a
    obtain ⟨U, h₁, h₂⟩ := hU m
    obtain ⟨U', h₁', h₂'⟩ := hU' m
    obtain ⟨c₀, hc₀⟩ := exists_const t.PP.L t.PP.isLB (t.G ⊗ t.G).hom hs
      (LB.mulGen t.PP.L _ _ _ _ w' (LB.invGen t.PP.L _ _ w))
      (mulGen_isGen _ _ _ _ _ _ _ hw' (invGen_isGen _ _ _ _ hw)) (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    have := jeq_of_VV t x0 (m := m)
      (f := E2 (B'.ad a) (gen 0 : Q S d 2) (gen 1) * E2 ε (gen 0) (ac (AQ B'.A (H.bar a)) (gen 1)))
      (g := E2 (B.ad a) (ac Φ (gen 0)) (ac Φ (gen 1)) * E2 ε (ac (AQ B'.A a) (gen 0)) (gen 1)) fun y J hJ => by
      have dA := dict_ad (A := B.A) (ad := B.ad) hJ a w U h₁ h₂
      have dB := dict_ad (A := B'.A) (ad := B'.ad) hJ a w' U' h₁' h₂'
      have k : ∀ p q : jOG x0 d m 2 ⟶ t.G, (val₂ w' y J p q * (val₂ w y J p q)⁻¹).val =
          gs (jOG x0 d m 2).hom y ⊤ c₀ := fun p q => by
        have := hc₀ _ (lift p q).left y J hJ
        rw [val_mul hJ, val_inv, Over.w] at this
        exact this
      have a₀ := dA 0 0
      have b₀ := dB 0 0
      rw [FrameRatioAdj.formalSeriesValueAtTwoPoints_zero_zero _ (B.adjoint_zero_fst a), VV_one, ac0, ac0, mul_inv_cancel_right, PP_zero hc] at a₀
      rw [FrameRatioAdj.formalSeriesValueAtTwoPoints_zero_zero _ (B'.adjoint_zero_fst a), VV_one, ac0, ac0, mul_inv_cancel_right, PP_zero hc'] at b₀
      have k₁ := Units.ext ((k (PP m x (ac Φ (gen 0))) (PP m x (ac Φ (gen 1)))).trans (k 1 1).symm)
      rw [Units.ext a₀.symm (v := 1), Units.ext b₀.symm (v := 1), mul_inv_cancel, mul_inv_eq_one] at k₁
      simp only [VV_mul, dA, dB, hE _ y J hJ, hA, hco, k₁, ← Units.val_mul]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [hstar a]
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, ac_val, gen_val, g2] using this
  · have := jeq_of_VV t x0 (m := m) (f := sb ![ac Φ (gen 0 : Q S d 1)] f)
      (g := sb ![(gen 0 : Q S d 1)] f' * E2 ε (gen 0) (ac (AQ B'.A H.w0) (gen 0)) ^ k) fun y J hJ => by
      have v := germ_val B.A hg hJ (ac Φ (gen 0))
      have v' := germ_val B'.A hg' hJ (gen 0)
      rw [hco, v] at v'
      have hp : ∀ (g : PS S 1 d) (k : ℕ), VV m y (g ^ k) = VV m y g ^ k := fun g k => by
        induction k with
        | zero => rw [pow_zero, pow_zero, VV_one]
        | succ k ih => rw [pow_succ, pow_succ, VV_mul, ih]
      rw [VV_mul, hp, hE _ y J hJ, hA, ← Units.val_pow_eq_pow_val, (Units.eq_mul_inv_iff_mul_eq _).2 v', _root_.mul_assoc,
        ← Units.val_mul]
      congr 2
      rw [← inv_pow, ← mul_pow]
      congr 1
      refine Additive.ofMul.injective ?_
      simp only [ofMul_mul, ofMul_inv]
      abel
    have e1 : ac Φ (gen 0 : Q S d 1) = Φ := Subtype.ext (funext fun i =>
      (congrArg (sb · (Φ.1 i)) (funext fun j => by fin_cases j; rfl)).trans (sb_gen _))
    have e2 : sb ![(gen 0 : Q S d 1)] f' = f' := (congrArg (sb · f') (funext fun j => by fin_cases j; rfl)).trans (sb_gen _)
    have e3 : sb ![Φ] f = ev ![Φ.1] f := (sb_apply _ _).trans (congrArg (ev · f) (funext fun j => by fin_cases j; rfl))
    rw [e1, e2, e3, formalSeriesValueAtTwoPoints_eq_ev, ac_val, gen_val] at this
    exact this

end GlobalTheory.ChartField
