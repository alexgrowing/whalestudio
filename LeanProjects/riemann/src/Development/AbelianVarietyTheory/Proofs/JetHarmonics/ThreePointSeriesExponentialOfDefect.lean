import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGoodConst
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesExpIntegralCanonGaugeAdditiveSecond

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameGeo

section Geo

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

theorem powGen_isGen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) : (GeneratorPullback.powGen L φ ε t n).IsGen := fun i j => by
  refine ((map_pow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_pow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_pow _ _ _).symm)
  exact (Finset.prod_pow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ =>
    (zpow_natCast _ n).symm.trans ((zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _))))

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

theorem prod_nmul {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) (n : ℕ) {c : U}
    (h : ∏ i, f i ^ e i = c) : ∏ i, f i ^ ((n : ℤ) * e i) = c ^ n := by
  rw [← h, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun _ _ => by rw [mul_comm, zpow_mul, zpow_natCast]

theorem exists_ratio {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(S₀, ⊤), IsUnit a ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs (r ≫ p) z ⊤ a * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z J hJ
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  refine ⟨a, S₀.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ?_, fun Z r z J hJ => ?_⟩
  · choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    have := key _ e y I hI
    rw [he] at this
    exact (congrArg IsUnit ((gs_eq (𝟙 S₀) y ⊤ hy _).symm.trans this.symm)).mpr (Units.isUnit _)
  · rw [← key Z r z J hJ, ← Units.val_mul, inv_mul_cancel_right]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

omit [IsCommMonObj G] in
theorem act_natCast_mul {O : Type} [CommRing O] (act : Geo.Tor.OAct O G) (w : O) (n : ℕ) :
    act.act ((n : O) * w) = act.act w ^ n := by
  induction n with
  | zero =>
    have := act.add 0 0
    rw [add_zero] at this
    rw [Nat.cast_zero, zero_mul, pow_zero]; exact mul_eq_left.1 this.symm
  | succ n ih => rw [Nat.cast_succ, add_mul, _root_.one_mul, act.add, ih, pow_succ]

theorem exists_gen_pull (Lr : RigLB G) (c : CubicalStr G Lr) {O : Type} [CommRing O] [StarRing O]
    (act : Geo.Tor.OAct O G) (a w0 : O) (N : ℕ) (hN : a * star a = (N : O))
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)) (hu : u.IsGen)
    (ρ : LB.Gen (LB.LinComb Lr.L (primφ (act.act w0)) primε)) (hρ : ρ.IsGen) :
    ∃ mu : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, (act.act a).left] ![(N : ℤ), -1]), mu.IsGen ∧
      ∀ (T : Over S) (y : T ⟶ G) (z : T.left) (J), Good Lr.L z J →
        val mu y.left z J * val ρ (y ≫ act.act a).left z J *
          ∏ i ∈ Finset.range N, cubV c z J y (y ≫ act.act ((i : O) * w0)) (y ≫ act.act w0) =
        (val₂ u z J y (y ≫ act.act (w0 * a)))⁻¹ * val ρ y.left z J ^ N := by
  obtain ⟨t, ht, vt⟩ := exists_cubN c (1 : G ⟶ G) (act.act w0) (𝟙 G) N
  obtain ⟨mu, hmu, hv⟩ := exists_gen Lr.isLB (K' := Fin 2) (φ' := ![𝟙 G.left, (act.act a).left])
    (ε' := ![(N : ℤ), -1]) (fun U _ h => by
      have p₁ := prod_prim (act.act w0) (𝟙 G) h
      have p₂ := prod_prim (act.act w0) (act.act a) h
      have p₃ := prod_ros (act.act a) (act.act (star a)) (𝟙 G) (act.act (w0 * a)) h
      have e₁ : act.act (w0 * a) ≫ act.act (star a) = act.act w0 ^ N := by
        rw [← act.mul, _root_.mul_assoc, hN, mul_comm, act_natCast_mul]
      have e₂ : act.act a ≫ act.act w0 = act.act (w0 * a) := by rw [← act.mul, mul_comm]
      rw [e₁] at p₃
      rw [e₂] at p₂
      simp only [Over.id_left, Category.id_comp] at p₁ p₃
      refine (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5 ⊕ Fin 6 ⊕ Fin 8) (U := U) _ (prod_nmul _ _ N p₁)
        (DVR.prod_neg _ _ (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 6 ⊕ Fin 8) (U := U) _ p₂
          (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 8) (U := U) _ p₃ (Fin.prod_univ_eight _))))).trans ?_
      rw [Fin.prod_univ_two]
      simp only [Sum.elim_inr, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [_root_.one_mul (act.act w0 ^ N), _root_.one_mul (𝟙 G), mul_comm (act.act w0 ^ N) (𝟙 G),
        mul_comm (act.act w0) (𝟙 G)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, Over.id_left]
      module)
    (LB.mulGen Lr.L _ _ _ _ (GeneratorPullback.powGen Lr.L _ _ ρ N) (LB.invGen Lr.L _ _
      (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (act.act a).left)
        (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift (𝟙 G) (act.act (w0 * a))).left) t))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hρ N) (DVR.invGen_isGen _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ _)
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) ht))))
  refine ⟨mu, hmu, fun T y z J hJ => ?_⟩
  have C := isCub_cubV c hJ
  have e₁ : cubN (cubV c z J) N (y ≫ 1) (y ≫ act.act w0) (y ≫ 𝟙 G) =
      ∏ i ∈ Finset.range N, cubV c z J y (y ≫ act.act ((i : O) * w0)) (y ≫ act.act w0) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [MonObj.comp_one, _root_.one_mul, Category.comp_id, act_natCast_mul, MonObj.comp_pow, C.s12, C.s01]
  have e₂ : val u (y.left ≫ (lift (𝟙 G) (act.act (w0 * a))).left) z J = val₂ u z J y (y ≫ act.act (w0 * a)) := by
    rw [← Over.comp_left, comp_lift, Category.comp_id]; rfl
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_mul hJ, val_mul hJ, val_powGen, val_pull hJ, val_pull hJ,
    vt T y z J hJ, e₁, e₂, Over.comp_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Geo

section Formal

open GlobalTheory.FramePull ReciprocityTheory.ChartRestriction.G.TB

variable {R : Type} [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

def IsExpOf (w : PS R 1 d) (f : PS k 1 d) : Prop := constantCoeff f = 0 ∧ FB.toK k w = FB.expS k f

theorem IsExpOf.mul {v w : PS R 1 d} {f g : PS k 1 d} (hf : IsExpOf v f) (hg : IsExpOf w g) :
    IsExpOf (v * w) (f + g) := by
  refine ⟨by simp [hf.1, hg.1], ?_⟩
  rw [FB.toK, map_mul]
  unfold FB.expS
  rw [WickVanishing.exp_add hf.1 hg.1]
  exact congrArg₂ (· * ·) hf.2 hg.2

theorem IsExpOf.one : IsExpOf (1 : PS R 1 d) (0 : PS k 1 d) := by
  refine ⟨map_zero _, ?_⟩
  unfold FB.expS
  rw [FB.toK, map_one, WickVanishing.exp_zero]

theorem IsExpOf.neg {v w : PS R 1 d} {f : PS k 1 d} (hf : IsExpOf v f) (hw : v * w = 1) : IsExpOf w (-f) := by
  have n0 : constantCoeff (-f) = 0 := by simp [hf.1]
  refine ⟨n0, ?_⟩
  have h1 : FB.toK k v * FB.toK k w = 1 := by rw [FB.toK, FB.toK, ← map_mul, hw, map_one]
  have h2 : FB.expS k (-f) * FB.expS k f = 1 := by
    unfold FB.expS
    rw [← WickVanishing.exp_add n0 hf.1, neg_add_cancel, WickVanishing.exp_zero]
  rw [hf.2] at h1
  calc FB.toK k w = (FB.expS k (-f) * FB.expS k f) * FB.toK k w := by rw [h2, _root_.one_mul]
    _ = FB.expS k (-f) := by rw [_root_.mul_assoc, h1, _root_.mul_one]

theorem isExpOf_ev {m : ℕ} {a : Fin m → Pt R 1 d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    {w : PS R m d} {f : PS k m d} (f0 : constantCoeff f = 0) (hw : FB.toK k w = FB.expS k f) :
    IsExpOf (ev a w) (ev (fun j i => FB.toK k (a j i)) f) := by
  have ha' : ∀ j i, constantCoeff (FB.toK k (a j i)) = 0 := fun j i => by simp [FB.toK, ha]
  refine ⟨by rw [constantCoeff_ev_eq ha', f0], ?_⟩
  have e1 : FB.toK k (ev a w) = ev (fun j i => FB.toK k (a j i)) (FB.toK k w) := map_ev_eq _ ha w
  rw [e1, hw]
  unfold ev FB.expS
  exact WickVanishing.subst_exp (fun p : Fin m × Fin d => FB.toK k (a p.1 p.2)) (fun p => ha' p.1 p.2) f0

variable {O : Type} [CommRing O] [StarRing O] {B : FB R d O} {h : PS k 2 d}

theorem isExpOf_ad (hh : B.IsCanonGauge k h) (a b c : O) :
    IsExpOf (ev ![B.A.act b, B.A.act c] (B.ad a))
      (ev ![B.actK k (a * b), B.actK k c] h - ev ![B.actK k b, B.actK k (star a * c)] h) := by
  have p0 : ∀ {n : ℕ} (j : Fin n) (i : Fin d), constantCoeff (pt k d j i) = 0 := constantCoeff_point
  have c0 : ∀ (e : O) (j : Fin 2) (i : Fin d), constantCoeff (comp1 (B.actK k e) (pt k d j) i) = 0 :=
    fun e j => constantCoeff_comp1 (constantCoeff_actK B e) (p0 j)
  have key := isExpOf_ev (cz2 (B.A.const b) (B.A.const c)) (by
    rw [map_sub, constantCoeff_ev_eq (cz2 (c0 a 0) (p0 1)), constantCoeff_ev_eq (cz2 (p0 0) (c0 _ 1)),
      sub_self]) (hh.ad a)
  have e : (fun j i => FB.toK k ((![B.A.act b, B.A.act c] : Fin 2 → Pt R 1 d) j i)) =
      ![B.actK k b, B.actK k c] := by
    funext j; fin_cases j <;> rfl
  have hb := cz2 (constantCoeff_actK (k := k) B b) (constantCoeff_actK (k := k) B c)
  rw [e, ev_minus hb, germEv_germEv_two_points (c0 a 0) (p0 1) hb, germEv_germEv_two_points (p0 0) (c0 _ 1) hb, ev_comp1 _ (p0 0) hb,
    ev_comp1 _ (p0 1) hb, ev_point_fun hb, ev_point_fun hb] at key
  rw [actK_mul, actK_mul]
  exact key

theorem isExpOf_canonical_gauge (hh : B.IsCanonGauge k h) (b c c' : O) :
    IsExpOf (ev ![B.A.act b, B.A.act c, B.A.act c'] B.ph2)
      (ev ![B.actK k b, B.actK k c] h + ev ![B.actK k b, B.actK k c'] h -
        ev ![B.actK k b, B.actK k (c + c')] h) := by
  have p0 : ∀ {n : ℕ} (j : Fin n) (i : Fin d), constantCoeff (pt k d j i) = 0 := constantCoeff_point
  have c0 : ∀ (i : Fin d), constantCoeff (addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2) i) = 0 :=
    constantCoeff_addOf (constantCoeff_FK B) (p0 1) (p0 2)
  have h0 : constantCoeff h = 0 := by
    rw [← constantCoeff_ev_eq (cz2 (x := (0 : Pt k 1 d)) (fun _ => by simp) (constantCoeff_point 0)),
      hh.ax0, map_zero]
  have key := isExpOf_ev (cz3 (B.A.const b) (B.A.const c) (B.A.const c')) (by
    rw [map_sub, map_add, constantCoeff_ev_eq (cz2 (p0 0) (p0 1)), constantCoeff_ev_eq (cz2 (p0 0) (p0 2)),
      constantCoeff_ev_eq (cz2 (p0 0) c0), h0]
    simp) hh.ph2
  have e : (fun j i => FB.toK k ((![B.A.act b, B.A.act c, B.A.act c'] : Fin 3 → Pt R 1 d) j i)) =
      ![B.actK k b, B.actK k c, B.actK k c'] := by
    funext j; fin_cases j <;> rfl
  have hb := cz3 (constantCoeff_actK (k := k) B b) (constantCoeff_actK (k := k) B c)
    (constantCoeff_actK (k := k) B c')
  rw [e, ev_minus hb, ev_plus hb, germEv_germEv_two_points (p0 0) (p0 1) hb, germEv_germEv_two_points (p0 0) (p0 2) hb, germEv_germEv_two_points (p0 0) c0 hb,
    ev_addOf _ (p0 1) (p0 2) hb, ev_point_fun hb, ev_point_fun hb, ev_point_fun hb] at key
  rw [actK_add]
  exact key

theorem isExpOf_prod (hh : B.IsCanonGauge k h) (b c : O)
    (hQ : ev ![B.A.act b, B.A.act 0, B.A.act 0] B.ph2 = 1) (n : ℕ) :
    IsExpOf (∏ i ∈ Finset.range n, ev ![B.A.act b, B.A.act ((i : O) * c), B.A.act c] B.ph2)
      ((n : k) • ev ![B.actK k b, B.actK k c] h - ev ![B.actK k b, B.actK k ((n : O) * c)] h) := by
  induction n with
  | zero =>
    have h0 := isExpOf_canonical_gauge hh b 0 0
    rw [hQ, add_zero, add_sub_cancel_right] at h0
    have e : ev ![B.actK k b, B.actK k 0] h = 0 :=
      WickVanishing.eq_zero_of_exp_eq_one h0.1 (h0.2.symm.trans (map_one _))
    rw [Finset.prod_range_zero, Nat.cast_zero, Nat.cast_zero, zero_smul, zero_mul, e, sub_zero]
    exact IsExpOf.one
  | succ j ih =>
    have := ih.mul (isExpOf_canonical_gauge hh b ((j : O) * c) c)
    rw [Finset.prod_range_succ]
    convert this using 1
    rw [Nat.cast_succ, Nat.cast_succ, add_smul, one_smul, add_mul, _root_.one_mul]
    ring

end Formal

section Key

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer.FBOf

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem series_ext_one (hJet : JetAlgSt) (hRep : RepSt) (Lr : RigLB G) (c : CubicalStr G Lr) {O : Type} [CommRing O]
    [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G)
    (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε))
    {d : ℕ} (x : Fam G (Fin d)) (hx : IsUnivChart G d x) (j : Lr.L.ι) (B : FB R d O) (hB : IsFBOf Lr c act u x j B)
    (g g' : PS R 1 d)
    (H : ∀ (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J : (T.left ⟶ G.left) → Lr.L.ι), Good Lr.L z J →
      ∀ (Φ : PS R 1 d →+* T.left.presheaf.stalk z) (y : T ⟶ G),
      (∀ r : R, Φ (C r) = gs T.hom z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) →
      (∀ (K : Type) [Fintype K] (φ : K → (G.left ⟶ G.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb Lr.L φ ε))
        (s : PS R 1 d), IsSer1 x _ (t.s (fun _ => j)).val s → ∀ a,
          Φ (ev ![B.A.act a] s) = (val t (y ≫ act.act a).left z J).val) →
      (∀ a b e, Φ (ev ![B.A.act a, B.A.act b, B.A.act e] B.ph2) =
        (cubV c z J (y ≫ act.act a) (y ≫ act.act b) (y ≫ act.act e)).val) →
      (∀ o a b, Φ (ev ![B.A.act a, B.A.act b] (B.ad o)) =
        (val₂ (u o) z J (y ≫ act.act a) (y ≫ act.act b))⁻¹.val) → Φ g = Φ g') :
    g = g' := by
  classical
  obtain ⟨j1, -, j3, -⟩ := hJet R (Fin 1 × Fin d)
  obtain ⟨r1, -⟩ := hRep R G d x hx (Fin 1 × Fin d)
  obtain ⟨Y, hY, -⟩ := r1 (pt R (n := 1) d 0) (gp_pt 0)
  have hA : ∀ a, Rep x (B.A.act a) (fun m => Y m ≫ act.act a) := fun a => by
    have := (hB.map a).2 1 _ _ hY
    rwa [gt_comp1_pt_right] at this
  refine j3 g g' fun m => ?_
  obtain ⟨τ, hτ, -⟩ := j1 m
  refine eq_of_germ fun z => ?_
  obtain ⟨J, hJ, hJ'⟩ := exists_good_const Lr.L Lr.isLB j z
  rw [← hτ, ← hτ]
  refine H (sp (R₀ := R) (JetR R (Fin 1 × Fin d) m)) z J hJ
    ((((Spec (CommRingCat.of (JetR R (Fin 1 × Fin d) m))).presheaf.germ ⊤ z trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (JetR R (Fin 1 × Fin d) m))).inv.hom).comp τ.toRingHom)
    (Y m) (fun r => ?_) (fun K _ φ ε t s hs a => ?_) (fun a b e => ?_) (fun o a b => ?_)
  · rw [gs_eq _ z ⊤ trivial]
    have e₁ : τ (C r) = algebraMap R _ r := τ.commutes r
    have e₂ := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap R (JetR R (Fin 1 × Fin d) m))))
    exact congrArg _ ((congrArg _ e₁).trans e₂)
  · obtain ⟨h1, h2⟩ := hs 1 _ _ (hA a) m
    refine Eq.trans ?_ (congrArg Units.val (val_const hJ' t _ h1)).symm
    refine Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h2.symm))
  · obtain ⟨h1, h2⟩ := hB.ph1 1 _ _ _ _ _ _ (hA a) (hA b) (hA e) m
    rw [hB.ph2]
    refine Eq.trans ?_ (congrArg Units.val (val_const (L := Lr.L) (φ := thφ G (x3 G)) (ε := thε) hJ' c.t _ h1)).symm
    refine Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h2.symm))
  · obtain ⟨h1, h2⟩ := hB.ad o 1 _ _ _ _ (hA a) (hA b) m
    refine Eq.trans ?_ (congrArg (fun q => q⁻¹.val) (val_const hJ' (u o) _ h1)).symm
    refine Eq.trans ?_ (congrArg Units.val (map_inv _ _))
    refine Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h2.symm))

end Key

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (isCub_cubV cubV val₂) in

theorem frame_pullback_geo : JetAlgSt → RepSt → SerSt → SerExSt → RosIdSt → ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Function.Surjective G.hom.appTop.hom → Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)), (∀ a, IsNormRos Lr.L _ _ (u a)) → ∀ (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x → ∀ j : Lr.L.ι, ⊤ ≤ η[G].left ⁻¹ᵁ Lr.L.U j → ∀ B : FB R d O, IsFBOf Lr c act u x j B → ∀ (w0 : O) (ρ : LB.Gen (LB.LinComb Lr.L (primφ (act.act w0)) primε)), ρ.IsGen → ∀ (a : O) (N : ℕ), a * star a = (N : O) → (∃ mu : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, (act.act a).left] ![(N : ℤ), -1]), mu.IsGen) ∧ ∀ mu : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, (act.act a).left] ![(N : ℤ), -1]), mu.IsGen → ∀ M r : PS R 1 d, IsSer1 x _ (mu.s (fun _ => j)).val M → IsSer1 x _ (ρ.s (fun _ => j)).val r → ∃ (w : PS R 1 d) (κ : Rˣ), w * r ^ N = C (κ : R) * M * ev (n := 1) ![B.A.act a] r ∧ ∀ (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d), B.IsCanonGauge k h → FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) := by
  intro hJet hRep _ _ _ R _ G _ _ s1 _ _ Lr c O _ _ act u hu d x hx j _ B hB w0 ρ hρ a N hN
  obtain ⟨mu₀, h₀, v₀⟩ := exists_gen_pull Lr c act a w0 N hN (u a) (hu a).1 ρ hρ
  refine ⟨⟨mu₀, h₀⟩, fun mu hmu M r hM hr => ?_⟩
  obtain ⟨α, hα, vα⟩ := exists_ratio Lr.isLB G.hom η[G].left (Over.w η[G]) s1 h₀ hmu
  have E := series_ext_one hJet hRep Lr c act u x hx j B hB
  have hκ : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom α) := hα.map _
  have e1 : ∀ s : PS R 1 d, ev ![B.A.act 1] s = s := fun s => by
    rw [B.A.one_act]
    have : (![pt R d 0] : Fin 1 → Pt R 1 d) = fun j => pt R d j := by
      funext j; fin_cases j; rfl
    rw [this, FBOf.ev_self]
  have a0 : act.act 0 = 1 := by simpa using act_natCast_mul act 0 0
  have hQ : ev ![B.A.act 1, B.A.act 0, B.A.act 0] B.ph2 = 1 := E _ _ fun T z J hJ Φ y _ _ p _ => by
    rw [p, a0, MonObj.comp_one, (isCub_cubV c hJ).face₂, map_one, Units.val_one]
  have w1 : constantCoeff B.ph2 = 1 := by
    rw [← FramePull.constantCoeff_ev_eq (FramePull.cz3 (x := (0 : Pt R 2 d)) (fun _ => by simp)
      (FramePull.constantCoeff_point 0) (FramePull.constantCoeff_point 1)), B.cocycleRight_zero_fst, map_one]
  obtain ⟨P, hP⟩ : ∃ P : PS R 1 d,
      P = ∏ i ∈ Finset.range N, ev ![B.A.act 1, B.A.act ((i : O) * w0), B.A.act w0] B.ph2 := ⟨_, rfl⟩
  have P1 : constantCoeff P = 1 := by
    rw [hP, map_prod]
    exact Finset.prod_eq_one fun i _ => by
      rw [FramePull.constantCoeff_ev_eq (FramePull.cz3 (B.A.const _) (B.A.const _) (B.A.const _)), w1]
  have PQ : P * invOfUnit P 1 = 1 := mul_invOfUnit P 1 (by simpa using P1)
  have main : ev ![B.A.act 1, B.A.act (w0 * a)] (B.ad a) * r ^ N =
      C (hκ.unit : R) * M * ev (n := 1) ![B.A.act a] r * P := E _ _ fun T z J hJ Φ y q₀ q₁ q₃ q₂ => by
    have m₁ := q₁ _ _ _ mu M hM 1
    have m₂ := q₁ _ _ _ ρ r hr 1
    rw [e1, act.one, Category.comp_id] at m₁ m₂
    have eα : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (hκ.unit : R) = α :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply α
    have v := congrArg Units.val (v₀ T y z J hJ)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, vα _ _ z J hJ, Over.w, Units.val_pow_eq_pow_val,
      Units.coe_prod] at v
    rw [map_mul, map_mul, map_mul, map_mul, map_pow, hP, map_prod, q₀, q₂, q₁ _ _ _ ρ r hr, m₁, m₂, eα, act.one,
      Category.comp_id, ← v]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [q₃, act.one, Category.comp_id]
  refine ⟨ev ![B.A.act 1, B.A.act (w0 * a)] (B.ad a) * invOfUnit P 1, hκ.unit, ?_, fun k _ _ _ h hh => ?_⟩
  · rw [mul_right_comm, main, _root_.mul_assoc _ P, PQ, _root_.mul_one]
  · have h1 := isExpOf_ad hh a 1 (w0 * a)
    have h2 := isExpOf_prod hh 1 w0 hQ N
    rw [← hP] at h2
    have e : star a * (w0 * a) = (N : O) * w0 := by rw [← hN]; ring
    rw [e, _root_.mul_one] at h1
    have h3 := (h1.mul (h2.neg PQ)).2
    rw [FramePull.ev_actK_hL, FramePull.hL_eq, h3]
    congr 1
    ring

end GlobalTheory.FrameGeo
