import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Definitions.Jets.SurjectiveAppTopSqCube
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThreePointSeriesExponentialOfDefect
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullGerm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt FB ev pt)
open GlobalTheory.FieldBaseChange (constVal gs_scal)

section Geo

theorem sec_ext_of_inj {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hinj : ∀ W : Y.Opens, Function.Injective (h.app W))
    (H : ∀ y J, Good L y J → sval s (𝟙 Y' ≫ h) y J = sval s' (𝟙 Y' ≫ h) y J) (j : K → L.ι) : s.f j = s'.f j := by
  refine hinj _ (fn_ext fun y hy => ?_)
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j := hy
  have m := hJ'.mem φ (𝟙 Y' ≫ h)
  refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
  exact (sec_trans s _ y hy' m).trans ((congrArg _ (H y J hJ')).trans (sec_trans s' _ y hy' m).symm)

theorem exists_norm {S : Scheme.{0}} {G : Over S} [GrpObj G] (Lr : RigLB G) (f : G ⟶ G) [IsMonHom f] {N : ℕ}
    (hN : 1 ≤ N) (mu : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, f.left] ![(N : ℤ), -1])) (hmu : mu.IsGen) :
    ∃ mu' : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, f.left] ![(N : ℤ), -1]), mu'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good Lr.L z J →
        val mu' (r ≫ eSec G) z J = val (GeneratorPullback.powGen Lr.L _ _ Lr.rig (N - 1)) r z J := by
  have he : eSec G ≫ f.left = eSec G := by
    simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨t, ht, vt⟩ := exists_gen Lr.isLB (K' := PUnit) (φ' := fun _ => eSec G)
    (ε' := fun _ => ((N - 1 : ℕ) : ℤ) * 1) (fun U _ g => by
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, he, Finset.univ_unique,
        Finset.prod_singleton]
      rw [← zpow_add]
      congr 1
      omega)
    (LB.pullGen Lr.L _ _ mu (eSec G)) (DVR.pullGen_isGen _ _ _ _ hmu _)
  obtain ⟨c, hc, vc⟩ := FrameGeo.exists_ratio Lr.isLB (𝟙 _) (𝟙 _) (Category.comp_id _)
    (by rw [Scheme.Hom.id_appTop]; exact Function.surjective_id)
    (FrameGeo.powGen_isGen Lr.L _ _ Lr.rig Lr.rigGen (N - 1)) ht
  refine ⟨scaleGen (hc.map G.hom.appTop.hom).unit mu, scaleGen_isGen _ _ hmu, fun Z r z J hJ => Units.ext ?_⟩
  refine Eq.trans ?_ (vc Z r z J hJ).symm
  rw [vt Z r z J hJ, val_pull hJ]
  refine (congrArg Units.val ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_res (r ≫ eSec G) z le_top (hJ.mem _ (r ≫ eSec G)) _) rfl))).trans ?_
  refine congrArg₂ (· * ·) ?_ rfl
  refine (gs_unit (r ≫ eSec G) z ⊤ trivial _).symm.trans ((gs_pull (r ≫ eSec G) G.hom z ⊤ trivial c).trans ?_)
  rw [Category.assoc, show eSec G ≫ G.hom = 𝟙 _ from Over.w η[G]]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

omit [IsDomain V] [IsDiscreteValuationRing V] [GrpObj G] [IsCommMonObj G] in
theorem endK_gK (f : G ⟶ G) : endK f ≫ gK = gK ≫ f.left := pullback.lift_fst _ _ _

omit [IsDomain V] [IsDiscreteValuationRing V] [IsCommMonObj G] in

theorem exists_generic (Lr : RigLB G) (f : G ⟶ G) (N k : ℕ)
    (mu : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, f.left] ![(N : ℤ), -1])) (hmu : mu.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (J), Good Lr.L z J →
      val mu (r ≫ eSec G) z J = val (GeneratorPullback.powGen Lr.L _ _ Lr.rig (N - 1)) r z J) :
    ∃ u : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)]), u.IsGen ∧
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u unitK)
        (LB.pullGen Lr.L _ _ (GeneratorPullback.powGen Lr.L _ _ Lr.rig (k * (N - 1))) (jK V)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G.hom (jK V)) (z : Z) (J), Good Lr.L z J →
        val u r z J = val mu (r ≫ gK) z J ^ k := by
  obtain ⟨u, hu, vu⟩ := exists_gen Lr.isLB (K' := Fin 2) (φ' := ![gK, endK f ≫ gK])
    (ε' := ![((k * N : ℕ) : ℤ), -(k : ℤ)]) (fun U _ g => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, endK_gK, Nat.cast_mul, mul_neg,
        _root_.mul_one])
    (LB.pullGen Lr.L _ _ (GeneratorPullback.powGen Lr.L _ _ mu k) gK)
    (DVR.pullGen_isGen _ _ _ _ (FrameGeo.powGen_isGen _ _ _ _ hmu k) _)
  have vu' : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G.hom (jK V)) (z : Z) (J), Good Lr.L z J →
      val u r z J = val mu (r ≫ gK) z J ^ k := fun Z r z J hJ => by
    rw [vu Z r z J hJ, val_pull hJ, FrameGeo.val_powGen]
  refine ⟨u, hu, corr_of_val Lr.isLB fun y J hJ => ?_, vu'⟩
  have e : (𝟙 _ ≫ unitK) ≫ (gK : _ ⟶ G.left) = (𝟙 _ ≫ jK V) ≫ eSec G := by
    rw [Category.id_comp, Category.id_comp]; exact pullback.lift_fst _ _ _
  rw [val_pull hJ, val_pull hJ, vu' _ _ y J hJ, e, hn _ _ y J hJ, FrameGeo.val_powGen, FrameGeo.val_powGen,
    ← pow_mul, mul_comm]

omit [IsDiscreteValuationRing V] [GrpObj G] [IsCommMonObj G] in

theorem sval_of_generic [Flat G.hom] {L : LB G.left} (hL : L.IsLB) (f : G ⟶ G) (N k : ℕ)
    (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, f.left] ![(N : ℤ), -1])) (hmu : mu.IsGen)
    (σ : H0 L k) (σ' : H0 L (k * N)) (t : V)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G.hom (jK V)) (z : Z) (J), Good L z J →
      sval σ' (r ≫ gK) z J = constVal (r ≫ pullback.snd G.hom (jK V) ≫ jK V) z t *
        (sval σ ((r ≫ endK f) ≫ gK) z J * (val mu (r ≫ gK) z J ^ k).val))
    (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J) (hJ : Good L z J) :
    sval σ' r z J = constVal (r ≫ G.hom) z t * (sval σ (r ≫ f.left) z J * (val mu r z J).val ^ k) := by
  have hk := FrameGeo.powGen_isGen _ _ _ _ hmu k
  obtain ⟨τ, hτ⟩ := exists_sec hL (φ' := fun _ : Fin 1 => 𝟙 G.left) (ε' := fun _ => ((k * N : ℕ) : ℤ))
    (fun W _ g => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg, _root_.mul_one, zpow_neg,
        Category.comp_id, Nat.cast_mul]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec σ f.left _ hk)
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good L z J →
      sval (SecOps.secScale (scal G.hom t) τ) r z J =
        constVal (r ≫ G.hom) z t * (sval σ (r ≫ f.left) z J * (val mu r z J).val ^ k) := fun Z r z J hJ => by
    rw [PullExpField.sval_secScale _ _ _ _ hJ, gs_scal, hτ Z r z J hJ, sval_pullMulSec _ _ _ hk r z hJ,
      FrameGeo.val_powGen, Units.val_pow_eq_pow_val]
  have : IsDominant (jK V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK V)
  have e := sec_ext_of_inj hL (s := σ') (s' := SecOps.secScale (scal G.hom t) τ)
    (h := (gK : pullback G.hom (jK V) ⟶ G.left)) (fun W => (pullback.fst G.hom (jK V)).app_injective W)
    (fun y J hJ => by
      rw [H _ _ y J hJ, v _ _ y J hJ, Units.val_pow_eq_pow_val]
      simp only [Category.assoc, endK_gK, pullback.condition])
  exact (congrArg (gs r z _) (e _)).trans (v Z r z J hJ)

end Geo

section Series

open GlobalTheory.JetSer GlobalTheory.JetSer.FBOf ReciprocityTheory.ChartRestriction.G.Chart

theorem gs_eq_germ_fnVal {A : Type} [CommRing A] {X : Scheme.{0}} (r : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ r ⁻¹ᵁ U) (a : Γ(X, U)) (z : Spec (CommRingCat.of A)) :
    gs r z U a = ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (fnVal r U a)) := by
  rw [gs_eq r z U (h trivial), fnVal, dif_pos h]
  have e : ∀ b, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b) = b :=
    fun b => congrArg (fun q => q.hom b) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id
  rw [e]
  exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of A)).presheaf (homOfLE h) z trivial _).symm

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ}

theorem ev_pt_zero (s : PS R 1 d) : ev (n := 1) ![pt R d 0] s = s := by
  have : (![pt R d 0] : Fin 1 → Pt R 1 d) = fun j => pt R d j := by
    funext j; fin_cases j; rfl
  rw [this, FBOf.ev_self]

theorem exists_evHom {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) :
    ∃ Ψ : PS R m d →+* PS R n d, (∀ f, ev a f = Ψ f) ∧ ∀ c, Ψ (MvPowerSeries.C c) = MvPowerSeries.C c :=
  ⟨(MvPowerSeries.substAlgHom (R := R) (FramePull.hasSubst_points ha)).toRingHom,
    fun f => (congrFun (MvPowerSeries.coe_substAlgHom (FramePull.hasSubst_points ha)) f).symm,
    fun c => (MvPowerSeries.substAlgHom (R := R) (FramePull.hasSubst_points ha)).commutes c⟩

theorem isSer1_unique (hJet : JetAlgSt) (hRep : RepSt) {x : JetSer.Fam G (Fin d)} (hx : IsUnivChart G d x)
    {U : G.left.Opens} {f : Γ(G.left, U)} {g g' : PS R 1 d} (h : IsSer1 x U f g) (h' : IsSer1 x U f g') :
    g = g' := by
  obtain ⟨-, -, j3, -⟩ := hJet R (Fin 1 × Fin d)
  obtain ⟨r1, -⟩ := hRep R G d x hx (Fin 1 × Fin d)
  obtain ⟨Y, hY, -⟩ := r1 (pt R (n := 1) d 0) (TB.WickVanishing.gp_pt 0)
  refine j3 g g' fun m => ?_
  have := (h 1 _ _ hY m).2.symm.trans (h' 1 _ _ hY m).2
  rwa [ev_pt_zero, ev_pt_zero] at this

theorem series_pull (hJet : JetAlgSt) (hRep : RepSt) {x : JetSer.Fam G (Fin d)} (hx : IsUnivChart G d x)
    {L : LB G.left} (hL : L.IsLB) (j : L.ι) {f : G ⟶ G} {α : Pt R 1 d} (hα : IsMapOf x x f α) {N k q : ℕ}
    (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, f.left] ![(N : ℤ), -1]))
    (σ : H0 L k) (σ' : H0 L q) (t : R)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good L z J →
      sval σ' r z J = constVal (r ≫ G.hom) z t * (sval σ (r ≫ f.left) z J * (val mu r z J).val ^ k))
    {M S S' : PS R 1 d} (hM : IsSer1 x _ (mu.s (fun _ => j)).val M) (hS : IsSer1 x _ (σ.f (fun _ => j)) S)
    (hS' : IsSer1 x _ (σ'.f (fun _ => j)) S') :
    S' = MvPowerSeries.C t * (ev (n := 1) ![α] S * M ^ k) := by
  classical
  obtain ⟨j1, -, j3, -⟩ := hJet R (Fin 1 × Fin d)
  obtain ⟨r1, -⟩ := hRep R G d x hx (Fin 1 × Fin d)
  obtain ⟨Y, hY, -⟩ := r1 (pt R (n := 1) d 0) (TB.WickVanishing.gp_pt 0)
  have hA : Rep x α (fun m => Y m ≫ f) := by
    have := hα.2 1 _ _ hY
    rwa [TB.WickVanishing.gt_comp1_pt_right] at this
  refine j3 _ _ fun m => ?_
  obtain ⟨τ, hτ, -⟩ := j1 m
  refine eq_of_germ fun z => ?_
  obtain ⟨J, hJ, hJ'⟩ := exists_good_const L hL j z
  rw [← hτ, ← hτ]
  let Φ := (((Spec (CommRingCat.of (JetR R (Fin 1 × Fin d) m))).presheaf.germ ⊤ z trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (JetR R (Fin 1 × Fin d) m))).inv.hom).comp τ.toRingHom
  have sv : ∀ (n : ℕ) (s : H0 L n) (r : Spec (CommRingCat.of (JetR R (Fin 1 × Fin d) m)) ⟶ G.left) (g : PS R 1 d),
      (⊤ ≤ r ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j) ∧
        fnVal r _ (s.f (fun _ => j)) = toJet m g) → Φ g = sval s r z J := fun n s r g h => by
    rw [sval_of s r z J (fun _ => j) fun i => hJ' _ (Set.mem_iInter.1 (h.1 (trivial : z ∈ (⊤ : _))) i)]
    refine Eq.trans ?_ (gs_eq_germ_fnVal _ _ h.1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h.2.symm))
  have e₁ := sv _ σ' _ _ (hS' 1 _ _ hY m)
  have e₂ := sv _ σ _ _ (hS 1 _ _ hA m)
  have e₃ : Φ (ev (n := 1) ![pt R d 0] M) = (val mu (Y m).left z J).val := by
    obtain ⟨h1, h2⟩ := hM 1 _ _ hY m
    refine Eq.trans ?_ (congrArg Units.val (val_const hJ' mu _ h1)).symm
    refine Eq.trans ?_ (gm_eq_germ_fnVal _ _ h1 _ z).symm
    exact congrArg _ (congrArg _ ((hτ _).trans h2.symm))
  have e₄ : Φ (MvPowerSeries.C t) = constVal ((Y m).left ≫ G.hom) z t := by
    rw [Over.w (Y m), constVal, gs_eq _ z ⊤ trivial]
    have a₁ : τ (MvPowerSeries.C t) = algebraMap R _ t := τ.commutes t
    have a₂ := congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap R (JetR R (Fin 1 × Fin d) m))))
    exact congrArg _ ((congrArg _ a₁).trans a₂)
  rw [ev_pt_zero] at e₁ e₃
  show Φ S' = Φ _
  rw [map_mul, map_mul, map_pow, e₁, e₂, e₃, e₄]
  exact H _ _ z J hJ

end Series

theorem surjective_appTop {S : Scheme.{0}} {G : Over S} [GrpObj G]
    (h : Function.Surjective (G ⊗ G).hom.appTop.hom) : Function.Surjective G.hom.appTop.hom := fun f => by
  obtain ⟨c, hc⟩ := h ((fst G G).left.appTop.hom f)
  refine ⟨c, ?_⟩
  have e := congrArg (lift (𝟙 G) (𝟙 G)).left.appTop.hom hc
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    Over.w, ← Over.comp_left, lift_fst] at e
  simpa using e

theorem germ_pullback : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt → JetSer.SerSt →
    JetSer.SerExSt → JetSer.RosIdSt → FamGerm.GermExSt → PullGermSt := by
  intro hL _ _ hJet hRep hSer hEx hRos _ E _ _ _ H V _ _ _ F _ _ _ _ _ _ y a N k hN hk ha h hh
  let _ := H.starRing
  have := y.P.U.smooth
  have := y.t.act.hom a
  have hLB := y.P.U.LG.isLB
  obtain ⟨s₂, s₃⟩ := surjective_appTop_sq_cube y.P.U.toUnifPre
  obtain ⟨⟨mu₀, hmu₀⟩, hgeo⟩ := FrameGeo.frame_pullback_geo hJet hRep hSer hEx hRos V y.t.G (surjective_appTop s₂)
    s₂ s₃ y.P.U.LG y.P.U.cubG (𝓞 E) y.t.act y.u y.hu y.d y.x y.hx y.j y.hj y.B y.hB H.w0 y.ρ y.hρ a N ha
  obtain ⟨mu, hmu, hn⟩ := exists_norm y.P.U.LG (y.t.act.act a) hN mu₀ hmu₀
  obtain ⟨u, hu, hc, vu⟩ := exists_generic y.P.U.LG (y.t.act.act a) N k mu hmu hn
  obtain ⟨r, hr⟩ := y.exists_frameSer
  obtain ⟨M, hM⟩ : ∃ M, JetSer.IsSer1 y.x _ (mu.s (fun _ => y.j)).val M := by
    refine ((hEx V y.t.G y.d y.x y.hx).1 _ (fun z hz => Set.mem_iInter.2 fun i => ?_) _).exists
    have key : η[y.t.G].left ≫ (![𝟙 y.t.G.left, (y.t.act.act a).left] : Fin 2 → _) i = η[y.t.G].left := by
      fin_cases i
      · exact Category.comp_id _
      · show η[y.t.G].left ≫ (y.t.act.act a).left = _
        rw [← Over.comp_left, IsMonHom.one_hom]
    have : (η[y.t.G].left ≫ (![𝟙 y.t.G.left, (y.t.act.act a).left] : Fin 2 → _) i) z ∈ y.P.U.LG.L.U y.j := by
      rw [key]; exact y.hj hz
    exact this
  obtain ⟨w, κ, hw, hexp⟩ := hgeo mu hmu M r hM hr
  refine ⟨w, κ⁻¹ ^ k, hexp F h hh, ?_⟩
  rintro s s' _ hP ⟨l, c, σ, f, g, r', h₁, h₂, hr', h₃, rfl⟩
  obtain rfl := isSer1_unique hJet hRep y.hx hr hr'
  have hB := GlobalTheory.T.expansion_commutes_pullback_cmEndo_four_le hL V E H y.t y.P a N ha hN k hk
  have T := PullExpField.term hL y.P.U y.P.oD a (y.t.act.act a) k N (by omega) hB u hu hc F
  choose t τ f' θ θ' ht hτ hθ hθ' hPi hv using fun i => T (σ i) (f i) (h₁ i)
  have hs := (PullExpField.secLin_iff_comb c hθ s).1 h₂
  let c' : Fin l → F := fun i => c i * (PullExpField.toF V F (t i))⁻¹
  have hc' : ∀ i, c' i * PullExpField.toF V F (t i) = c i := fun i =>
    inv_mul_cancel_right₀ (PullExpField.toF_ne_zero F (ht i)) _
  have hs' : s' = ∑ i, c' i • θ' i := by
    refine PullLin.pullAl_unique hL.globalFns _ a k N hP ?_
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · have := PullLin.pullAl_smul _ a k N (0 : F) hP
      rw [zero_smul, zero_smul] at this
      rw [hs, Fin.sum_univ_zero, Fin.sum_univ_zero]
      exact this
    · have := GlobalTheory.T.pullAl_linear_combination hL.globalFns V y.P.D F _ y.P.oD a k N l hl c' _ _ hPi
      simp only [smul_smul, hc'] at this
      rw [hs]
      exact this
  have cz := FramePull.cz1 (y.B.A.const a)
  obtain ⟨Ψ, hΨ, -⟩ := exists_evHom cz
  refine ⟨l, c', τ, f', fun i => MvPowerSeries.C (t i) *
    (MvPowerSeries.C ((κ⁻¹ ^ k : Vˣ) : V) * (ev (n := 1) ![y.B.A.act a] (g i) * w ^ k)), r, hτ,
    (PullExpField.secLin_iff_comb c' hθ' _).2 hs', hr, fun i => ?_, ?_⟩
  · obtain ⟨S, hS, e⟩ := h₃ i
    obtain ⟨S', hS'⟩ : ∃ S', JetSer.IsSer1 y.x _ ((τ i).f (fun _ => y.j)) S' :=
      ((hEx V y.t.G y.d y.x y.hx).1 (LB.wchart y.P.U.LG.L (fun _ : Fin 1 => 𝟙 y.t.G.left) (fun _ => y.j))
        (fun z hz => Set.mem_iInter.2 fun _ => y.hj hz) _).exists
    refine ⟨S', hS', ?_⟩
    rw [series_pull hJet hRep y.hx hLB y.j (y.hB.map a) mu (σ i) (τ i) (t i)
      (sval_of_generic hLB _ N k mu hmu _ _ _ fun Z q z J hJ => by rw [hv i Z q z J hJ, vu Z q z J hJ]) hM hS hS',
      ← e, hΨ (g i * r ^ k), map_mul, map_pow, ← hΨ, ← hΨ]
    have hκ : (MvPowerSeries.C ((κ⁻¹ ^ k : Vˣ) : V) : PS V 1 y.d) * MvPowerSeries.C (κ : V) ^ k = 1 := by
      rw [← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow,
        Units.val_one, map_one]
    have hwk := congrArg (· ^ k) hw
    simp only [mul_pow] at hwk
    rw [mul_comm k N, pow_mul]
    linear_combination (MvPowerSeries.C (t i) * MvPowerSeries.C ((κ⁻¹ ^ k : Vˣ) : V) *
      ev (n := 1) ![y.B.A.act a] (g i)) * hwk + (MvPowerSeries.C (t i) * ev (n := 1) ![y.B.A.act a] (g i) *
      M ^ k * ev (n := 1) ![y.B.A.act a] r ^ k) * hκ
  · have eV : TWO.algVF (V := V) (F := F) = algebraMap V F := (IsScalarTower.algebraMap_eq V _ F).symm
    have czK := FramePull.cz1 (FramePull.constantCoeff_actK (k := F) y.B a)
    obtain ⟨Θ, hΘ, hΘ'⟩ := exists_evHom czK
    rw [hΘ, map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (fun j i => MvPowerSeries.map (algebraMap V F) ((![y.B.A.act a] : Fin 1 → Pt V 1 y.d) j i)) =
        ![y.B.actK F a] := by
      funext j; fin_cases j; rfl
    have e' : algebraMap V F (t i) = PullExpField.toF V F (t i) := IsScalarTower.algebraMap_apply V _ F _
    rw [eV, map_mul Θ, hΘ', ← hΘ, ← hc' i, map_mul _ (c' i), map_mul (MvPowerSeries.map _),
      map_mul (MvPowerSeries.map _), map_mul (MvPowerSeries.map _), map_pow (MvPowerSeries.map _),
      MvPowerSeries.map_C, MvPowerSeries.map_C, FramePull.map_ev_eq _ cz, e, e']
    ring

end GlobalTheory.PullGerm
