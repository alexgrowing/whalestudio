import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RawChartFormalBiextensionBaseChange
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValuesInvariantUniversalEndomorphism
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueCopiesGaugeIndependent
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueGermsIndependentOfChart

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.GermValuationJetHarmonics

open GlobalTheory.ChartPush

section General

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

theorem val_of_maps {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    {a : LB.Gen (LB.LinComb L' φ' ε)} {b : LB.Gen (LB.LinComb L (fun k => φ' k ≫ Φ) ε)}
    (h : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L Φ φ' ε b)) (r : Z ⟶ Y) (z : Z) {J J'}
    (hJ : Good L z J) (hJ' : Good L' z J') :
    val b r z J = (∏ k, om w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  have pm := (Geo.Tor.maps_iff w φ' (fun k => φ' k ≫ Φ) ε a b (𝟙 Y) (flatGen L Φ φ' ε b)
    (fun j => wchart_pull_le L Φ φ' j) (fun _ => rfl)).1 h
  have e := DegPull.pmaps_val (fun k => (Category.id_comp _).symm) pm r z hJ hJ'
  rw [Category.comp_id] at e
  exact e

theorem exists_good_cast {L₁ L₂ : LB X} (h : L₁ = L₂) (z : Z) (J₂ : (Z ⟶ X) → L₂.ι) (hJ : Good L₂ z J₂) :
    ∃ J₁, Good L₁ z J₁ ∧
      (∀ {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (b : LB.Gen (LB.LinComb L₁ φ ε)) (r : Z ⟶ Y),
        val (genCast h φ ε b) r z J₂ = val b r z J₁) ∧
      ∀ (w : LB.Iso L' (L₁.pull Φ)) (p : Z ⟶ X') (J' : (Z ⟶ X') → L'.ι),
        gv (isoCast h Φ w) p z (fun _ => J₂ (p ≫ Φ)) (J' p) = om w z J₁ J' p := by
  subst h
  exact ⟨J₂, hJ, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

end General

section Transport

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}} {t : SAB H X}
  {t' : SAB H X'} {Φ : t'.G.left ⟶ t.G.left} {w : LB.Iso t'.PP.L (t.PP.L.pull Φ)}

theorem val_prim_mul {Y Z : Scheme.{0}} {φ' : ULift.{0} (Finset (Fin 2)) → (Y ⟶ t'.G.left)}
    {e' : LB.Gen (LB.LinComb t'.PP.L φ' (cε 2))} {e : LB.Gen (LB.LinComb t.PP.L (fun k => φ' k ≫ Φ) (cε 2))}
    (he : LB.Gen.Maps (LB.linCombIso w φ' (cε 2)) e' (flatGen t.PP.L Φ φ' (cε 2) e))
    {u' : LB.Gen (LB.LinComb t'.PP.L (primφ t') primε)}
    {u : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ Φ) primε)}
    (hu : LB.Gen.Maps (LB.linCombIso w (primφ t') primε) u' (flatGen t.PP.L Φ _ _ u))
    (p : Z ⟶ t'.G.left) (s : Z ⟶ Y) (hs : ∀ I, s ≫ φ' I = p ≫ cφG t' ![𝟙 t'.G, t'.act.act H.w0] I) (z : Z) {J J'}
    (hJ : Good t.PP.L z J) (hJ' : Good t'.PP.L z J') :
    val u p z J * val e s z J = om w z J J' p * (val u' p z J' * val e' s z J') := by
  rw [val_of_maps he s z hJ hJ', val_of_maps hu p z hJ hJ']
  simp only [hs, primφ, primε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id,
    zpow_one, zpow_neg, Finset.prod_inv_distrib]
  generalize (∏ I : ULift.{0} (Finset (Fin 2)), om w z J J' (p ≫ cφG t' ![𝟙 t'.G, t'.act.act H.w0] I) ^ cε 2 I) = l
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X} {x0' : Sp S ⟶ X'} {d : ℕ}
  {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
  {x' : ∀ m, jOG x0' d m 1 ⟶ t'.G} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}

theorem cube_subst {ρ : X' ⟶ X} (ν : SABMap t' t ρ) (hc : IsChartG t x0 d F act tg uvec x)
    (hx : ∀ m, (x' m).left ≫ ν.φ = (x m).left) (m : ℕ) (I : ULift.{0} (Finset (Fin 2))) :
    (homAt x0' (GermD.sL m (act H.w0))).left ≫
        cφG t' ![jptG t' x0' d x' m (0 : Fin 2), jptG t' x0' d x' m (1 : Fin 2)] I =
      (x' m).left ≫ cφG t' ![𝟙 t'.G, t'.act.act H.w0] I := by
  have i₀ : (𝟙 t'.G : t'.G ⟶ t'.G).left ≫ ν.φ = ν.φ ≫ (𝟙 t.G : t.G ⟶ t.G).left := by simp
  have a := (cφ_push ν (T := jOG x0 d m 2) (T' := jOG x0' d m 2) (𝟙 _)
      ((jpt_push hx m 0).trans (Category.id_comp _).symm) ((jpt_push hx m 1).trans (Category.id_comp _).symm) I).trans
      (Category.id_comp _)
  have b := cφ_push ν ν.φ i₀ (ν.act H.w0) I
  apply ν.cart.1.hom_ext
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) a).trans ?_)
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) b)).symm
    rw [← Category.assoc, hx]
    exact (GermD.formEq_eL hc m I).symm
  · simp only [cφG, ← Over.comp_left, Over.w]

theorem isGermG_of_val (hc : IsChartG t x0 d F act tg uvec x) {e : ∀ m, FrTyG t x0 d x m} {wP : PrimTyG t}
    (hg : ∀ m, (e m).IsGen) (hP : wP.IsGen) {k : ℕ} {s : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))}
    {f : MvPowerSeries (Fin 1 × Fin d) S}
    (h : ∀ (m : ℕ) (z : (jOG x0 d m 1).left) (J), Good t.PP.L z J →
      sv t s ((ptSecT t.G (x m)).left ≫ (jBaseG x0 d m 1 ▷ t.G).left) z J =
        gs (𝟙 _) z ⊤ (toΓ _ (psJet m f)) * (val (eLG t x0 d x act e wP m) (𝟙 _) z J ^ k).val) :
    IsGermG t x0 d x act e wP k s f := by
  intro m
  have heL : (eLG t x0 d x act e wP m).IsGen :=
    DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (DVR.pullGen_isGen t.PP.L _ _ _ hP _) (DVR.pullGen_isGen t.PP.L _ _ _ (hg m) _)
  obtain ⟨τ, -, hτ⟩ : ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => (k : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 1).left) (z : Z)
        (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
          val τ r z J = val (genPowG t _ _ (eLG t x0 d x act e wP m) k) r z J := by
    refine exists_gen t.PP.isLB ?_ _ (GermD.genPowG_isGen t _ _ _ heL k)
    intro U _ hU
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, _root_.mul_one,
      GermD.formEq_eL hc m]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, _root_.mul_neg, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  obtain ⟨s₁, hp⟩ := GermD.exists_pullSec t.G t.PP.L (k : ℤ) (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) s
  refine ⟨s₁, τ, hp, corr_of_val t.PP.isLB fun y J hJ => hτ _ _ y J hJ, fun j => fn_ext fun y hy => ?_⟩
  obtain ⟨J, hJ, e₀⟩ := exists_good t.PP.L t.PP.isLB y (fun _ : Fin 1 => (x m).left) j
    (fun a b _ => congrArg j (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hy k)
  have q : sv t s₁ (𝟙 _ ≫ (ptSecT t.G (x m)).left) y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m f)) * (val τ (𝟙 _) y J).val := by
    rw [sv_pullSec hp _ y hJ, Category.id_comp, h m y J hJ, hτ _ _ y J hJ, GermD.val_genPowG]
  rw [val_of τ _ y J j (fun k => by rw [Category.id_comp]; exact e₀ k)] at q
  have q' := (sval_of (φ := fun _ : Fin 1 => (snd _ t.G).left) (ε := fun _ => (k : ℤ)) s₁
    (𝟙 _ ≫ (ptSecT t.G (x m)).left) y J j
    (fun k => by rw [Category.id_comp, ptSecT_snd]; exact e₀ k)).symm.trans q
  exact ((gs_res _ y _ hy _).trans (gs_pull _ (ptSecT t.G (x m)).left y _ (val_le t.G t.PP.L (x m) _ hy) _)).trans
    (q'.trans ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy _) (gs_unit _ y _ hy _))).symm)

theorem ptSec_base (m : ℕ) (a : jOG x0 d m 1 ⟶ t.G) :
    ((ptSecT t.G a).left ≫ (jBaseG x0 d m 1 ▷ t.G).left) ≫ (snd (Over.mk x0) t.G).left = a.left ∧
    ((ptSecT t.G a).left ≫ (jBaseG x0 d m 1 ▷ t.G).left) ≫ (fst (Over.mk x0) t.G).left =
      spMap (algebraMap S (Jet S (Fin 1 × Fin d) m)) := by
  constructor
  · rw [← Over.comp_left, ← Over.comp_left, ptSecT, lift_whiskerRight, lift_snd]
  · rw [← Over.comp_left, ← Over.comp_left, ptSecT, lift_whiskerRight, lift_fst, Category.id_comp]; rfl

end Transport

section Charts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem frames_tied {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (C : IntegralChartA3 Xo c T io y) (m : ℕ)
    {Z : Scheme.{0}} (r : Z ⟶ Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m)) :
    letI := io.toAlgebra
    ∃ p : Z ⟶ C.I.t'.G.left, p ≫ C.I.t'.G.hom = r ≫ spMap (algebraMap T.Fr _) ∧ p ≫ C.I.m1.φ = r ≫ (C.ch.x m).left ∧
      p ≫ C.I.m2.φ = (r ≫ spMap (jetCoef (algebraMap T.V T.Fr) _ m)) ≫ (C.xT m).left ∧
      ∀ (z : Z) J₁ J₂ J', Good Xo.univ.t.PP.L z J₁ → Good C.I.G.PP.L z J₂ → Good C.I.t'.PP.L z J' →
        ∃ A, val (eL y.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP m) r z J₁ = om C.I.w1 z J₁ J' p * A ∧
          val (eLG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT m)
            (r ≫ spMap (jetCoef (algebraMap T.V T.Fr) _ m)) z J₂ = om C.I.w2 z J₂ J' p * A := by
  letI := io.toAlgebra
  obtain ⟨⟨-, hact, -⟩, x', hx₂, hx₁, ⟨e', he'⟩, wP', -, ⟨u₂, cu₂, mu₂⟩, u₁, cu₁, mu₁⟩ := C.gen
  obtain ⟨-, ⟨c₂, cc₂, mc₂⟩, c₁, cc₁, mc₁⟩ := he' m
  have hc := (isChart_iff y.1 _ _ _ _ _).1 C.ch.chart
  have p₁ : (r ≫ (x' m).left) ≫ C.I.m1.φ = r ≫ (C.ch.x m).left :=
    (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (hx₁ m))
  have p₂ : (r ≫ (x' m).left) ≫ C.I.m2.φ = (r ≫ spMap (jetCoef (algebraMap T.V T.Fr) _ m)) ≫ (C.xT m).left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (hx₂ m)).trans (Category.assoc _ _ _).symm)
  refine ⟨r ≫ (x' m).left, ?_, p₁, p₂, fun z J₁ J₂ J' h₁ h₂ h' => ?_⟩
  · exact (Category.assoc _ _ _).trans (congrArg (r ≫ ·) ((Over.w (x' m)).trans (Category.comp_id _)))
  have hs := fun I => (Category.assoc r _ _).trans ((congrArg (r ≫ ·) (cube_subst C.I.m1 hc hx₁ m I)).trans
    (Category.assoc _ _ _).symm)
  have k₁ := val_prim_mul mc₁ mu₁ _ _ hs z h₁ h'
  have k₂ := val_prim_mul mc₂ mu₂ _ _ hs z h₂ h'
  refine ⟨_, Eq.trans ?_ k₁, Eq.trans ?_ k₂⟩
  · refine (val_mul h₁ _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · refine (val_pull h₁ _ _ _).trans (Eq.trans ?_ ((val_corr h₁ cu₁ _).trans (val_pull h₁ _ _ _)).symm)
      exact congrArg (fun q => val C.ch.wP q z J₁) p₁.symm
    · exact (val_pull h₁ _ _ _).trans (val_corr h₁ cc₁ _).symm
  · refine (val_mul h₂ _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · refine (val_pull h₂ _ _ _).trans (Eq.trans ?_ ((val_corr h₂ cu₂ _).trans (val_pull h₂ _ _ _)).symm)
      exact congrArg (fun q => val C.wPT q z J₂) p₂.symm
    · refine (val_pull h₂ _ _ _).trans (Eq.trans ?_ ((val_corr h₂ cc₂ _).trans (val_pull h₂ _ _ _)).symm)
      refine congrArg (fun q => val (L := C.I.G.PP.L) (φ := cφG C.I.G ![jptG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT m (0 : Fin 2),
        jptG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT m (1 : Fin 2)]) (ε := cε 2) (C.eT m) q z J₂) ?_
      refine (Category.assoc _ _ _).trans (Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm)
      have e : (fun p : Fin 2 × Fin (chD C.ch) => (![fun j => MvPolynomial.X ((0 : Fin 1), j),
          fun j => psIn (chD C.ch) m ![0] (C.ch.B.A.act H.w0 j)] :
            Fin 2 → Fin (chD C.ch) → MvPolynomial (Fin 1 × Fin (chD C.ch)) T.Fr) p.1 p.2) =
          fun p => MvPolynomial.map (algebraMap T.V T.Fr) ((![fun j => MvPolynomial.X ((0 : Fin 1), j),
          fun j => psIn (chD C.ch) m ![0] (C.actT H.w0 j)] :
            Fin 2 → Fin (chD C.ch) → MvPolynomial (Fin 1 × Fin (chD C.ch)) T.V) p.1 p.2) := by
        funext ⟨i, j⟩
        fin_cases i
        · exact (MvPolynomial.map_X _ _).symm
        · exact (congrArg (psIn (chD C.ch) m ![0]) (hact H.w0 j)).trans (RawChartGermBC.map_psIn _ _ m _ _).symm
      refine (RawChartGermBC.spMap_comp_eq _ _ _ _ ?_).symm
      refine Eq.trans ?_ (PullbackSections.jetSubstP_comp_jetBC (algebraMap T.V T.Fr) m _)
      rw [← e]
      rfl

theorem exists_chart_baseChange {S S' : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [CommRing S'] [Algebra c.F S']
    [Algebra ℚ S'] (φ : S →ₐ[c.F] S') {y : FrPt Xo c S} {y' : FrPt Xo c S'} (h : FrMap φ y y') (C : ChartAt Xo c y) :
    ∃ (x' : ∀ m, jO y' C.d m 1 ⟶ Xo.univ.t.G) (e' : ∀ m, FrTy y' C.d x' m),
      IsChart y' C.d (FBMap.mapFB φ.toRingHom C.B).G.F (FBMap.mapFB φ.toRingHom C.B).A.act
        (fun ℓ j => φ.toRingHom (C.uvec ℓ j)) x' ∧
      IsFrame y' C.d x' (FBMap.mapFB φ.toRingHom C.B).G.F (FBMap.mapFB φ.toRingHom C.B).A.act
        (FBMap.mapFB φ.toRingHom C.B).ph1 (FBMap.mapFB φ.toRingHom C.B).ph2 (FBMap.mapFB φ.toRingHom C.B).sy
        (FBMap.mapFB φ.toRingHom C.B).ad e' ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y' C.d x' (FBMap.mapFB φ.toRingHom C.B).A.act e' C.wP 0)
          (homAt y'.x (jetAug : Jet S' (Fin 1 × Fin C.d) 0 →ₐ[S'] S')).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y'.x S') 1) ∧
      (∀ m, (x' m).left = spMap (jetCoef φ.toRingHom _ m) ≫ (C.x m).left) ∧
      ∀ (m : ℕ) (z : Sp (Jet S' (Fin 1 × Fin C.d) m)) (J), Good Xo.univ.t.PP.L z J →
        val (eL y' C.d x' (FBMap.mapFB φ.toRingHom C.B).A.act e' C.wP m) (𝟙 _) z J =
          val (eL y C.d C.x C.B.A.act C.e C.wP m) (spMap (jetCoef φ.toRingHom _ m)) z J := by
  obtain ⟨x0', a₁, u', a₂, a₃, a₄, a₅, a₆⟩ := y'
  obtain ⟨hx, hu, -⟩ := h
  dsimp only at hx hu
  obtain rfl : u' = fun τ i => spMap (dualMap φ.toRingHom) ≫ y.u τ i := funext fun τ => funext fun i => hu τ i
  subst hx
  let R := ChartAt.toRaw C
  obtain ⟨e', hg, hc, -⟩ := GlobalTheory.T.exists_rawChart_frames_baseChange E H Dw l Xo S S' φ.toRingHom y.x R.d R.B.G.F R.B.A.act R.x
    (fun m => rjBC φ.toRingHom y.x R.d m 1 ≫ R.x m) (fun _ => rfl) R.e R.frame.gen
  have hG := GlobalTheory.T.rawChart_baseChange_rig_germ_alt E H Dw l Xo S S' φ.toRingHom y.x R.d R.B.G.F R.B.A.act R.x
    (fun m => rjBC φ.toRingHom y.x R.d m 1 ≫ R.x m) (fun _ => rfl) R.e e' R.frame.gen hg hc
    R.wP R.prim.1
  have h₁ := GlobalTheory.T.isRawChart_baseChange_jetPoints E H Dw l Xo S S' φ.toRingHom y.x R.d R.B.G.F R.B.A.act R.x
      (fun m => rjBC φ.toRingHom y.x R.d m 1 ≫ R.x m) (fun _ => rfl) y.u R.uvec R.chart
  have h₂ := GlobalTheory.T.isFrame_rawChart_baseChange E H Dw l Xo S S' φ.toRingHom y.x R.d R.B.G.F R.B.A.act R.x
      (fun m => rjBC φ.toRingHom y.x R.d m 1 ≫ R.x m) (fun _ => rfl) R.e e' R.frame.gen hg hc
      _ _ _ _ R.frame
  refine ⟨fun m => rjBC φ.toRingHom y.x R.d m 1 ≫ R.x m, e', ⟨h₁.zero, h₁.trunc, h₁.law, h₁.act, h₁.tan, h₁.basis⟩,
    ⟨h₂.gen, h₂.ph1, h₂.ph2, h₂.sy, h₂.ad⟩, hG.1 R.rig0, fun _ => rfl, fun m z J hJ => ?_⟩
  have k := RawChartGermBC.val_reL_bc φ.toRingHom y.x R.d R.B.A.act R.x _ (fun _ => rfl) R.e e' hc R.wP m (𝟙 _) z hJ
  rw [Category.id_comp] at k
  exact k

end Charts

theorem nabValN_columns {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    [StarRing (𝓞 E)] {R k k₀ : Type} [CommRing R] [Field k] [Field k₀] [Algebra ℚ k] [Algebra R k] (g : k₀ →+* k) {d : ℕ}
    (B : FB R d (𝓞 E)) (h : PS k 2 d) (hh : MvPowerSeries.constantCoeff h = 0) (q n : ℕ) (f : Fin n → PS k 1 d)
    (u : Lt1 Dw → Fin d → k) (P : MvPolynomial (LtN Dw n) k₀) :
    nabValN B k h H.w0 q (boxSer f) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) => u ⟨ℓ.1, ℓ.2.1⟩)
        (MvPolynomial.map g P) =
      ∑ m ∈ P.support, g (P.coeff m) * ∏ b, (FBMap.mapFB (algebraMap R k) B).nabVal k h H.w0 q (f b) u
        (MvPolynomial.monomial (colOf m b) 1) := by
  have hK : ∀ {n : ℕ} (f : Germ.PS R n d),
      Germ.FB.toK k (MvPowerSeries.map (algebraMap R k) f : Germ.PS k n d) = Germ.FB.toK k f := by
    intro n f
    ext m
    rfl
  have hF : (FBMap.mapFB (algebraMap R k) B).FK k = B.FK k := funext fun i => hK (B.G.F i)
  have hA : ∀ a, (FBMap.mapFB (algebraMap R k) B).actK k a = B.actK k a :=
    fun a => funext fun i => hK (B.A.act a i)
  have hN : ∀ b Q, (FBMap.mapFB (algebraMap R k) B).nabVal k h H.w0 q (f b) u Q = B.nabVal k h H.w0 q (f b) u Q := by
    intro b Q
    simp only [FB.nabVal, FB.hL, hF, hA]
  simp only [hN]
  have hP : ∀ Q : MvPolynomial (LtN Dw n) k,
      nabValN B k h H.w0 q (boxSer f) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) => u ⟨ℓ.1, ℓ.2.1⟩) Q =
      ∑ m ∈ Q.support, Q.coeff m * ∏ b, B.nabVal k h H.w0 q (f b) u (MvPolynomial.monomial (colOf m b) 1) := by
    intro Q
    obtain ⟨Q, rfl⟩ : ∃ Q', MvPolynomial.rename (HarmCopies.letterEquiv (E →+* ℂ) Dw.mult n) Q' = Q :=
      MvPolynomial.rename_surjective _ (HarmCopies.letterEquiv _ _ n).surjective Q
    rw [nabValN_boxSer R _ _ B k h H.w0 hh q n f _ _
      (HarmCopies.letterEquiv (E →+* ℂ) Dw.mult n) _ u _ (fun _ => rfl) (fun _ => rfl),
      GlobalTheory.NabCol.sum_support_rename (HarmCopies.letterEquiv (E →+* ℂ) Dw.mult n) (fun mo =>
        ∏ b, B.nabVal k h H.w0 q (f b) u (MvPolynomial.monomial (colOf mo b) 1))]
    refine Finset.sum_congr rfl fun mo _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    have hc : colM mo b = colOf (Finsupp.mapDomain (HarmCopies.letterEquiv (E →+* ℂ) Dw.mult n) mo) b := by
      ext ℓ
      exact (Finsupp.mapDomain_apply (HarmCopies.letterEquiv (E →+* ℂ) Dw.mult n).injective mo (ℓ, b)).symm
    rw [hc]
  rw [hP, MvPolynomial.support_map_of_injective _ g.injective]
  simp only [MvPolynomial.coeff_map]

theorem alg_tie {R : Type} [CommRing R] {a b f : R} {o₁ o₂ A v₁ v₂ : Rˣ} {q : ℕ} (h : a * o₁.val ^ q = b * o₂.val ^ q)
    (ha : a = f * (v₂ ^ q).val) (h₁ : v₁ = o₁ * A) (h₂ : v₂ = o₂ * A) : b = f * (v₁ ^ q).val := by
  subst ha h₁ h₂
  refine (Units.mul_left_inj (o₂ ^ q)).1 ?_
  rw [Units.val_pow_eq_pow_val, ← h]
  simp only [Units.val_pow_eq_pow_val, Units.val_mul]
  ring

theorem jetCoef_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) (κ : Type) (m : ℕ) :
    (jetCoef g κ m).comp (jetCoef f κ m) = jetCoef (g.comp f) κ m := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_)
  exact congrArg (Ideal.Quotient.mk _) (MvPolynomial.map_map f g p)

theorem spMap_spMap {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    (spMap g ≫ spMap f : Sp D ⟶ Sp A) = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

set_option maxHeartbeats 800000 in

theorem sv_of_tie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
    {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G) (τ : Frames P.U.LG.L (κ := Fin 1 × Fin (chD C.ch)) C.xT)
    (hτ : IsEL P C.xT C.actT C.eT C.wPT τ) (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F]
    [IsScalarTower T.V T.Fr F] (xF : Sp F ⟶ Xo.X) (q : ℕ) (σ : P.U.toUnifPre.SecGF F q)
    (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) (f : PS F 1 (chD C.ch))
    (ht : SecTieF C.I P F xF q σ hh) (hf : GermA P.U.toUnifPre (κ := Fin 1 × Fin (chD C.ch)) C.xT τ F q σ f)
    (m : ℕ) (a : jOG xF (chD C.ch) m 1 ⟶ Xo.univ.t.G)
    (ha : letI := io.toAlgebra; a.left = spMap (jetCoef (algebraMap T.Fr F) _ m) ≫ (C.ch.x m).left)
    (z : Sp (Jet F (Fin 1 × Fin (chD C.ch)) m)) (J) (hJ : Good Xo.univ.t.PP.L z J) :
    letI := io.toAlgebra
    sv Xo.univ.t hh ((ptSecT Xo.univ.t.G a).left ≫ (jBaseG xF (chD C.ch) m 1 ▷ Xo.univ.t.G).left) z J =
      gs (𝟙 _) z ⊤ (toΓ _ (psJet m f)) * (val (eL y.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP m)
        (spMap (jetCoef (algebraMap T.Fr F) _ m)) z J ^ q).val := by
  letI := io.toAlgebra
  obtain ⟨p, p₀, p₁, p₂, hp⟩ := frames_tied C m (spMap (jetCoef (algebraMap T.Fr F) (Fin 1 × Fin (chD C.ch)) m))
  obtain ⟨zF, z₁, z₂, hz⟩ := hf m
  have hLG : P.U.LG.L.IsLB := P.U.LG.isLB
  obtain ⟨J₂, hJ₂⟩ := DegPull.exists_good' hLG z
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' C.I.t'.PP.isLB z
  obtain ⟨J₃, hJ₃, hv, hw⟩ := exists_good_cast (L' := C.I.t'.PP.L) (Φ := C.I.m2.φ)
    (congrArg RigLB.L P.bundle).symm z J₂ hJ₂
  obtain ⟨A, k₁, k₂⟩ := hp z J J₃ J' hJ hJ₃ hJ'
  have ec : spMap (jetCoef (algebraMap T.Fr F) (Fin 1 × Fin (chD C.ch)) m) ≫
      spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin (chD C.ch)) m) =
      spMap (jetCoef (algebraMap T.V F) (Fin 1 × Fin (chD C.ch)) m) := by
    rw [spMap_spMap, jetCoef_comp, ← IsScalarTower.algebraMap_eq]
  rw [ec] at p₂ k₂
  obtain ⟨b₁, b₂⟩ := ptSec_base (t := Xo.univ.t) m a
  have key := ht.2 _ p zF _ (z₂.trans p₂.symm) (b₁.trans (ha.trans p₁.symm)) (z₁.trans b₂.symm) (by
      rw [← Category.assoc, p₀]
      refine (congrArg (· ≫ spMap (algebraMap T.Fr F)) b₂).trans ?_
      exact RawChartGermBC.spMap_comp_eq _ _ _ _
        (RingHom.ext fun s => (jetBC_algebraMap (algebraMap T.Fr F) _ m s).symm))
    z J J₂ (J' p) hJ hJ₂ (hJ' p)
  rw [hw] at key
  have k₃ := (val_corr hJ₂ (corr_of_val hLG (hτ m))
    (spMap (jetCoef (algebraMap T.V F) (Fin 1 × Fin (chD C.ch)) m))).trans ((hv _ _ _ _).trans k₂)
  exact alg_tie key (hz z J₂ hJ₂) k₁ k₃

end GlobalTheory.GermValuationJetHarmonics

namespace GlobalTheory

open GermValuationJetHarmonics in
set_option maxHeartbeats 800000 in

theorem harmonic_value_of_tied_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (τ : Frames P.U.LG.L (κ := Fin 1 × Fin (chD C.ch)) C.xT), τ.Gen → IsEL P C.xT C.actT C.eT C.wPT τ → ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y.1 yF → ∀ (q n : ℕ) (σ : Fin n → P.U.toUnifPre.SecGF F q) (hh : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo yF.x))) (f : Fin n → PS F 1 (chD C.ch)), (∀ i, SecTieF C.I P F yF.x q (σ i) (hh i)) → (∀ i, GermA P.U.toUnifPre (κ := Fin 1 × Fin (chD C.ch)) C.xT τ F q (σ i) (f i)) → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF (q : ℤ) (hh i) (colOf m i) = nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 q (boxSer f) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map (algebraMap c.F F) Pp) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C P τ _ hτ F _ _ _ _ _
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  intro φ hφ yF hy q n σ hh f ht hf a Pp hP
  obtain ⟨x', e', h₁, h₂, h₃, h₄, h₅⟩ := exists_chart_baseChange φ hy C.ch
  rw [hφ] at h₁ h₂ h₃ h₄ h₅
  have hg := RawChartBaseChange.isCanonGauge_mapFB (algebraMap T.Fr F) C.ch.B C.ch.h C.ch.gauge
  let CF : ChartAt Xo c yF := ⟨C.ch.d, FBMap.mapFB (algebraMap T.Fr F) C.ch.B, fun ℓ j => algebraMap T.Fr F (C.ch.uvec ℓ j),
    x', e', C.ch.wP, MvPowerSeries.map (algebraMap T.Fr F) C.ch.h, h₁, h₂, C.ch.prim, hg, h₃⟩
  have hG : ∀ i, IsGerm yF CF.d CF.x CF.B.A.act CF.e CF.wP q (hh i) (f i) := fun i =>
    (isGerm_iff yF _ _ _ _ _ _ _ _).2 (isGermG_of_val ((isChart_iff yF _ _ _ _ _).1 h₁) h₂.gen C.ch.prim.1
      fun m z J hJ => (sv_of_tie C P τ hτ F yF.x q (σ i) (hh i) (f i) (ht i) (hf i) m (x' m) (h₄ m) z J hJ).trans
        (congrArg (fun v => gs (𝟙 _) z ⊤ (toΓ _ (psJet m (f i))) * (v ^ q).val) (h₅ m z J hJ).symm))
  obtain ⟨C₁, hex, hpin⟩ := hnab.2 F yF
  choose f₁ hf₁ using fun b => hex q (hh b)
  have e₁ : ∀ m, ∏ b, nab yF q (hh b) (colOf m b) =
      ∏ b, C₁.B.nabVal F C₁.h H.w0 q (f₁ b) C₁.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin q (hh b) (f₁ b) (hf₁ b) (colOf m b)
  have h := ChartField.chartVal_indep E H Dw l Xo c hnab.1 F yF C₁ CF q n hh f₁ f hf₁ hG a Pp hP
  simp only [e₁]
  refine h.trans ?_
  exact (nabValN_columns (algebraMap c.F F) C.ch.B _ (HarmCopies.const_eq_zero hg) q n f
    (fun ℓ j => algebraMap T.Fr F (C.ch.uvec ℓ j)) Pp).symm

end GlobalTheory
