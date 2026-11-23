import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HarmonicChartValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifBijectiveOfParam
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecondCubicalLawIffClause
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsGermGIffExistsFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NilpotentSubOrigin
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NablaPinCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames GlobalTheory.IndefiniteRowSideFullHecke.HarmonicChartValues GlobalTheory.GermSectionCompare
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {j : JetPts t.G x0 d}

theorem frameEquiv_eq (e : FrameFam t.G x0 t.PP.L j) : frameEquiv t x0 j e = FrameCompare.frEquiv t x0 j e := by
  have key : ∀ {T : Over X0} {p q : Fin 2 → (T ⟶ t.G)} (h : p = q) (h' : lamφ t.G p = lamφ t.G q)
      (g : LB.Gen (cubeLB t.G p t.PP.L)), genCast (L := t.PP.L) lamε h' g = FrameCompare.castGen t h g := by
    intro T p q h h' g
    subst h
    unfold FrameCompare.castGen
    exact genCast_rfl (L := t.PP.L) lamε g
  funext m
  rw [frameEquiv_apply, FrameCompare.frEquiv_apply]
  exact key (FrameCompare.pair_eq t x0 j m) _ (e m)

theorem powFrame_isGen {T : Over X0} (z : T ⟶ t.G)
    (e : LB.Gen (LB.LinComb t.PP.L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
    (he : e.IsGen) (k : ℤ) : (powFrame t.G t.PP.L z e k).IsGen := by
  intro i j
  have h := congrArg (· ^ k) (he i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

theorem isGermIn_unique (eL : FrameL t.G x0 t.PP.L j) (k : ℤ) (F : LB.Sec (LPow t.G t.PP.L k (Over.mk x0)))
    (f f' : Germ.PS S 1 d) (hf : IsGermIn eL k F f) (hf' : IsGermIn eL k F f') : f = f' := by
  refine psJet_inj fun m => ?_
  obtain ⟨F₁, hP₁, hV₁⟩ := hf m
  obtain ⟨F₂, hP₂, hV₂⟩ := hf' m
  have hF := pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  exact toΓ_injective _ (value_unique _ _ t.PP.isLB _ _ _ _ _ _ hV₁ hV₂)

def zeroSec (t : SAB H X0) (k : ℤ) (T : Over X0) : LB.Sec (LPow t.G t.PP.L k T) := ⟨fun _ => 0, fun i j => by simp⟩

theorem isGermIn_zero (eL : FrameL t.G x0 t.PP.L j) (k : ℤ) : IsGermIn eL k (zeroSec t k _) 0 := by
  intro m
  refine ⟨zeroSec t k _, fun i => ?_, fun i => ?_⟩
  · simp only [zeroSec, map_zero]
  · have h : funOn (psJet m (0 : Germ.PS S 1 d)) = 0 := by
      have : psJet m (0 : Germ.PS S 1 d) = 0 := by simp [psJet, psTrunc]
      rw [this]; exact map_zero _
    rw [h]
    simp only [zeroSec, map_zero]
    exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans (zero_mul _).symm

theorem exists_isGermIn (eL : FrameL t.G x0 t.PP.L j) (hg : ∀ m, (eL m).IsGen)
    (hx : ∀ m, ρT x0 d m ≫ chartEquiv t x0 j (m + 1) = chartEquiv t x0 j m)
    (htr : ∀ m y J, Good t.PP.L y J → val (eL (m + 1)) (ρT x0 d m).left y J = val (eL m) (𝟙 _) y J)
    (k : ℤ) (Fs : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))) : ∃ f, IsGermIn eL k Fs f := by
  have hL := t.PP.isLB
  let x : ∀ m, jOG x0 d m 1 ⟶ t.G := chartEquiv t x0 j
  let τ : ∀ m, LB.Gen (LB.LinComb t.PP.L (Y := (jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => k) := fun m => powFrame t.G t.PP.L (x m) (eL m) k
  have hτg : ∀ m, (τ m).IsGen := fun m => powFrame_isGen (x m) (eL m) (hg m) k
  choose F' hF' using fun m =>
    exists_pullSec t.G t.PP.L k (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) Fs
  choose v hv using fun m => exists_value t.G t.PP.L hL k (F' m) (x m) (τ m) (hτg m)
  have hvc : ∀ m, v m = (ρT x0 d m).left.appTop.hom (v (m + 1)) := by
    intro m
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨i, hi⟩ := exists_chart hL ((x m).left y)
    have hρx : (ρT x0 d m).left ≫ (x (m + 1)).left = (x m).left := by
      rw [← Over.comp_left, hx m]
    have hm : (𝟙 _ : (jOG x0 d m 1).left ⟶ _) y ∈ LB.wchart t.PP.L (fun _ : Fin 1 => (x m).left) (fun _ => i) :=
      Set.mem_iInter.2 fun _ => hi
    have app_eq : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C), f ≫ g = h → ∀ a, g (f a) = h a :=
      fun f g h e a => congrArg (fun q => q a) e
    have hps0 : (𝟙 _ ≫ (ptSecT t.G (x m)).left) ≫ (snd (jOG x0 d m 1) t.G).left = (x m).left := by
      rw [Category.id_comp, ← Over.comp_left, ptSecT, lift_snd]
    have hps1 : ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) ≫ (snd (jOG x0 d (m + 1) 1) t.G).left =
        (x m).left := by
      rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd, hρx]
    have hm1 : (ρT x0 d m).left y ∈ LB.wchart t.PP.L (fun _ : Fin 1 => (x (m + 1)).left) (fun _ => i) := by
      refine Set.mem_iInter.2 fun _ => ?_
      show (x (m + 1)).left ((ρT x0 d m).left y) ∈ (t.PP.L.U i : Set t.G.left)
      rw [app_eq _ _ _ hρx]
      exact hi
    have mem0 : (𝟙 _ ≫ (ptSecT t.G (x m)).left) y ∈ (LPow t.G t.PP.L k (jOG x0 d m 1)).U (fun _ => i) := by
      refine Set.mem_iInter.2 fun _ => ?_
      show (snd (jOG x0 d m 1) t.G).left ((𝟙 _ ≫ (ptSecT t.G (x m)).left) y) ∈ (t.PP.L.U i : Set t.G.left)
      rw [app_eq _ _ _ hps0]
      exact hi
    have mem1 : ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) y ∈
        (LPow t.G t.PP.L k (jOG x0 d (m + 1) 1)).U (fun _ => i) := by
      refine Set.mem_iInter.2 fun _ => ?_
      show (snd (jOG x0 d (m + 1) 1) t.G).left (((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) y) ∈
        (t.PP.L.U i : Set t.G.left)
      rw [app_eq _ _ _ hps1]
      exact hi
    have e0 := value_stalk t.G t.PP.L hL k (hv m) (𝟙 _) y (fun _ => i) hm
    have e1 := value_stalk t.G t.PP.L hL k (hv (m + 1)) (ρT x0 d m).left y (fun _ => i) hm1
    have l0 := pullSec_stalk t.G t.PP.L k (hF' m) (𝟙 _ ≫ (ptSecT t.G (x m)).left) y (fun _ => i) mem0
    have l1 := pullSec_stalk t.G t.PP.L k (hF' (m + 1)) ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) y
      (fun _ => i) mem1
    have hmor : (𝟙 _ ≫ (ptSecT t.G (x m)).left) ≫ (jBaseG x0 d m 1 ▷ t.G).left =
        ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) ≫ (jBaseG x0 d (m + 1) 1 ▷ t.G).left := by
      rw [Category.id_comp, Category.assoc]
      simp only [← Over.comp_left]
      refine congrArg (fun f => Over.Hom.left f) ?_
      simp only [ptSecT, lift_whiskerRight, comp_lift, Category.id_comp]
      rw [jBase_trunc, hx m]
    obtain ⟨J, hJ, hJi⟩ := exists_good t.PP.L hL y (fun _ : Fin 1 => (x m).left) (fun _ => i) (fun _ _ _ => rfl)
      (fun _ => hi)
    have p0 : val (τ m) (𝟙 _) y J = val (eL m) (𝟙 _) y J ^ k := map_zpow _ _ _
    have p1 : val (τ (m + 1)) (ρT x0 d m).left y J = val (eL (m + 1)) (ρT x0 d m).left y J ^ k := map_zpow _ _ _
    have hunit : gm (𝟙 _) y (LB.wchart t.PP.L (fun _ : Fin 1 => (x m).left) (fun _ => i)) ((τ m).s (fun _ => i)) =
        gm (ρT x0 d m).left y (LB.wchart t.PP.L (fun _ : Fin 1 => (x (m + 1)).left) (fun _ => i))
          ((τ (m + 1)).s (fun _ => i)) :=
      (val_of (τ m) (𝟙 _) y J (fun _ => i) (fun _ => by rw [Category.id_comp]; exact hJi 0)).symm.trans
        (p0.trans ((congrArg (· ^ k) (htr m y J hJ)).symm.trans (p1.symm.trans
          (val_of (τ (m + 1)) _ y J (fun _ => i) (fun _ => by rw [hρx]; exact hJi 0)))))
    have hmain := e0.symm.trans (l0.trans ((congrArg (fun r => gs r y _ (Fs.f (fun _ => i))) hmor).trans
      (l1.symm.trans e1)))
    have h2 := (Units.mul_left_inj (gm (𝟙 _) y _ ((τ m).s (fun _ => i)))).1
      (hmain.trans (congrArg (fun u => gs (ρT x0 d m).left y ⊤ (v (m + 1)) * (u : (_ : Type)ˣ).val) hunit.symm))
    have h3 := gs_pull (𝟙 _) (ρT x0 d m).left y ⊤ (by trivial) (v (m + 1))
    rw [Category.id_comp] at h3
    exact h2.trans h3.symm
  choose a ha using fun m => (⟨_, congrArg (fun f => CommRingCat.Hom.hom f (v m))
    (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin 1 × Fin d) m))))⟩ :
      ∃ b, toΓ (Jet S (Fin 1 × Fin d) m) b = v m)
  have hac : ∀ m, (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) (a (m + 1)) = a m := by
    intro m
    apply toΓ_injective
    rw [ha m, hvc m, ← ha (m + 1)]
    exact congrArg (fun f => CommRingCat.Hom.hom f (a (m + 1)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) :
        Jet S (Fin 1 × Fin d) (m + 1) →+* Jet S (Fin 1 × Fin d) m)))
  obtain ⟨f, hf⟩ := exists_ps_of_jets a hac
  refine ⟨f, fun m => ⟨F' m, hF' m, ?_⟩⟩
  rw [funOn_eq, hf m, ha m]
  exact hv m

theorem isRigAtZero_iff (eL : FrameL t.G x0 t.PP.L j)
    (htr : ∀ m y J, Good t.PP.L y J → val (eL (m + 1)) (ρT x0 d m).left y J = val (eL m) (𝟙 _) y J)
    {act : 𝓞 E → Germ.Pt S 1 d} {e : ∀ m, FrTyG t x0 d (chartEquiv t x0 j) m} {wP : PrimTyG t}
    (h0 : LB.Gen.Corr t.PP.L _ _ _ _ (eL 0) (eLG t x0 d (chartEquiv t x0 j) act e wP 0)) :
    IsRigAtZero t.PP eL ↔ Rig0G t x0 d (chartEquiv t x0 j) act e wP := by
  have hL := t.PP.isLB
  have k0 : ∀ y J, Good t.PP.L y J →
      val (LB.pullGen t.PP.L _ _ (eL 0) (algMap x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (𝟙 _) y J =
      val (LB.pullGen t.PP.L _ _ (eLG t x0 d (chartEquiv t x0 j) act e wP 0)
        (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (𝟙 _) y J := fun y J hJ =>
    (val_pull hJ _ _ _).trans ((val_corr hJ h0 _).trans (val_pull hJ _ _ _).symm)
  refine ⟨fun h => corr_of_val hL fun y J hJ => (k0 y J hJ).symm.trans (val_corr hJ (h 0) _), fun h m => ?_⟩
  induction m with
  | zero => exact corr_of_val hL fun y J hJ => (k0 y J hJ).trans (val_corr hJ h _)
  | succ m ih =>
    have hc : LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ (eL (m + 1)) (ρT x0 d m).left) (eL m) :=
      corr_of_val hL fun y J hJ => (val_pull hJ _ _ _).trans
        ((congrArg (fun r => val (eL (m + 1)) r y J) (Category.id_comp _)).trans (htr m y J hJ))
    have ha : homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ ρT x0 d m =
        homAt x0 (jetAug : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] S) := by
      rw [homAt_comp]
      exact congrArg (homAt x0) (jet_hom_ext fun s => rfl)
    refine corr_of_val hL fun y J hJ => Eq.trans ?_ (val_corr hJ ih _)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_corr hJ hc _).symm).symm)
    refine Eq.trans (congrArg (fun r => val (eL (m + 1)) r y J) ?_) (val_pull hJ _ _ _).symm
    rw [Category.assoc, algMap_eq, algMap_eq, ← Over.comp_left, ha]

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem starRing_eq (st : StarRing (𝓞 E)) (h : ∀ a : 𝓞 E, star a = H.bar a) : st = H.starRing := by
  obtain @⟨@⟨@⟨⟨s⟩, _⟩, _⟩, _⟩ := st
  obtain rfl : s = fun a => H.bar a := funext h
  rfl

section Chart

variable {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S}

variable (y) in

abbrev BarChart : Type := @ChartAt E _ _ _ H Dw l Xo c H.starRing S _ _ (ratAlg c S) y

abbrev Compat (C : BarChart y) : Prop :=
  letI := H.starRing
  letI := ratAlg c S
  FrTruncC y C

variable {d : ℕ} {j : JetPts Xo.univ.t.G y.x d} {e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j} {B : FBar H S d}
  {cf : Lt1 Dw → Fin d → S} {h : Germ.PS S 2 d} {eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j}

theorem isGaugedChart_iff : IsGaugedChart y j e B cf h eL ↔
    letI := H.starRing
    letI := ratAlg c S
    ∃ wP : PrimTyG Xo.univ.t,
      (IsChartG Xo.univ.t y.x d B.G.F B.A.act (fun ℓ : Lt1 Dw => y.u ℓ.1 ℓ.2) cf (chartEquiv _ y.x j) ∧
        IsFrameG Xo.univ.t y.x d (chartEquiv _ y.x j) B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad (frameEquiv _ y.x j e) ∧
        IsPrimG Xo.univ.t wP ∧ B.IsCanonGauge S h ∧
        Rig0G Xo.univ.t y.x d (chartEquiv _ y.x j) B.A.act (frameEquiv _ y.x j e) wP) ∧
      FrTrunc Xo.univ.t y.x d (chartEquiv _ y.x j) (frameEquiv _ y.x j e) ∧
      ∀ m, (eL m).IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eL m)
        (eLG Xo.univ.t y.x d (chartEquiv _ y.x j) B.A.act (frameEquiv _ y.x j e) wP m) := by
  letI := H.starRing
  letI := ratAlg c S
  have tr : ∀ wP : PrimTyG Xo.univ.t,
      IsChartG Xo.univ.t y.x d B.G.F B.A.act (fun ℓ : Lt1 Dw => y.u ℓ.1 ℓ.2) cf (chartEquiv _ y.x j) →
      FrTrunc Xo.univ.t y.x d (chartEquiv _ y.x j) (frameEquiv _ y.x j e) →
      (∀ m, (eL m).IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eL m)
        (eLG Xo.univ.t y.x d (chartEquiv _ y.x j) B.A.act (frameEquiv _ y.x j e) wP m)) →
      ∀ m z J, Good Xo.univ.t.PP.L z J → val (eL (m + 1)) (ρT y.x d m).left z J = val (eL m) (𝟙 _) z J :=
    fun wP hc ht hL m z J hJ => (val_corr hJ (hL (m + 1)).2 _).trans
      ((val_eL_trunc hc _ wP ht m z J hJ).trans (val_corr hJ (hL m).2 _).symm)
  constructor
  · rintro ⟨hc, hr, hg, ⟨-, w, hw, hL⟩, h0⟩
    have hc' := (ChartCompare.isChartOf_iff_framed y j B.G B.A cf).1 hc
    obtain ⟨-, hf, ht⟩ := (FrameCompare.realises_iff e B).1 hr
    rw [← frameEquiv_eq] at hf ht
    have hL' := ((isFrameLVia_iff B.A.act e w eL).1 hL).2.2
    exact ⟨_, ⟨hc', hf, (isPrim_iff_isPrimG _ w).1 hw, hg,
      (isRigAtZero_iff eL (tr _ hc' ht hL') (hL' 0).2).1 h0⟩, ht, hL'⟩
  · rintro ⟨wP, ⟨hc', hf, hw, hg, h0⟩, ht, hL'⟩
    obtain ⟨w, rfl⟩ := (primEquiv Xo.univ.t).surjective wP
    have hc := (ChartCompare.isChartOf_iff_framed y j B.G B.A cf).2 hc'
    have hr : Realises Xo.univ.t y.x j e B := (FrameCompare.realises_iff e B).2
      ⟨⟨fun _ => rfl, hc.1, hc.2.1, hc.2.2.1⟩, by rw [← frameEquiv_eq]; exact ⟨hf, ht⟩⟩
    exact ⟨hc, hr, hg, ⟨hc.1, w, (isPrim_iff_isPrimG _ w).2 hw,
      (isFrameLVia_iff B.A.act e w eL).2 ⟨hr.2.2.2.2.1, hc.2.2.1 H.w0, hL'⟩⟩,
      (isRigAtZero_iff eL (tr _ hc' ht hL') (hL' 0).2).2 h0⟩

theorem existsUnique_germ (hg : IsGaugedChart y j e B cf h eL) (k : ℤ) (F : SecAt y k) :
    ∃! f, IsGermIn eL k F f := by
  obtain ⟨wP, ⟨hc, -⟩, ht, hL⟩ := isGaugedChart_iff.1 hg
  obtain ⟨f, hf⟩ := exists_isGermIn eL (fun m => (hL m).1) hc.trunc (fun m z J hJ =>
    (val_corr hJ (hL (m + 1)).2 _).trans ((val_eL_trunc hc _ wP ht m z J hJ).trans (val_corr hJ (hL m).2 _).symm)) k F
  exact ⟨f, hf, fun f' hf' => isGermIn_unique eL k F f' f hf' hf⟩

variable (j e B cf h eL) in

def SameData (C : BarChart y) : Prop :=
  letI := H.starRing
  letI := ratAlg c S
  ∃ wP hc hf hp hg hr, C = ⟨d, B, cf, chartEquiv _ y.x j, frameEquiv _ y.x j e, wP, h, hc, hf, hp, hg, hr⟩ ∧
    ∀ m, (eL m).IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eL m)
      (eLG Xo.univ.t y.x d (chartEquiv _ y.x j) B.A.act (frameEquiv _ y.x j e) wP m)

theorem isGaugedChart_iff_chartAt : IsGaugedChart y j e B cf h eL ↔
    ∃ C : BarChart y, SameData j e B cf h eL C ∧ Compat C := by
  letI := H.starRing
  letI := ratAlg c S
  refine isGaugedChart_iff.trans ⟨?_, ?_⟩
  · rintro ⟨wP, ⟨hc, hf, hp, hg, hr⟩, ht, hL⟩
    exact ⟨_, ⟨wP, (isChart_iff y d _ _ _ _).2 hc, (Formalism.L2.Pj.isFrame_iff y d _ _ _ _ _ _ _ _).2 hf, hp, hg, hr,
      rfl, hL⟩, ht⟩
  · rintro ⟨_, ⟨wP, hc, hf, hp, hg, hr, rfl, hL⟩, ht⟩
    exact ⟨wP, ⟨(isChart_iff y d _ _ _ _).1 hc, (Formalism.L2.Pj.isFrame_iff y d _ _ _ _ _ _ _ _).1 hf, hp, hg, hr⟩, ht, hL⟩

theorem exists_sameData (C : BarChart y) :
    letI := H.starRing
    letI := ratAlg c S
    ∃ j e eL, SameData j e C.B C.uvec C.h eL C := by
  letI := H.starRing
  letI := ratAlg c S
  obtain ⟨d, B, cf, x, e, wP, h, hc, hf, hp, hg, hr⟩ := C
  obtain ⟨j, rfl⟩ := (chartEquiv Xo.univ.t y.x).surjective x
  obtain ⟨e, rfl⟩ := (frameEquiv Xo.univ.t y.x j).surjective e
  obtain ⟨w, rfl⟩ := (primEquiv Xo.univ.t).surjective wP
  obtain ⟨eL, hL⟩ := exists_frameL B.A.act e w ((isGen_primEquiv _ w).1 hp.1)
    (fun m => (isGen_frameEquiv e m).1 (hf.gen m)) (fun m => hc.act m H.w0)
  exact ⟨j, e, eL, _, hc, hf, hp, hg, hr, rfl, hL⟩

def ComputesNat (C : BarChart y) (v : ∀ k : ℤ, SecAt y k → (Lt1 Dw →₀ ℕ) → S) : Prop :=
  letI := H.starRing
  letI := ratAlg c S
  (∀ (k : ℕ) (F : SecAt y k), ∃ f, Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) ∧
    ∀ (k : ℕ) (F : SecAt y k) (f : MvPowerSeries (Fin 1 × Fin C.d) S),
      Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
        ∀ α : Lt1 Dw →₀ ℕ, v k F α = C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1)

theorem computesNat_iff {C : BarChart y} (hC : SameData j e B cf h eL C)
    (v : ∀ k : ℤ, SecAt y k → (Lt1 Dw →₀ ℕ) → S) : ComputesNat C v ↔
    ∀ (k : ℕ) (F : SecAt y k), ∃ f, IsGermIn eL k F f ∧ ∀ α, v k F α = IndefiniteRowSideFullHecke.HarmonicChartValues.chartVal c B cf h k f α := by
  letI := H.starRing
  letI := ratAlg c S
  obtain ⟨wP, hc, hf, hp, hg, hr, rfl, hL⟩ := hC
  obtain ⟨w, rfl⟩ := (primEquiv Xo.univ.t).surjective wP
  have g := fun k F f => (isGermIn_iff B.A.act e w eL (fun m => (hL m).2) k F f).trans
    (isGerm_iff y d _ _ _ _ k F f).symm
  have n : ∀ (k : ℕ) f α, IndefiniteRowSideFullHecke.HarmonicChartValues.chartVal c B cf h k f α =
      B.nabVal S h H.w0 k f cf (MvPolynomial.monomial α 1) := fun k f α => monVal_natCast B h H.w0 k f cf α
  constructor
  · rintro ⟨h1, h2⟩ k F
    obtain ⟨f, hf⟩ := h1 k F
    exact ⟨f, (g k F f).2 hf, fun α => (h2 k F f hf α).trans (n k f α).symm⟩
  · refine fun hv => ⟨fun k F => (hv k F).imp fun f hf => (g k F f).1 hf.1, fun k F f hf α => ?_⟩
    obtain ⟨f', h1, h2⟩ := hv k F
    obtain rfl := isGermIn_unique eL k F f f' ((g k F f).2 hf) h1
    exact (h2 α).trans (n k f α)

theorem computesNat_iff_extends (v : ∀ k : ℤ, SecAt y k → (Lt1 Dw →₀ ℕ) → S) :
    (∃ C : BarChart y, Compat C ∧ ComputesNat C v) ↔
      ∃ v', IsNablaAt y v' ∧ ∀ (k : ℕ) F α, v k F α = v' k F α := by
  constructor
  · rintro ⟨C, ht, hv⟩
    obtain ⟨j, e, eL, hC⟩ := exists_sameData C
    have hg := isGaugedChart_iff_chartAt.2 ⟨C, hC, ht⟩
    choose f hf hu using existsUnique_germ hg
    refine ⟨fun k F α => IndefiniteRowSideFullHecke.HarmonicChartValues.chartVal c _ _ _ k (f k F) α,
      ⟨_, j, e, _, _, _, eL, hg, fun k F => ⟨f k F, hf k F, fun _ => rfl⟩⟩, fun k F α => ?_⟩
    obtain ⟨f', h1, h2⟩ := (computesNat_iff hC v).1 hv k F
    rw [h2 α, hu k F f' h1]
  · rintro ⟨v', ⟨d, j, e, B, cf, h, eL, hg, hv⟩, hvv⟩
    obtain ⟨C, hC, ht⟩ := isGaugedChart_iff_chartAt.1 hg
    exact ⟨C, ht, (computesNat_iff hC v).2 fun k F =>
      (hv k F).imp fun f hf => ⟨hf.1, fun α => (hvv k F α).trans (hf.2 α)⟩⟩

theorem isNablaAt_zero {v : ∀ k : ℤ, SecAt y k → (Lt1 Dw →₀ ℕ) → S} (hv : IsNablaAt y v) (k : ℤ)
    (α : Lt1 Dw →₀ ℕ) : v k (zeroSec _ k _) α = 0 := by
  obtain ⟨d, j, e, B, cf, h, eL, -, hv⟩ := hv
  obtain ⟨f, h1, h2⟩ := hv k (zeroSec _ k _)
  obtain rfl := isGermIn_unique eL k _ f 0 h1 (isGermIn_zero eL k)
  letI := H.starRing
  letI := ratAlg c S
  rw [h2, IndefiniteRowSideFullHecke.HarmonicChartValues.chartVal, monVal, zero_mul, ReciprocityTheory.ChartRestriction.G.TB.GE.dmonOf_zero, map_zero]

end Chart

section Pin

variable (Xo c)

def IsNabCompat [StarRing (𝓞 E)] (nab : NabV Xo c) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) ∧
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S),
    ∃ C : ChartAt Xo c y, FrTruncC y C ∧
      (∀ (k : ℕ) (F : SecAt y k), ∃ f, Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) ∧
      ∀ (k : ℕ) (F : SecAt y k) (f : MvPowerSeries (Fin 1 × Fin C.d) S),
        Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
          ∀ α : Lt1 Dw →₀ ℕ, nab y k F α = C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1)

variable {Xo c}

theorem compat_of_germs [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
    (C : ChartAt Xo c y)
    (h : ∀ (k : ℕ) (F : SecAt y k), ∃ f, Formalism.L2.Pj.IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) : FrTruncC y C :=
  haveI := Xo.univ.proper
  FrameCompatOfGerms.frTrunc_of_germs Xo.univ.ample ((isChart_iff y C.d _ _ _ _).1 C.chart)
    ((Formalism.L2.Pj.isFrame_iff y C.d _ _ _ _ _ _ _ _).1 C.frame) (wP := C.wP)
    fun k F => (h k F).imp fun f hf => (isGerm_iff y C.d _ _ _ _ k F f).1 hf

def AgreeNat (nab nab' : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) (F : SecAt y k) (α : Lt1 Dw →₀ ℕ),
    nab y k F α = nab' y k F α

theorem IsNabCompat.isNab [StarRing (𝓞 E)] {nab : NabV Xo c} (h : IsNabCompat Xo c nab) : IsNab Xo c nab :=
  ⟨h.1, fun S _ _ _ y => (h.2 S y).imp fun _ hC => hC.2⟩

theorem isNab_iff_compat [StarRing (𝓞 E)] (nab : NabV Xo c) :
    IsNab Xo c nab ↔ IsNabCompat Xo c nab :=
  ⟨fun h => ⟨h.1, fun S _ _ _ y => (h.2 S y).imp fun C hC => ⟨compat_of_germs C hC.1, hC⟩⟩, IsNabCompat.isNab⟩

theorem isNabCompat_iff [st : StarRing (𝓞 E)] (nab : NabV Xo c) :
    IsNabCompat Xo c nab ↔
      (∀ a : 𝓞 E, star a = H.bar a) ∧ ∃ nab' : NabV Xo c, IsNablaPin Xo c nab' ∧ AgreeNat nab nab' := by
  refine and_congr_right fun hs => ?_
  obtain rfl := starRing_eq st hs
  constructor
  · intro h
    have h' : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
        ∃ v', IsNablaAt y v' ∧ ∀ (k : ℕ) F α, nab y k F α = v' k F α := fun S _ _ y =>
      (computesNat_iff_extends fun k F α => nab y k F α).1 (@h S _ _ (ratAlg c S) y)
    choose v hv using h'
    exact ⟨fun y => v _ y, fun S _ _ y => (hv S y).1, fun S _ _ y => (hv S y).2⟩
  · rintro ⟨nab', h, ha⟩ S _ _ q y
    obtain rfl : q = ratAlg c S := Subsingleton.elim _ _
    exact (computesNat_iff_extends fun k F α => nab y k F α).2 ⟨_, h S y, ha S y⟩

theorem isNab_of_isNablaPin [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a) {nab : NabV Xo c}
    (h : IsNablaPin Xo c nab) : IsNab Xo c nab :=
  ((isNabCompat_iff nab).2 ⟨hs, nab, h, fun _ _ _ _ _ _ _ => rfl⟩).isNab

theorem isNab_iff [StarRing (𝓞 E)] (nab : NabV Xo c) :
    IsNab Xo c nab ↔
      (∀ a : 𝓞 E, star a = H.bar a) ∧ ∃ nab' : NabV Xo c, IsNablaPin Xo c nab' ∧ AgreeNat nab nab' :=
  (isNab_iff_compat nab).trans (isNabCompat_iff nab)

theorem isNab_iff_nat [StarRing (𝓞 E)] (nab : NabV Xo c) :
    IsNab Xo c nab ↔ (∀ a : 𝓞 E, star a = H.bar a) ∧
      ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
        ∃ (d : ℕ) (j : JetPts Xo.univ.t.G y.x d) (e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j) (B : FBar H S d)
          (cf : Lt1 Dw → Fin d → S) (h : Germ.PS S 2 d) (eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j),
          IsGaugedChart y j e B cf h eL ∧ ∀ (k : ℕ) (F : SecAt y k), ∃ f : Germ.PS S 1 d, IsGermIn eL k F f ∧
            ∀ α : Lt1 Dw →₀ ℕ, nab y k F α = IndefiniteRowSideFullHecke.HarmonicChartValues.chartVal c B cf h k f α := by
  refine (isNab_iff nab).trans (and_congr_right fun _ => ⟨?_, fun h => ?_⟩)
  · rintro ⟨nab', h, ha⟩ S _ _ y
    obtain ⟨d, j, e, B, cf, g, eL, hg, hv⟩ := h S y
    exact ⟨d, j, e, B, cf, g, eL, hg, fun k F =>
      (hv k F).imp fun f hf => ⟨hf.1, fun α => (ha S y k F α).trans (hf.2 α)⟩⟩
  · have h' : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
        ∃ v', IsNablaAt y v' ∧ ∀ (k : ℕ) F α, nab y k F α = v' k F α := fun S _ _ y => by
      obtain ⟨d, j, e, B, cf, g, eL, hg, hv⟩ := h S y
      obtain ⟨C, hC, ht⟩ := isGaugedChart_iff_chartAt.1 hg
      exact (computesNat_iff_extends fun k F α => nab y k F α).1 ⟨C, ht, (computesNat_iff hC _).2 hv⟩
    choose v hv using h'
    exact ⟨fun y => v _ y, fun S _ _ y => (hv S y).1, fun S _ _ y => (hv S y).2⟩

theorem AgreeNat.thExpr_eq {nab nab' : NabV Xo c} (h : AgreeNat nab nab') {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (F : Fin n → SecAt y ((l.M : ℤ) ^ 2)) :
    thExpr Xo c nab y P F = thExpr Xo c nab' y P F := by
  have key : ∀ (k : ℤ), 0 ≤ k → ∀ (F : SecAt y k) α, nab y k F α = nab' y k F α := by
    intro k hk
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact h S y k
  simp only [thExpr, key _ (sq_nonneg _)]

theorem polyVal_eq_of_chartIndep (hC : ChartIndepSt2) [StarRing (𝓞 E)] {nab nab' : NabV Xo c} (h : IsNab Xo c nab)
    (h' : IsNablaPin Xo c nab') {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k n : ℕ)
    (F : Fin n → SecAt y k) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n) :
    polyVal c P (fun b => nab y k (F b)) = polyVal c P fun b => nab' y k (F b) :=
  letI := ratAlg c S
  thExprUniq_of_chartIndep2 hC E H Dw l Xo c nab nab' h (isNab_of_isNablaPin h.1 h') S y k n F a P hP

theorem exists_isNab_not_isNablaPin [StarRing (𝓞 E)] {nab : NabV Xo c} (h : IsNab Xo c nab)
    {S : Type} [CommRing S] [Nontrivial S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ nab' : NabV Xo c, IsNab Xo c nab' ∧ AgreeNat nab' nab ∧ ¬ IsNablaPin Xo c nab' := by
  let nab' : NabV Xo c := fun y k F α => if k < 0 then 1 else nab y k F α
  have ha : AgreeNat nab' nab := fun _ _ _ _ k _ _ => if_neg (not_lt.2 (Int.natCast_nonneg k))
  refine ⟨nab', ⟨h.1, fun T _ _ _ z => (h.2 T z).imp fun C hC =>
    ⟨hC.1, fun k F f hf α => (ha T z k F α).trans (hC.2 k F f hf α)⟩⟩, ha, fun hp => ?_⟩
  exact one_ne_zero ((if_pos (by decide)).symm.trans (isNablaAt_zero (hp S y) (-1) 0))

end Pin

end GlobalTheory.NablaPinCompare
