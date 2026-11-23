import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RosLevel
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PreUniformization
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratingFramesComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesGeneratingAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetEvaluationPowerSeriesStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv.Transport

open GlobalTheory.TorusModel

theorem exists_refine {S : Scheme.{0}} {H T₁ T₂ Z : Over S} [IsSeparated H.hom] [IsFinite T₁.hom] [IsFinite T₂.hom]
    {w₁ : T₁ ⟶ H} {w₂ : T₂ ⟶ H} {k₁ : Z ⟶ T₁} {k₂ : Z ⟶ T₂} (h : k₁ ≫ w₁ = k₂ ≫ w₂) :
    ∃ (T : Over S) (_ : IsFinite T.hom) (p₁ : T ⟶ T₁) (p₂ : T ⟶ T₂) (k : Z ⟶ T),
      p₁ ≫ w₁ = p₂ ≫ w₂ ∧ k ≫ p₁ = k₁ ∧ k ≫ p₂ = k₂ := by
  have : IsFinite (w₂.left ≫ H.hom) := by rw [Over.w]; infer_instance
  have : IsFinite w₂.left := IsFinite.of_comp w₂.left H.hom
  have hl : k₁.left ≫ w₁.left = k₂.left ≫ w₂.left := congrArg (·.left) h
  refine ⟨Over.mk (pullback.fst w₁.left w₂.left ≫ T₁.hom),
    inferInstanceAs (IsFinite (pullback.fst w₁.left w₂.left ≫ T₁.hom)), Over.homMk (pullback.fst _ _) rfl,
    Over.homMk (pullback.snd _ _) ?_, Over.homMk (pullback.lift k₁.left k₂.left hl) ?_,
    Over.OverMorphism.ext pullback.condition, Over.OverMorphism.ext (pullback.lift_fst _ _ _),
    Over.OverMorphism.ext (pullback.lift_snd _ _ _)⟩
  · change pullback.snd w₁.left w₂.left ≫ T₂.hom = pullback.fst w₁.left w₂.left ≫ T₁.hom
    rw [← Over.w w₂, ← Over.w w₁, pullback.condition_assoc]
  · change pullback.lift k₁.left k₂.left hl ≫ pullback.fst w₁.left w₂.left ≫ T₁.hom = Z.hom
    rw [pullback.lift_fst_assoc, Over.w]

def rat {X X' Y Z : Scheme.{0}} {L : LB X'} {M : LB X} {ψ' : Y ⟶ X'} {ψ : Y ⟶ X} (g' : Frame L ψ') (g : Frame M ψ)
    (r : Z ⟶ Y) (z : Z) (JM : (Z ⟶ X) → M.ι) (JL : (Z ⟶ X') → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val g r z JM * (val g' r z JL)⁻¹

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G)
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} (Y : Ray oa)

def Near {Z : Over (Sp R)} (x : Z ⟶ Y.H) (x' : Z ⟶ G) : Prop :=
  ∃ (T : Over (Sp R)) (_ : IsFinite T.hom) (k : Z ⟶ T) (w : T ⟶ Y.H) (w' : T ⟶ G),
    IsPointOf U (Y.Φ T w) w' ∧ k ≫ w = x ∧ k ≫ w' = x'

def Tr {Z : Over (Sp R)} (x : Z ⟶ Y.H) (x' : Z ⟶ G) {b' : Z.left ⟶ G.left} {b : Z.left ⟶ D.toPre.P.A.left}
    (e' : Frame U.LG.L b') (e : Frame D.toPre.P.L b) : Prop :=
  ∃ (T : Over (Sp R)) (_ : IsFinite T.hom) (k : Z ⟶ T) (w : T ⟶ Y.H) (w' : T ⟶ G) (c : T.left ⟶ D.toPre.P.A.left)
    (g' : Frame U.LG.L w'.left) (g : Frame D.toPre.P.L c),
    IsPointOf U (Y.Φ T w) w' ∧ k ≫ w = x ∧ k ≫ w' = x' ∧ c = (w ≫ Y.q).left ∧ g'.IsGen ∧ g.IsGen ∧
    FrRel U w'.left c g' g ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z.left) (z : Z') (JM) (JL), Good D.toPre.P.L z JM →
      Good U.LG.L z JL → rat e' e r z JM JL = rat g' g (r ≫ k.left) z JM JL

variable {U Y}

instance : IsSeparated Y.H.hom := (isSemiAbelian_of_isGt _ _ _ Y.isGt).separated

instance : Smooth Y.H.hom := (isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth

theorem pt_pull {T T' : Over (Sp R)} (k : T' ⟶ T) {w : T ⟶ Y.H} {w' : T ⟶ G} (h : IsPointOf U (Y.Φ T w) w') :
    IsPointOf U (Y.Φ T' (k ≫ w)) (k ≫ w') := h.pull k (Y.rep.1 _ _ k w)

theorem pt_act {ιA : A.OAct O} {a : OAct O G} (hO : U.OLinear O oa ιA a.toRingAct) (c : O) {T : Over (Sp R)}
    {w : T ⟶ Y.H} {w' : T ⟶ G} (h : IsPointOf U (Y.Φ T w) w') :
    IsPointOf U (Y.Φ T (w ≫ Y.act.act c)) (w' ≫ a.act c) :=
  h.smul GlobalTheory.allSixLaws.1.globalFns hO c (Y.smul c T w)

theorem Near.comp {Z Z' : Over (Sp R)} {x : Z ⟶ Y.H} {x' : Z ⟶ G} (h : Near U Y x x') (r : Z' ⟶ Z) :
    Near U Y (r ≫ x) (r ≫ x') := by
  obtain ⟨T, hT, k, w, w', hw, rfl, rfl⟩ := h
  exact ⟨T, hT, r ≫ k, w, w', hw, Category.assoc _ _ _, Category.assoc _ _ _⟩

theorem Near.act {ιA : A.OAct O} {a : OAct O G} (hO : U.OLinear O oa ιA a.toRingAct) (c : O) {Z : Over (Sp R)}
    {x : Z ⟶ Y.H} {x' : Z ⟶ G} (h : Near U Y x x') : Near U Y (x ≫ Y.act.act c) (x' ≫ a.act c) := by
  obtain ⟨T, hT, k, w, w', hw, rfl, rfl⟩ := h
  exact ⟨T, hT, k, _, _, pt_act hO c hw, (Category.assoc _ _ _).symm, (Category.assoc _ _ _).symm⟩

theorem FrRel.pull {T T' : Scheme.{0}} {x' : T ⟶ G.left} {b : T ⟶ D.toPre.P.A.left} {g' : Frame U.LG.L x'}
    {g : Frame D.toPre.P.L b} (h : FrRel U x' b g' g) (p : T' ⟶ T) :
    FrRel U (p ≫ x') (p ≫ b) (LB.pullGen _ _ _ g' p) (LB.pullGen _ _ _ g p) := fun e Z r y hy z JM JL hM hL =>
  (val_pull hM g p r).trans ((h e Z (r ≫ p) y (hy.trans (Category.assoc _ _ _).symm) z JM JL hM hL).trans
    (congrArg _ (val_pull hL g' p r).symm))

variable [IsNoetherianRing R] [hc : IsAdicComplete (maximalIdeal R) R]

theorem adic (T : Over (Sp R)) [IsFinite T.hom] : IsAdicColimit (maximalIdeal R) T :=
  FiniteTorsLift.isAdicColimit_of_isFinite_noetherian hc T

theorem pt_unique {T : Over (Sp R)} [IsFinite T.hom] {w : T ⟶ Y.H} {w' w'' : T ⟶ G} (h : IsPointOf U (Y.Φ T w) w')
    (h' : IsPointOf U (Y.Φ T w) w'') : w' = w'' := (existsUnique_point U (adic T) _).unique h h'

theorem Near.unique {Z : Over (Sp R)} {x : Z ⟶ Y.H} {x' x'' : Z ⟶ G} (h : Near U Y x x') (h' : Near U Y x x'') :
    x' = x'' := by
  obtain ⟨T, hT, k, w, w', hw, e, rfl⟩ := h
  obtain ⟨T₂, hT₂, k₂, w₂, w₂', hw₂, e₂, rfl⟩ := h'
  obtain ⟨T₃, _, p₁, p₂, l, h₁, rfl, rfl⟩ := exists_refine (e.trans e₂.symm)
  rw [Category.assoc, Category.assoc, pt_unique (pt_pull p₁ hw) (h₁ ▸ pt_pull p₂ hw₂)]

variable (U Y) in

def Loc {Z : Over (Sp R)} (x : Z ⟶ Y.H) (x' : Z ⟶ G) (e' : Frame U.LG.L x'.left)
    (e : Frame D.toPre.P.L (x ≫ Y.q).left) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra R W) (_ : Module.Finite R W)
    (k : Z ⟶ Over.mk (spMap (algebraMap R W))) (w : Over.mk (spMap (algebraMap R W)) ⟶ Y.H)
    (w' : Over.mk (spMap (algebraMap R W)) ⟶ G) (g' : Frame U.LG.L w'.left) (g : Frame D.toPre.P.L (w ≫ Y.q).left)
    (ρ : Γ(Z.left, ⊤)ˣ), IsPointOf U (Y.Φ _ w) w' ∧ k ≫ w = x ∧ k ≫ w' = x' ∧ g'.IsGen ∧ g.IsGen ∧
    FrRel U w'.left (w ≫ Y.q).left g' g ∧
    (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z.left) (z : Z') (J), Good U.LG.L z J →
      val e' r z J = gm r z ⊤ ρ * val g' (r ≫ k.left) z J) ∧
    ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z.left) (z : Z') (J), Good D.toPre.P.L z J →
      val e r z J = gm r z ⊤ ρ * val g (r ≫ k.left) z J

section Loc

variable {Z : Over (Sp R)} {x : Z ⟶ Y.H} {x' : Z ⟶ G} {e' : Frame U.LG.L x'.left}
  {e : Frame D.toPre.P.L (x ≫ Y.q).left} (h : Loc U Y x x' e' e)
include h

end Loc

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] hc in
theorem gs_toΓ {W J : Type} [CommRing W] [CommRing J] (κ : W →+* J) (y : Sp J) (t : W) :
    gs (spMap κ) y ⊤ (toΓ W t) = gs (𝟙 (Sp J)) y ⊤ (toΓ J (κ t)) := by
  have h := congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom κ))
  have h' : toΓ J (κ t) = (spMap κ).appTop.hom (toΓ W t) := h
  rw [h']
  exact ((gs_pull (𝟙 _) (spMap κ) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm

theorem Loc.germ {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (f : R →+* C)
    (hf : ∀ r, ‖f r‖ ≤ 1) (hf' : ∀ r ∈ maximalIdeal R, ‖f r‖ < 1) {ρ : Type} [Fintype ρ] [DecidableEq ρ] {m : ℕ}
    {x : overAt (spMap f) (Jet C ρ m) ⟶ Y.H} {x' : overAt (spMap f) (Jet C ρ m) ⟶ G} {e' : Frame U.LG.L x'.left}
    {e : Frame D.toPre.P.L (x ≫ Y.q).left} (h : Loc U Y x x' e' e) {k : ℕ} {σ : H0 U.LG.L k}
    {F : ∀ α, D.toPre.SecB k α} (hF : ∀ l, U.ExpandsAt l k σ F) {g : D.toPre.X → MvPowerSeries ρ C}
    (hg : ∀ α y J, Good D.toPre.P.L y J → sval (F α) (x ≫ Y.q).left y J * (val ((Y.Φ _ x).s α) (𝟙 _) y J).val =
      gs (𝟙 _) y ⊤ (toΓ _ (psJet m (g α))) * (val e (𝟙 _) y J ^ k).val) :
    (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → Summable fun α => MvPowerSeries.coeff n (g α)) ∧
      ∀ g₀ : MvPowerSeries ρ C, (∀ n : ρ →₀ ℕ, HasSum (fun α => MvPowerSeries.coeff n (g α)) (MvPowerSeries.coeff n g₀)) →
        ∀ y J, Good U.LG.L y J →
          sval σ x'.left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m g₀)) * (val e' (𝟙 _) y J ^ k).val := by
  obtain ⟨W, _, _, _, _, l, w, w', c', c, u, hw, rfl, rfl, a', a, fr, v', v⟩ := h
  obtain ⟨κ, hκ⟩ : ∃ κ : W →+* Jet C ρ m, spMap κ = l.left := by
    obtain ⟨κ, hκ⟩ := Spec.map_surjective (show Spec (.of (Jet C ρ m)) ⟶ Spec (.of W) from l.left)
    exact ⟨κ.hom, hκ⟩
  have hκ' : ∀ r, κ (algebraMap R W r) = algebraMap C (Jet C ρ m) (f r) := fun r => by
    have h₁ : spMap κ ≫ spMap (algebraMap R W) = spMap (algebraMap C (Jet C ρ m)) ≫ spMap f :=
      (congrArg (· ≫ spMap (algebraMap R W)) hκ).trans (Over.w l)
    rw [← Spec.map_comp, ← Spec.map_comp] at h₁
    exact congrArg (fun q => q.hom r) (Spec.map_injective h₁)
  obtain ⟨s, t, hs, ht, hst⟩ := GlobalTheory.T.frames_generating_at_point R _ D A G U W (algebraMap R W) _ w' hw _
    (congrArg (·.left) (Y.Φ_b w)) c' c a' a fr k σ F hF
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Jet C ρ m, toΓ _ u₀ = (u⁻¹ ^ k).val :=
    ⟨(Scheme.ΓSpecIso (.of (Jet C ρ m))).hom.hom (u⁻¹ ^ k).val, Iso.hom_inv_id_apply _ _⟩
  have key : ∀ (y : Sp (Jet C ρ m)) (a : W) (b : ((Sp (Jet C ρ m)).presheaf.stalk y)ˣ),
      gs (𝟙 _) y ⊤ (toΓ _ (u₀ * κ a)) * ((gm (𝟙 (Sp (Jet C ρ m))) y ⊤ u * b) ^ k).val =
        gs (spMap κ) y ⊤ (toΓ W a) * (b ^ k).val := fun y a b => by
    rw [gs_toΓ, map_mul, gs_mul _ y ⊤ trivial, hu₀]
    erw [gs_unit (𝟙 (Sp (Jet C ρ m))) y ⊤ trivial]
    rw [map_pow, map_inv, mul_right_comm, ← Units.val_mul, ← mul_pow, inv_mul_cancel_left, mul_comm]
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.jet_evaluation_power_series C R _ (maximalIdeal R).fg_of_isNoetherianRing f hf hf' W ρ m κ hκ' _ s t hst u₀ g
    fun α => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Jet C ρ m))).inv).1
      (fn_ext (V := ⊤) fun y _ => by
        obtain ⟨J, hJ⟩ := UU.exists_good_pt D.toPre.P.isLB y
        have e₁ := hg α y J hJ
        have e₂ := ht α _ l.left y J hJ
        have e₃ := ((isPull_iff _ _ _).1 (Y.rep.1 _ _ l w)).2 α y J hJ
        have e₄ := v _ (𝟙 _) y J hJ
        rw [Category.id_comp] at e₄
        refine (val e (𝟙 _) y J ^ k).mul_left_inj.1 (e₁.symm.trans ?_)
        rw [e₄]
        refine Eq.trans ?_ (key y (t α) (val c l.left y J)).symm
        rw [hκ]
        refine Eq.trans (congrArg₂ (· * ·) ?_ (congrArg Units.val e₃)) e₂
        rw [Category.assoc]
        rfl)
  refine ⟨h₁, fun g₀ hg₀ y J hJ => ?_⟩
  have e₄ := v' _ (𝟙 _) y J hJ
  rw [Category.id_comp] at e₄
  rw [h₂ g₀ fun n _ => hg₀ n, e₄]
  refine (hs _ l.left y J hJ).trans (Eq.trans ?_ (key y s _).symm)
  rw [hκ]

open NumberField
open Formalism.MainNotions.DIV.Cons (SCF intO)

end GlobalTheory.RayEv.Transport
