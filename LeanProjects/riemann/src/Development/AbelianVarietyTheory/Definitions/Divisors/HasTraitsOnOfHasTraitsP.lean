import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTraitsP

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GSep

structure GSet where

  o₁ : Type

  Ω₁ : Type
  [ring : CommRing o₁]
  [field : Field Ω₁]
  [alg : Algebra o₁ Ω₁]
  [ar : ArithBase o₁ Ω₁]

  S : ThetaSys o₁ Ω₁

  ρ : S.Real
  big : S.Big

  M : RatModel o₁ Ω₁
  normal : GlobalTheory.IsNormalScheme M.Z
  projM : IsProjOver M.s
  div : M.HasDiv S.th

attribute [instance] GSet.ring GSet.field GSet.alg GSet.ar

variable {I : Type}

def RegAt (X₁ : GSet) (z₁ : X₁.M.Z) {V : Type} [CommRing V] [IsDomain V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) : Prop :=
  ∀ a ∈ X₁.S.R, a ∈ X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)))

def IsAct (X₁ : GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) : Prop := ∀ a, IsMonHom (act a)

structure GMem (X₁ : GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A))
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
    (L : Type) [AddCommGroup L] (mo : L → V) (hL : I → L → L) where
  cn : IsCN V
  loc : IsLocalHom ev
  reg : RegAt X₁ z₁ ev

  yK : X₁.S.R →+* FractionRing V
  yK_eq : ∀ a : X₁.S.R, yK a = X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a

  D : DegData V (maximalIdeal V)

  e₈ : L ≃+ D.toPre.X

  G : Over (Sp V)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  A : PolAV (Sp (FractionRing V))

  U : Unif (maximalIdeal V) D A G

  φ : A.A.left ⟶ X₁.ρ.P.A.left
  cart : IsGrpPullback A.A X₁.ρ.P.A (spMap yK) φ

  wl : LB.Iso A.L (X₁.ρ.P.L.pull φ)
  wl_gen : wl.IsGen
  equiv : ∀ a : I, ∃ E : EndU U.toUnifPre, E.aA.left ≫ φ = φ ≫ (act a).left ∧ ∀ mu, E.h (e₈ mu) = e₈ (hL a mu)
  psi : ∀ mu, ∃ u : Vˣ, Formalism.L2.Pj.PsiCoord D.toPre (e₈ mu) (u * mo mu)

attribute [instance] GMem.grp GMem.comm

namespace GMem
variable {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {L : Type} [AddCommGroup L] {mo : L → V} {hL : I → L → L} (𝔪 : GMem X₁ z₁ act V ev L mo hL)

def YY (a : X₁.S.Gam) (mu : L) : Prop :=
  ∃ (p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N))
    (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), p.y = 𝔪.e₈ mu ∧
    QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p x ∧
    x.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left

def Over' (w₀ : W0 𝔪.U.toUnifPre) (g' : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b)
    (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ wk : Frm 𝔪.D.toPre (FractionRing V) k g'.b,
    (∀ z J, Good 𝔪.D.toPre.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k) → wk.IsGen →
    ∀ (s : SecA 𝔪.A (FractionRing V) k) (s' : Fam 𝔪.D.toPre (FractionRing V) k) (v : FractionRing V),
      𝔪.U.ExpandsF (FractionRing V) k w₀ s s' → ValAt s x fr v → SumF (maximalIdeal V) (FractionRing V) (coef s' g' wk) v

def Terms (x₀ : X₁.S.Gam) {C : Type} (lab : C → X₁.S.Gam) (T : L → C → V) : Prop :=
  ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
    (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
    (w : ∀ c, Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
    (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧
    (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧
    (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ w₀.IsGen ∧
    𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s ∧
    (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
      𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) ∧
    ∀ mu c, algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ = coef s (g' c) (w c) (𝔪.e₈ mu)

def LatTo {V' : Type} [CommRing V'] [IsDomain V'] [IsLocalRing V'] {ev' : X₁.M.Z.presheaf.stalk z₁ →+* V'}
    {L' : Type} [AddCommGroup L'] {mo' : L' → V'} {hL' : I → L' → L'} (𝔪' : GMem X₁ z₁ act V' ev' L' mo' hL') : Prop :=
  ∃ K : L ≃+ L', (∀ a mu, K (hL a mu) = hL' a (K mu)) ∧ ∀ a mu, 𝔪.YY a mu → 𝔪'.YY a (K mu)

theorem LatTo.refl : 𝔪.LatTo 𝔪 := ⟨AddEquiv.refl _, fun _ _ => rfl, fun _ _ h => h⟩

omit 𝔪 in

theorem nonempty_of_regular (hact : IsAct X₁ act) (hz : X₁.S.R ≤ X₁.M.O z₁) (hV : IsCN V)
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (hev : IsLocalHom ev) (L : Type) [AddCommGroup L] [Subsingleton L]
    (hL : I → L → L) : Nonempty (GMem X₁ z₁ act V ev L (fun _ => 1) hL) := by
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  let yV : X₁.S.R →+* V := (RatModel.valLoc (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) z₁ (sp _)).comp
    (Subalgebra.inclusion hz).toRingHom
  let P := StrictPull.polPull X₁.ρ.P (spMap yV)
  letI := P.isAb.comm
  obtain ⟨D, A, U, ψ, hX, hψ, hL', hE⟩ := Sep.exists_unif_good hV P
  have r : LBIso P.L (X₁.ρ.P.L.pull (pullback.fst X₁.ρ.P.A.hom (spMap yV))) := PolBaseChange.lbIso_refl P.isLB
  obtain ⟨wl, hwl⟩ := LBIso.trans A.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hL' (lbIso_pull_comp r ψ)
  haveI := hV.2.2.2
  obtain ⟨r₀, hr₀, -, -, hu⟩ := (PsiCoordLocal.main V D hV.2.1 0).1
  refine ⟨{
    cn := hV
    loc := hev
    reg := fun a ha => RatModel.O_le_of_specializes (sp _) (hz ha)
    yK := (algebraMap V (FractionRing V)).comp yV
    yK_eq := fun a => (RatModel.val_spMap_comp (M := X₁.M) (algebraMap V (FractionRing V)) _ (sp _) ⟨a.1, hz a.2⟩).symm
    D := D
    e₈ := ⟨⟨fun _ => 0, fun _ => 0, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩,
      fun _ _ => Subsingleton.elim _ _⟩
    G := P.A
    semi := isSemiAbelian_of_isAbelianScheme _ P.isAb
    A := A
    U := U
    φ := ψ ≫ pullback.fst X₁.ρ.P.A.hom (spMap yV)
    cart := (hψ.comp (isGrpPullback_pullback X₁.ρ.P.A (spMap yV))).congr
      (Spec.map_comp (CommRingCat.ofHom yV) (CommRingCat.ofHom (algebraMap V (FractionRing V)))).symm rfl
    wl := wl
    wl_gen := hwl
    equiv := fun a => ?_
    psi := fun mu => ⟨(hu rfl).unit, ?_⟩ }⟩
  · have := hact a
    obtain ⟨E, h⟩ := hE ((Over.pullback (spMap yV)).map (act a))
      (inferInstanceAs (IsMonHom ((Over.pullback (spMap yV)).map (act a))))
    refine ⟨E, ?_, fun _ => Subsingleton.elim _ _⟩
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans ((Category.assoc _ _ _).trans
      ((congrArg (ψ ≫ ·) (pullback.lift_fst _ _ _)).trans (Category.assoc _ _ _).symm)))
  · rw [_root_.mul_one]
    exact hr₀

end GMem

theorem exists_gMem (X₁ : GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (h : IsAct X₁ act) :
    ∃ (z₁ : X₁.M.Z) (ev : X₁.M.Z.presheaf.stalk z₁ →+* X₁.Ω₁),
      Nonempty (GMem X₁ z₁ act X₁.Ω₁ ev PUnit (fun _ => 1) (fun _ x => x)) := by
  refine ⟨_, (Scheme.stalkClosedPointTo (R := CommRingCat.of X₁.Ω₁) X₁.M.pt).hom,
    GMem.nonempty_of_regular h ?_ ⟨inferInstance, inferInstance, ?_, X₁.ar.char⟩ _ inferInstance _ _⟩
  · exact le_top.trans ((congrArg X₁.M.O (X₁.M.pt_apply _)).trans X₁.M.O_genericPoint).ge
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance

def IsGeo {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} (X₁ : GSet) (z₁ : X₁.M.Z)
    (act : O → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (Φ : VPre bar q W (X₁.M.Z.presheaf.stalk z₁))
    (lab : Φ.Q → X₁.S.Gam) : Prop :=
  X₁.M.Div X₁.S.th x₀ z₁ ∧ Set.range lab = X₁.S.HH X₁.M z₁ ∧
    ∀ y, ∃ 𝔪 : GMem X₁ z₁ act (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) (mono W (Φ.t y) (Φ.δ y)) (fun a mu => a • mu),
      𝔪.Terms x₀ lab (Φ.term y)

open Classical in

def ZHAbove (X₁ : GSet) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) : Prop :=
  ∃ (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J), Nonempty (ZHOut X₁.ρ Y U₀ EE) ∧ X₁.S.Over₀ Y U₀ ∧ X₁.S.IsEE Y U₀ EE ∧
    X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY

structure Tower (X₁ : GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) where

  X₂ : GSet

  act₂ : I → (X₂.ρ.P.A ⟶ X₂.ρ.P.A)
  isAct : IsAct X₂ act₂
  [alg : Algebra X₁.Ω₁ X₂.Ω₁]
  fd : FiniteDimensional X₁.Ω₁ X₂.Ω₁
  gal : IsGalois X₁.Ω₁ X₂.Ω₁

  d : ℕ
  lev : X₂.S.r * X₂.S.N = X₁.S.r * X₁.S.N * d

  om : X₁.S.R →+* X₂.S.R
  om_eq : ∀ a, (om a : X₂.Ω₁) = algebraMap X₁.Ω₁ X₂.Ω₁ a
  om_fin : om.Finite

  sR : (X₂.Ω₁ ≃ₐ[X₁.Ω₁] X₂.Ω₁) → (X₂.S.R →+* X₂.S.R)
  sR_eq : ∀ σ a, (sR σ a : X₂.Ω₁) = σ a

  p : X₂.M.Z ⟶ X₁.M.Z
  p_fin : IsFinite p
  p_pt : X₂.M.pt ≫ p = spMap (algebraMap X₁.Ω₁ X₂.Ω₁) ≫ X₁.M.pt

  φ : X₂.ρ.P.A.left ⟶ X₁.ρ.P.A.left
  cart : IsGrpPullback X₂.ρ.P.A X₁.ρ.P.A (spMap om) φ
  lb : LBIso X₂.ρ.P.L (X₁.ρ.P.L.pull φ)
  act_eq : ∀ a, (act₂ a).left ≫ φ = φ ≫ (act a).left

  lam : X₁.S.Gam →+ X₂.S.Gam
  lam_pt : ∀ a, (X₂.ρ.pt (lam a)).left ≫ φ = spMap om ≫ (X₁.ρ.pt a).left
  lam_range : ∀ a', ∃ a, lam a = d • a'

  gl : (X₂.Ω₁ ≃ₐ[X₁.Ω₁] X₂.Ω₁) → (X₂.S.Gam →+ X₂.S.Gam)
  gl_pt : ∀ σ a, (X₂.ρ.pt (gl σ a)).left ≫ φ = spMap (sR σ) ≫ (X₂.ρ.pt a).left ≫ φ
  gl_lam : ∀ σ a, gl σ (lam a) = lam a

attribute [instance] Tower.alg

def Tower.Ext {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z}
    {z₂ : 𝔗.X₂.M.Z} {V V' : Type} [CommRing V] [CommRing V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V')
    (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') : Prop :=
  IsLocalHom ev₂ ∧ ∀ x x₂, 𝔗.X₂.M.stalkHom z₂ x₂ = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom z₁ x) → ev₂ x₂ = io (ev x)

def Tower.self (X₁ : GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (h : IsAct X₁ act) : Tower X₁ act where
  X₂ := X₁
  act₂ := act
  isAct := h
  alg := Algebra.id _
  fd := inferInstance
  gal := inferInstance
  d := 1
  lev := by simp
  om := RingHom.id _
  om_eq _ := rfl
  om_fin := RingHom.Finite.id _
  sR _ := RingHom.id _
  sR_eq σ a := (σ.commutes a).symm
  p := 𝟙 _
  p_fin := inferInstance
  p_pt := by
    rw [show spMap (algebraMap X₁.Ω₁ X₁.Ω₁) = 𝟙 _ from Spec.map_id _]; simp
  φ := 𝟙 _
  cart := by rw [show spMap (RingHom.id X₁.S.R) = 𝟙 _ from Spec.map_id _]; exact Wit.grpPullback_id _
  lb := ⟨Wit.idPull _, Wit.idPull_isGen X₁.ρ.P.isLB⟩
  act_eq _ := by simp
  lam := AddMonoidHom.id _
  lam_pt a := by
    rw [show spMap (RingHom.id X₁.S.R) = 𝟙 _ from Spec.map_id _]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  lam_range a := ⟨a, by simp⟩
  gl _ := AddMonoidHom.id _
  gl_pt σ a := by
    rw [show spMap (RingHom.id X₁.S.R) = 𝟙 _ from Spec.map_id _]; exact (Category.id_comp _).symm
  gl_lam _ _ := rfl

theorem Tower.self_ext {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (h : IsAct X₁ act) {z₁ : X₁.M.Z} {V : Type} [CommRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (hev : IsLocalHom ev) :
    (Tower.self X₁ act h).Ext (z₁ := z₁) (z₂ := z₁) ev (RingHom.id V) ev :=
  ⟨hev, fun _ _ e => congrArg ev (X₁.M.stalkHom_injective z₁ e)⟩

theorem Tower.d_pos {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (T : Tower X₁ act) : 0 < T.d := by
  rcases Nat.eq_zero_or_pos T.d with h | h
  · have h1 := T.lev
    rw [h, mul_zero] at h1
    have := T.X₂.S.r_pos
    have := T.X₂.S.N_ge
    have : 0 < T.X₂.S.r * T.X₂.S.N := Nat.mul_pos (by omega) (by omega)
    omega
  · exact h

def Deep (X₁ : GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) : Prop :=
  ∀ N₀ : ℕ, ∃ 𝔗 : Tower X₁ act, N₀ ≤ 𝔗.X₂.S.r * 𝔗.X₂.S.N

section Siegel
variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

def ofSetup (X₁ : Setup F W i) : GSet where
  o₁ := X₁.o₁
  Ω₁ := X₁.Ω₁
  S := X₁.S
  ρ := X₁.ρ
  big := X₁.big
  M := X₁.M
  normal := X₁.normal
  projM := X₁.projM
  div := X₁.div

def ofUMem {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ) :
    GMem (I := {p : Matrix (Fin 8) (Fin 8) ℤ × Matrix (Fin 8) (Fin 8) ℤ // (W + W.transpose) * p.2 = p.1.transpose * (W + W.transpose)})
      (ofSetup X₁) z₁ (fun p => act p.1.1) V ev (Fin 8 → X) (mono W t δ) (fun p mu u => ∑ v, p.1.2 u v • mu v) where
  cn := 𝔪.cn
  loc := 𝔪.loc
  reg := 𝔪.reg
  yK := 𝔪.yK
  yK_eq := 𝔪.yK_eq
  D := 𝔪.D
  e₈ := 𝔪.e₈
  G := 𝔪.G
  semi := 𝔪.semi
  A := 𝔪.A
  U := 𝔪.U
  φ := 𝔪.φ
  cart := 𝔪.cart
  wl := 𝔪.wl
  wl_gen := 𝔪.wl_gen
  equiv := fun p => 𝔪.equiv p.1.1 p.1.2 p.2
  psi := 𝔪.psi

theorem isAct_ofSetup {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    (h : GlobalTheory.Poinc.Sep.IsAct X₁ act) (k : I → Matrix (Fin 8) (Fin 8) ℤ) : IsAct (ofSetup X₁) (fun a => act (k a)) :=
  fun a => h.isMonHom (k a)

theorem exists_gMem_ofSetup (X₁ : Setup F W i) : ∃ act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A),
    GlobalTheory.Poinc.Sep.IsAct X₁ act ∧ (∀ (I : Type) (k : I → Matrix (Fin 8) (Fin 8) ℤ), IsAct (ofSetup X₁) (fun a => act (k a))) ∧
    ∃ (z₁ : X₁.M.Z) (ev : X₁.M.Z.presheaf.stalk z₁ →+* X₁.Ω₁), Nonempty
      (GMem (I := {p : Matrix (Fin 8) (Fin 8) ℤ × Matrix (Fin 8) (Fin 8) ℤ //
          (W + W.transpose) * p.2 = p.1.transpose * (W + W.transpose)})
        (ofSetup X₁) z₁ (fun p => act p.1.1) X₁.Ω₁ ev (Fin 8 → PUnit) (mono W (m := 0) Fin.elim0 Fin.elim0)
        (fun p mu u => ∑ v, p.1.2 u v • mu v)) :=
  let ⟨act, h, z₁, ev, ⟨𝔪⟩⟩ := exists_uMem X₁
  ⟨act, h, fun _ k => isAct_ofSetup h k, z₁, ev, ⟨ofUMem 𝔪⟩⟩

def ofTower {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    (k : I → Matrix (Fin 8) (Fin 8) ℤ) (𝔗 : GlobalTheory.Poinc.Sep.Tower X₁ act) : Tower (ofSetup X₁) (fun a => act (k a)) where
  X₂ := ofSetup 𝔗.X₂
  act₂ a := 𝔗.act₂ (k a)
  isAct a := 𝔗.isAct.isMonHom (k a)
  alg := 𝔗.alg
  fd := 𝔗.fd
  gal := 𝔗.gal
  d := 𝔗.d
  lev := 𝔗.lev
  om := 𝔗.om
  om_eq := 𝔗.om_eq
  om_fin := 𝔗.om_fin
  sR := 𝔗.sR
  sR_eq := 𝔗.sR_eq
  p := 𝔗.p
  p_fin := 𝔗.p_fin
  p_pt := 𝔗.p_pt
  φ := 𝔗.φ
  cart := 𝔗.cart
  lb := 𝔗.lb
  act_eq a := 𝔗.act_eq (k a)
  lam := 𝔗.lam
  lam_pt := 𝔗.lam_pt
  lam_range := 𝔗.lam_range
  gl := 𝔗.gl
  gl_pt := 𝔗.gl_pt
  gl_lam := 𝔗.gl_lam

theorem ofTower_ext {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    (k : I → Matrix (Fin 8) (Fin 8) ℤ) (𝔗 : GlobalTheory.Poinc.Sep.Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z} {V V' : Type}
    [CommRing V] [CommRing V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V')
    (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') :
    (ofTower k 𝔗).Ext (z₁ := z₁) (z₂ := z₂) ev io ev₂ ↔ 𝔗.Ext ev io ev₂ := Iff.rfl

theorem deep_ofSetup {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    (k : I → Matrix (Fin 8) (Fin 8) ℤ) (h : ∀ N₀ : ℕ, ∃ 𝔗 : GlobalTheory.Poinc.Sep.Tower X₁ act, N₀ ≤ 𝔗.X₂.S.r * 𝔗.X₂.S.N) :
    Deep (ofSetup X₁) (fun a => act (k a)) := fun N₀ =>
  let ⟨𝔗, h𝔗⟩ := h N₀
  ⟨ofTower k 𝔗, h𝔗⟩

end Siegel

section Unitary
open GlobalTheory.UPoinc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def ULink (C : UCompact Xo c) (X₁ : GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c)
    (π : X₁.M.Z ⟶ C.Z) : Prop :=
  IsAct X₁ act ∧
  (∃ (G : Over (Sp (ratHull X₁.S.R))) (_ : GrpObj G) (α : G.left ⟶ X₁.ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
    IsGrpPullback G X₁.ρ.P.A (spMap (toRat X₁.S.R)) α ∧ IsGrpPullback G Xo.univ.t.G (u ≫ pullback.fst _ _) β ∧
      LBIso (X₁.ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      ∀ a, ∃ f : G ⟶ G, f.left ≫ α = α ≫ (act a).left ∧ f.left ≫ β = β ≫ (Xo.univ.t.act.act (H.bar a)).left) ∧
  (∀ w, (spMap (ratHull X₁.S.R).val.toRingHom ≫ u) w ∈ genericPoints (Xo.XF c)) ∧
  X₁.M.pt ≫ π = spMap (ratHull X₁.S.R).val.toRingHom ≫ u ≫ C.i

theorem ULink.uOver {C : UCompact Xo c} {X₁ : GSet} {act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c} {π : X₁.M.Z ⟶ C.Z} (h : ULink C X₁ act u π) :
    UOver Xo c X₁.ρ.P (toRat X₁.S.R) u :=
  let ⟨_, ⟨G, i, α, β, h₁, h₂, h₃, _⟩, _⟩ := h
  ⟨G, i, α, β, h₁, h₂, h₃⟩

variable {C : UCompact Xo c} {M : Scheme.{0}} {z₁ : M} (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b))
  (Φ : VPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] (M.presheaf.stalk z₁))

def HasTraitsOn (U : M.Opens) : Prop :=
  ∀ (T : UTrait Xo c) (ev : M.presheaf.stalk z₁ →+* T.V), IsLocalHom ev → jK T.V ≫ spMap ev ≫ ζ = T.y ≫ C.iF →
    Set.range (jK T.V ≫ spMap ev ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] T.P.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k ^ 2 = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.be (e a) (e b)

abbrev IsMemberP (N₁ : ℕ) {φ : InvFun (𝓞 E)} {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (Cm : GlobalTheory.UChart.MonoFam Xo c φ V) (ξ : Sp V ⟶ pullback C.z (spMap C.b)) (y : Φ.Y) (ρ : V →+* Φ.V y)
    (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) : Prop :=
  GlobalTheory.USep.IsMemberP ζ Φ N₁ Cm ξ y ρ e h

theorem hasTraitsOn_of_hasTraitsP (h : GlobalTheory.USep.HasTraitsP ζ Φ) (U : M.Opens) : HasTraitsOn ζ Φ U :=
  fun T ev h₁ h₂ _ => h T ev h₁ h₂

theorem hasTraitsOn_top : HasTraitsOn ζ Φ ⊤ ↔ GlobalTheory.USep.HasTraitsP ζ Φ :=
  ⟨fun h T ev h₁ h₂ => h T ev h₁ h₂ (Set.subset_univ _), fun h => hasTraitsOn_of_hasTraitsP ζ Φ h ⊤⟩

theorem hasTraitsOn_of_hasTraits {N₁ : ℕ} {Ψ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)}
    (h : GlobalTheory.USep.HasTraits ζ Ψ) (U : M.Opens) : HasTraitsOn ζ Ψ.pre U := fun T ev h₁ h₂ _ => h T ev h₁ h₂

end Unitary

end GlobalTheory.GSep
