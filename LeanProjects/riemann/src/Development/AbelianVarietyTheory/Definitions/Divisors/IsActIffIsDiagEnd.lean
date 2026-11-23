import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagEndIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

namespace Sep
open GlobalTheory.ZH

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

def IsAct (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) : Prop :=
  IsDiagEnd F W X₁.ρ.P X₁.u act

theorem isAct_iff_isDiagEnd {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} :
    IsAct X₁ act ↔ IsDiagEnd F W X₁.ρ.P X₁.u act := Iff.rfl

theorem isAct_iff {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} : IsAct X₁ act ↔
    ∃ c : SiegPre g n (zetaAway n) (X₁.u ≫ F.s), SiegPB c F.univ X₁.u ∧ ∃ pr : Fin 8 → (X₁.ρ.P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) ∧
      (∀ (T' : Over (Sp X₁.S.R)) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ X₁.ρ.P.A, ∀ a, x ≫ pr a = y a) ∧
      LBIso X₁.ρ.P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
      ∀ a u, act a ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod := by
  unfold IsAct IsDiagEnd
  simp only [List.ofFn_eq_map]

theorem IsAct.isMonHom {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (h : IsAct X₁ act)
    (E : Matrix (Fin 8) (Fin 8) ℤ) : IsMonHom (act E) := by
  obtain ⟨c, -, pr, hpr, huniq, -, hε⟩ := h
  have key : ∀ (T' : Over (Sp X₁.S.R)) (x : T' ⟶ X₁.ρ.P.A) (a : Fin 8),
      (x ≫ act E) ≫ pr a = ((List.finRange 8).map fun b => (x ≫ pr b) ^ E a b).prod := by
    intro T' x a
    rw [Category.assoc, hε]
    change diagPrecomp (M := c.A) x _ = _
    rw [map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun b _ => map_zpow (diagPrecomp (M := c.A) x) (pr b) (E a b)
  refine isMonHom_of_mul _ fun T' x z => (huniq T' fun a => (x ≫ act E * z ≫ act E) ≫ pr a).unique (fun a => ?_) fun _ => rfl
  have hm : ∀ (b : Fin 8) (x z : T' ⟶ X₁.ρ.P.A), (x * z) ≫ pr b = (x ≫ pr b) * (z ≫ pr b) := fun b x z =>
    map_mul (IsMonHom.monoidHom (pr b) T') x z
  rw [key, hm, key, key, ← List.prod_map_mul]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  rw [hm, mul_zpow]

theorem nonempty_isAct (X₁ : Setup F W i) : Nonempty {act // IsAct X₁ act} :=
  let ⟨ε, h, _⟩ := exists_diagEnd_isMonHom g n F W _ X₁.ρ.P X₁.u X₁.sharp
  ⟨⟨ε, h⟩⟩

structure UMem (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A))
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
    (X : Type) [AddCommGroup X] {m : ℕ} (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) where
  cn : IsCN V
  loc : IsLocalHom ev
  reg : RegAt X₁ z₁ ev

  yK : X₁.S.R →+* FractionRing V
  yK_eq : ∀ a : X₁.S.R, yK a = X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a

  D : DegData V (maximalIdeal V)

  e₈ : (Fin 8 → X) ≃+ D.toPre.X

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
  equiv : ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) →
    ∃ E : EndU U.toUnifPre, E.aA.left ≫ φ = φ ≫ (act a).left ∧ ∀ mu, E.h (e₈ mu) = e₈ fun u => ∑ v, a' u v • mu v
  psi : ∀ mu, ∃ u : Vˣ, Formalism.L2.Pj.PsiCoord D.toPre (e₈ mu) (u * mono W t δ mu)

attribute [instance] UMem.grp UMem.comm

namespace UMem
variable {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ)

def YY (a : X₁.S.Gam) (mu : Fin 8 → X) : Prop :=
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

def Terms (x₀ : X₁.S.Gam) {C : Type} (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V) : Prop :=
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

end UMem

def IsGeo (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam)
    (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam) : Prop :=
  X₁.M.Div X₁.S.th x₀ z₁ ∧ Set.range lab = X₁.S.HH X₁.M z₁ ∧
    ∀ y, ∃ 𝔪 : UMem X₁ z₁ act (Φ.V y) (Φ.ev y) (Φ.X y) (Φ.t y) (Φ.δ y), 𝔪.Terms x₀ lab (Φ.term y)

section
variable {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ)

include 𝔪 in

theorem UMem.mono_ne_zero (mu : Fin 8 → X) : mono W t δ mu ≠ 0 :=
  let ⟨_, h⟩ := 𝔪.psi mu
  right_ne_zero_of_mul (PsiCoordLocal.ne_zero_of_coord h)

include 𝔪 in

theorem UMem.mono_mem {mu : Fin 8 → X} (h : mu ≠ 0) : mono W t δ mu ∈ maximalIdeal V := by
  haveI := 𝔪.cn.2.2.2
  obtain ⟨u, hu⟩ := 𝔪.psi mu
  obtain ⟨r, hr, -, hm, -⟩ := (PsiCoordLocal.main V 𝔪.D 𝔪.cn.2.1 (𝔪.e₈ mu)).1
  obtain ⟨v, hv⟩ := PsiCoordLocal.exists_unit_of_coord hr hu
  have : (u : V) * mono W t δ mu ∈ maximalIdeal V := hv ▸ Ideal.mul_mem_left _ _ (hm (𝔪.e₈.map_ne_zero_iff.2 h))
  exact (Ideal.unit_mul_mem_iff_mem _ u.isUnit).1 this

end

example {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} :
    IsEmpty (UMem X₁ z₁ act V ev ℤ (m := 0) Fin.elim0 Fin.elim0) :=
  ⟨fun 𝔪 => (maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 (by
    simpa [mono] using 𝔪.mono_mem (mu := 1) one_ne_zero))⟩

theorem exists_unif_good {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V) (P : PolAV (Sp V)) :
    letI := P.isAb.comm
    ∃ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A P.A)
      (ψ : A.A.left ⟶ P.A.left), Subsingleton D.toPre.X ∧ IsGrpPullback A.A P.A (jK V) ψ ∧ LBIso A.L (P.L.pull ψ) ∧
      ∀ a : P.A ⟶ P.A, IsMonHom a → ∃ E : EndU U.toUnifPre, E.aA.left ≫ ψ = ψ ≫ a.left := by
  have hN := hV.1
  have hC := hV.2.2.1
  obtain ⟨D, rfl, hX⟩ := SelfUnif.exists_degData firstFiveLaws.1.cube (maximalIdeal V) P
  let A := StrictPull.polPull D.toPre.P (jK V)
  have r : LBIso A.L (D.toPre.P.L.pull (pullback.fst D.toPre.P.A.hom (jK V))) := PolBaseChange.lbIso_refl A.isLB
  have hm : IsMonHom (Iso.refl A.A).hom := inferInstanceAs (IsMonHom (𝟙 A.A))
  have hw : LBIso (A.L.pull (Iso.refl A.A).hom.left) (D.toPre.P.L.pull (pullback.fst D.toPre.P.A.hom (jK V))) := by
    have := lbIso_pull_comp r (𝟙 A.A.left)
    exact Eq.mp (congrArg (fun f => LBIso _ (D.toPre.P.L.pull f)) (Category.id_comp _)) this
  let U : Unif (maximalIdeal V) D A D.toPre.P.A := ⟨SelfUnif.selfPre D A (Iso.refl _) hm hw, fun k _ =>
    SelfUnif.expBij D A (Iso.refl _) hm hw firstFiveLaws.1.globalFns (IsAdicComplete.le_jacobson_bot _) k⟩
  refine ⟨D, A, U, _, hX, isGrpPullback_pullback _ _, r, fun a ha => ?_⟩
  obtain ⟨E, -, hE⟩ := exists_degenerationEndomorphism_of_admissibleBase V _ ⟨hN, inferInstance, hV.2.1, hC⟩ D A _
    (isSemiAbelian_of_isAbelianScheme _ D.toPre.P.isAb) U a ((Over.pullback (jK V)).map a) ha
    (inferInstanceAs (IsMonHom ((Over.pullback (jK V)).map a))) ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact ⟨E, hE ▸ pullback.lift_fst _ _ _⟩

theorem UMem.nonempty_of_regular {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    (hact : IsAct X₁ act) (hz : X₁.S.R ≤ X₁.M.O z₁) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V)
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (hev : IsLocalHom ev) (X : Type) [AddCommGroup X] [Subsingleton X] {m : ℕ}
    (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) : Nonempty (UMem X₁ z₁ act V ev X t δ) := by
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  let yV : X₁.S.R →+* V := (RatModel.valLoc (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) z₁ (sp _)).comp
    (Subalgebra.inclusion hz).toRingHom
  let P := StrictPull.polPull X₁.ρ.P (spMap yV)
  letI := P.isAb.comm
  obtain ⟨D, A, U, ψ, hX, hψ, hL, hE⟩ := exists_unif_good hV P
  have r : LBIso P.L (X₁.ρ.P.L.pull (pullback.fst X₁.ρ.P.A.hom (spMap yV))) := PolBaseChange.lbIso_refl P.isLB
  obtain ⟨wl, hwl⟩ := LBIso.trans A.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hL (lbIso_pull_comp r ψ)
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
    equiv := fun a a' _ => ?_
    psi := fun mu => ⟨(hu rfl).unit, ?_⟩ }⟩
  · have := hact.isMonHom a
    obtain ⟨E, h⟩ := hE ((Over.pullback (spMap yV)).map (act a))
      (inferInstanceAs (IsMonHom ((Over.pullback (spMap yV)).map (act a))))
    refine ⟨E, ?_, fun _ => Subsingleton.elim _ _⟩
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans ((Category.assoc _ _ _).trans
      ((congrArg (ψ ≫ ·) (pullback.lift_fst _ _ _)).trans (Category.assoc _ _ _).symm)))
  · have : mono W t δ mu = 1 := by
      rw [Subsingleton.elim mu 0]
      simp [mono, qW]
    rw [this, _root_.mul_one]
    exact hr₀

theorem exists_uMem (X₁ : Setup F W i) : ∃ act, IsAct X₁ act ∧ ∃ (z₁ : X₁.M.Z) (ev : X₁.M.Z.presheaf.stalk z₁ →+* X₁.Ω₁),
    Nonempty (UMem X₁ z₁ act X₁.Ω₁ ev PUnit (m := 0) Fin.elim0 Fin.elim0) := by
  obtain ⟨act, h⟩ := nonempty_isAct X₁
  refine ⟨act, h, _, (Scheme.stalkClosedPointTo (R := CommRingCat.of X₁.Ω₁) X₁.M.pt).hom,
    UMem.nonempty_of_regular h ?_ ⟨inferInstance, inferInstance, ?_, X₁.ar.char⟩ _ inferInstance _ _ _⟩
  · exact le_top.trans ((congrArg X₁.M.O (X₁.M.pt_apply _)).trans X₁.M.O_genericPoint).ge
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance

end Sep

end GlobalTheory.Poinc
