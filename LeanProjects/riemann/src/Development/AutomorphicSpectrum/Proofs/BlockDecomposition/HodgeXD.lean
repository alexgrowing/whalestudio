import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT

namespace GlobalTheory.CompanionTheory.KunGlue

universe w

variable {K : Type} [Field K]

structure Idx (c n : ℕ) where
  a : ℕ
  i : ℕ
  a' : ℕ
  j : ℕ
  ha : a + a' = c
  h : i + j = n
  deriving DecidableEq

def KunE {P Q T : ℕ → Cx.{w} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) : Prop :=
  ∀ c n : ℕ, ∃ e : (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ≃ₗ[K] (T c).H n,
    ∀ (t : Idx c n) (x : (P t.a).X t.i) (y : (Q t.a').X t.j) (hx : (P t.a).d t.i x = 0) (hy : (Q t.a').d t.j y = 0)
      (hz : (T c).d n ((pr t.ha).μ t.h x y) = 0),
      e (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t ((P t.a).cls x hx ⊗ₜ (Q t.a').cls y hy)) =
        (T c).cls ((pr t.ha).μ t.h x y) hz

def shD (ς : ℤˣ) (k : ℕ) (C : Cx.{w} K) (n : ℕ) (x : ∀ m : {m : ℕ // m + k = n}, C.X m.1) :
    ∀ m : {m : ℕ // m + k = n + 1}, C.X m.1
  | ⟨0, _⟩ => 0
  | ⟨m + 1, h⟩ => (ς : ℤ) • C.d m (x ⟨m, by omega⟩)

def Sh (ς : ℤˣ) (k : ℕ) (C : Cx.{w} K) : Cx.{w} K where
  X n := ∀ m : {m : ℕ // m + k = n}, C.X m.1
  d n :=
    { toFun := shD ς k C n
      map_add' := fun x y => by
        funext ⟨m, h⟩
        cases m with
        | zero => simp [shD]
        | succ m => simp [shD, smul_add]
      map_smul' := fun r x => by
        funext ⟨m, h⟩
        cases m with
        | zero => simp [shD]
        | succ m => simp [shD, smul_comm r] }
  dd n x := by
    funext ⟨m, h⟩
    cases m with
    | zero => rfl
    | succ m =>
      cases m with
      | zero => simp [shD]
      | succ m => simp [shD, C.dd]

def Dsum {I : Type w} [DecidableEq I] (E : I → Cx.{w} K) : Cx.{w} K where
  X n := ⨁ i, (E i).X n
  d n := DirectSum.lmap fun i => (E i).d n
  dd n x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x => simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (E i).dd]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]

variable {ι : Type} [DecidableEq ι]

def Sh.map (ς : ℤˣ) (k : ℕ) {C C' : Cx.{w} K} (f : Cx.Hom C C' (RingHom.id K)) :
    Cx.Hom (Sh ς k C) (Sh ς k C') (RingHom.id K) where
  f n := LinearMap.pi fun m => (f.f m.1).comp (LinearMap.proj m)
  comm n x := by
    funext ⟨m, h⟩
    cases m with
    | zero => exact (map_zero (f.f 0)).symm
    | succ m =>
      change (ς : ℤ) • C'.d m (f.f m (x ⟨m, _⟩)) = f.f (m + 1) ((ς : ℤ) • C.d m (x ⟨m, _⟩))
      rw [f.comm, map_zsmul]

def shSy (ς : ℤˣ) (k : ℕ) (A : Sy.{w} K ι) : Sy.{w} K ι where
  K S := Sh ς k (A.K S)
  res h := Sh.map ς k (A.res h)
  res_id S h n x := funext fun m => A.res_id S h _ _
  res_comp h h' n x := funext fun m => A.res_comp h h' _ _

def Dsum.map {I : Type w} [DecidableEq I] {E E' : I → Cx.{w} K} (f : ∀ i, Cx.Hom (E i) (E' i) (RingHom.id K)) :
    Cx.Hom (Dsum E) (Dsum E') (RingHom.id K) where
  f n := DirectSum.lmap fun i => (f i).f n
  comm n x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ (DirectSum.lmap _ _) = DirectSum.lmap _ (DirectSum.lmap _ _)
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (f i).comm]
    | add x y hx hy => simp only [map_add, hx, hy]

def sumSy {I : Type w} [DecidableEq I] (A : I → Sy.{w} K ι) : Sy.{w} K ι where
  K S := Dsum fun i => (A i).K S
  res h := Dsum.map fun i => (A i).res h
  res_id S h n x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ _ = _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (A i).res_id]
    | add x y hx hy => simp only [map_add, hx, hy]
  res_comp h h' n x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ (DirectSum.lmap _ _) = DirectSum.lmap _ _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (A i).res_comp]
    | add x y hx hy => simp only [map_add, hx, hy]

structure XD (K : Type) [Field K] where
  C₁ : Type 1
  [c₁ : Category.{0} C₁]
  C₂ : Type 1
  [c₂ : Category.{0} C₂]
  D : Type 1
  [cD : Category.{0} D]
  F₁ : ℕ → C₁ ⥤ ModuleCat.{0} K
  F₂ : ℕ → C₂ ⥤ ModuleCat.{0} K
  F₃ : ℕ → D ⥤ ModuleCat.{0} K
  L₁ : D ⥤ C₁
  L₂ : D ⥤ C₂
  τ₁ : ∀ (a : ℕ) (T : D), (F₁ a).obj (L₁.obj T) →ₗ[K] (F₃ a).obj T
  τ₂ : ∀ (a : ℕ) (T : D), (F₂ a).obj (L₂.obj T) →ₗ[K] (F₃ a).obj T
  n₁ : ∀ (a : ℕ) {T T' : D} (φ : T ⟶ T') (x : (F₁ a).obj (L₁.obj T)),
    τ₁ a T' (((F₁ a).map (L₁.map φ)).hom x) = ((F₃ a).map φ).hom (τ₁ a T x)
  n₂ : ∀ (a : ℕ) {T T' : D} (φ : T ⟶ T') (x : (F₂ a).obj (L₂.obj T)),
    τ₂ a T' (((F₂ a).map (L₂.map φ)).hom x) = ((F₃ a).map φ).hom (τ₂ a T x)
  μ : ∀ {a a' c : ℕ}, a + a' = c → CH.Pairing (F₃ a) (F₃ a') (F₃ c)

attribute [instance] XD.c₁ XD.c₂ XD.cD

namespace XD

variable (E : XD K)

def m₁ (a : ℕ) : CH.Mor (E.F₁ a) (E.F₃ a) (RingHom.id K) := ⟨E.L₁, E.τ₁ a, E.n₁ a⟩

def m₂ (a : ℕ) : CH.Mor (E.F₂ a) (E.F₃ a) (RingHom.id K) := ⟨E.L₂, E.τ₂ a, E.n₂ a⟩

def μU (U : ObjectProperty E.D) {a a' c : ℕ} (ha : a + a' = c) :
    CH.Pairing (U.ι ⋙ E.F₃ a) (U.ι ⋙ E.F₃ a') (U.ι ⋙ E.F₃ c) :=
  ⟨fun T => (E.μ ha).μ T.obj, fun φ => (E.μ ha).nat φ.hom⟩

def pr (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {a a' c : ℕ} (ha : a + a' = c) :
    CxPairing (CH.cx (U₁.ι ⋙ E.F₁ a)) (CH.cx (U₂.ι ⋙ E.F₂ a')) (CH.cx (U₃.ι ⋙ E.F₃ c)) where
  μ {p q n} h := ((E.μU U₃ ha).cupC h).compl₁₂ ((morU (E.m₁ a) h₁).pullC p) ((morU (E.m₂ a') h₂).pullC q)
  leib {p q n} h x y := by
    simp only [LinearMap.compl₁₂_apply]
    rw [CrystallineSemistableComparison.P.leibniz, (morU (E.m₁ a) h₁).d_pullC, (morU (E.m₂ a') h₂).d_pullC]

end XD

variable {X X' P : Scheme.{0}}

def hodgeXD (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (hw : p₂ ≫ q' = p₁ ≫ q) : XD K where
  C₁ := Thick (smFun X q)
  C₂ := Thick (smFun X' q')
  D := Thick (smFun P (p₁ ≫ q))
  F₁ a := G q a
  F₂ a := G q' a
  F₃ a := G (p₁ ≫ q) a
  L₁ := (smS p₁ rfl).G
  L₂ := (smS p₂ hw).G
  τ₁ a := (morG p₁ rfl a).τ
  τ₂ a := (morG p₂ hw a).τ
  n₁ a := (morG p₁ rfl a).nat
  n₂ a := (morG p₂ hw a).nat
  μ ha := (grOk (smFun P (p₁ ≫ q)) ha).pair

def swapPr {P Q T : ℕ → Cx.{w} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) {a a' c : ℕ}
    (ha : a + a' = c) : CxPairing (Q a) (P a') (T c) where
  μ {p q n} h := ((-1 : ℤ) ^ (p * q)) • ((pr (show a' + a = c by omega)).μ (show q + p = n by omega)).flip
  leib {p q n} h x y := by
    simp only [LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul]
    rw [(pr (show a' + a = c by omega)).leib (show q + p = n by omega) y x]
    have s1 : ((-1 : ℤ) ^ (p * q) * (-1) ^ q) = (-1) ^ ((p + 1) * q) := by
      rw [← pow_add]
      congr 1
      ring
    have s2 : ((-1 : ℤ) ^ p * (-1) ^ (p * (q + 1))) = (-1) ^ (p * q) := by
      have : p + p * (q + 1) = p * q + 2 * p := by ring
      rw [← pow_add, this, pow_add, pow_mul]
      simp
    simp only [smul_add, smul_smul, s1, s2]
    exact add_comm _ _

def XD.Kun (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) : Prop :=
  KunE (P := fun a => CH.cx (U₁.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) (T := fun a => CH.cx (U₃.ι ⋙ E.F₃ a))
    (fun {a a' c} ha => E.pr U₁ U₂ U₃ h₁ h₂ ha)

def MvE {ι : Type} {I : Type 1} [DecidableEq I] (k : I → ℕ) (A : I → Sy.{1} K ι) (T : Sy.{1} K ι)
    (g : ∀ (u : I) (S : Finset ι) {m n : ℕ}, m + k u = n → ((A u).K S).X m →ₗ[K] (T.K S).X n) (S : Finset ι) (n : ℕ) : Prop :=
  ∃ e : (⨁ v : {v : I × ℕ // v.2 + k v.1 = n}, ((A v.1.1).K S).H v.1.2) ≃ₗ[K] (T.K S).H n,
    ∀ (v : {v : I × ℕ // v.2 + k v.1 = n}) (x : ((A v.1.1).K S).X v.1.2) (hx : ((A v.1.1).K S).d v.1.2 x = 0)
      (hz : (T.K S).d n (g v.1.1 S v.2 x) = 0),
      e (DirectSum.lof K _ (fun v : {v : I × ℕ // v.2 + k v.1 = n} => ((A v.1.1).K S).H v.1.2) v (((A v.1.1).K S).cls x hx)) =
        (T.K S).cls (g v.1.1 S v.2 x) hz

end GlobalTheory.CompanionTheory.KunGlue
