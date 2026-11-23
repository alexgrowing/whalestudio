import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier

namespace GlobalTheory.ShFam

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure EigFrame (Z : Model Xo c β) {R : Type} [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) : Type where
  v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)
  tan : ∀ τ i, IsTanAtG Z.t x (v τ i)
  eig : ∀ τ i (a : 𝓞 E), v τ i ≫ (Z.t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ v τ i
  basis : ∀ τ w, IsTanAtG Z.t x w → (∀ a : 𝓞 E, w ≫ (Z.t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ w) →
    ∃! a : Fin (Dw.mult τ) → R, IsCombAtG Z.t x (v τ) a w

def EigFrame.Tri {Z : Model Xo c β} {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ) : Prop :=
  x' = spMap ψ ≫ x ∧ φ' = ψ.comp φ ∧ ∀ τ i, ∃ cf : Fin (Dw.mult τ) → R', cf i = t τ i ∧ (∀ k, i < k → cf k = 0) ∧
    IsCombAtG Z.t x' (fun k => spMap (dualMap ψ) ≫ f.v τ k) cf (g.v τ i)

attribute [local instance] Over.cartesianMonoidalCategory in
open MonObj in

theorem isCombAtG_single {X0 : Scheme.{0}} (t : SAB H X0) {R : Type} [CommRing R] (x : Sp R ⟶ X0) {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j)) (j : Fin m) :
    IsCombAtG t x v (Pi.single j 1) (v j) := by
  have hb : ∀ a : R, spMap (epsMul a) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) :=
    fun a => by
      rw [← Spec.map_comp]
      congr 1
      ext r <;> simp [epsMul]
  have h1 : spMap (epsMul (1 : R)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [epsMul]
  have h0 : spMap (epsMul (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have e : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
      RingHom.ext fun z => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Spec.map_comp, e]
    rfl
  let u : Fin m → (tEpsG x ⟶ t.G) := fun i =>
    Over.homMk (spMap (epsMul ((Pi.single j 1 : Fin m → R) i)) ≫ v i) (by
      rw [Category.assoc, (hv i).1, ← Category.assoc, hb]; rfl)
  have hu : ∀ i, i ≠ j → u i = 1 := fun i hi => by
    let p : tEpsG x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
    rw [← MonObj.comp_one p]
    ext
    show spMap (epsMul ((Pi.single j 1 : Fin m → R) i)) ≫ v i = _
    rw [Pi.single_eq_of_ne hi, h0, Category.assoc, (hv i).2]
    rfl
  refine ⟨u, fun i => rfl, ?_⟩
  have : (List.ofFn u).prod = u j := by
    rw [List.ofFn_eq_map, List.prod_map_eq_pow_single j u fun i hi _ => hu i hi,
      List.count_eq_one_of_mem (List.nodup_finRange m) (List.mem_finRange j), pow_one]
  rw [this]
  show spMap (epsMul ((Pi.single j 1 : Fin m → R) j)) ≫ v j = _
  rw [Pi.single_eq_same, h1, Category.id_comp]

theorem EigFrame.tri_refl {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f : EigFrame Z φ x) : f.Tri (RingHom.id R) f 1 := by
  have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  refine ⟨by rw [h2, Category.id_comp], rfl, fun τ i => ⟨Pi.single i 1, by simp,
    fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
  simp only [h1, Category.id_comp]
  exact isCombAtG_single Z.t x (f.tan τ) i

variable {F : Type} [Field F]

def constF (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) : c.F →+* Y.Fn := (algebraMap F Y.Fn).comp e.symm.toRingHom

def stalkPt (Y : GlobalTheory.ProjVar.Var F) (y : Y.X) : Sp (Y.X.presheaf.stalk y) ⟶ Y.X := Y.X.fromSpecStalk y

def genericPt (Y : GlobalTheory.ProjVar.Var F) : Sp Y.Fn ⟶ Y.X := Y.X.fromSpecStalk (genericPoint Y.X)

structure FlagCpt (Z : Model Xo c β) (e : F ≃+* c.F) : Type where
  Y : GlobalTheory.ProjVar.Var F
  π : Y.X ⟶ gen Z
  π_str : π ≫ genStr Z ≫ spMap e.toRingHom = Y.str

  y0 : letI := (constF e Y).toAlgebra; FrPt Xo c Y.Fn

  f0 : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)
  y0_x : (letI := (constF e Y).toAlgebra; GlobalTheory.AllWt.ptF y0) ≫ Z.jQ = genericPt Y ≫ π

  flagComponentFramedPoint_frame : letI := (constF e Y).toAlgebra; ∀ τ i, ∃ w : Sp (DualNumber Y.Fn) ⟶ Z.oF.t.G.left,
    w ≫ Z.oF.t.G.hom = spMap (algebraMap Y.Fn (DualNumber Y.Fn)) ≫ GlobalTheory.AllWt.ptF y0 ∧
    w ≫ Z.m0.toSABMap.φ = y0.u τ i ∧ w ≫ Z.m.φ = f0.v τ i

  gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv

  gr_spec : ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z))
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ),
    f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f0 t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i)

  bd : Y.Dv
  bd_eff : Y.Eff bd
  bd_supp : ∀ y : Y.X, y ∈ Y.supp bd ↔ π y ∈ genBd Z
  bd_red : ∀ (y : Y.X) (g : Y.Fnˣ), bd.IsEqn y g → ∀ (f : Y.Fn) (n : ℕ), RegAt y f → RegAt y (f ^ n / g) → RegAt y (f / g)

namespace FlagCpt

variable {Z : Model Xo c β} {e : F ≃+* c.F} (C : FlagCpt Z e)

def Carries {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} (p : Sp k ⟶ C.Y.X) (g : EigFrame Z φ x) : Prop :=
  ∃ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y)
    (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
    p = spMap ψ ≫ stalkPt C.Y y ∧ f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t ∧ f.Tri ψ g t'

def Ybd : C.Y.Cl := C.Y.supp C.bd

def LEx : (Ix Dw → ℤ) →+ C.Y.Dv where
  toFun ex := -∑ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ex (some x) • C.gr x.1 x.2
  map_zero' := by simp
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib, add_comm]

def Lw (la : GlobalTheory.AllWt.Weight Dw) : C.Y.Dv := C.LEx (GlobalTheory.AllWt.exOf Dw la 0)

theorem Lw_zero : C.Lw 0 = 0 := by
  have h : GlobalTheory.AllWt.exOf Dw 0 0 = 0 := by
    rw [GlobalTheory.AllWt.exOf, GlobalTheory.AllWt.wtOf_zero]; funext i; cases i <;> rfl
  rw [Lw, h, map_zero]

theorem Lw_add (la la' : GlobalTheory.AllWt.Weight Dw) : C.Lw (la + la') = C.Lw la + C.Lw la' := by
  have h := GlobalTheory.AllWt.exOf_add la la' 0 0
  rw [add_zero] at h
  rw [Lw, h, map_add, Lw, Lw]

theorem LEx_congr {a b : Ix Dw → ℤ} (h : ∀ x, a (some x) = b (some x)) : C.LEx a = C.LEx b := by
  simp only [LEx, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h]

open Classical in

theorem LEx_single (x : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : C.LEx (Pi.single (some x) 1) = -C.gr x.1 x.2 := by
  simp only [LEx, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single x (fun b _ hb => by rw [Pi.single_eq_of_ne (by simpa using hb), zero_smul]) (by simp),
    Pi.single_eq_same, one_smul]

def val (f : Rul Xo c) : C.Y.Fn := letI := (constF e C.Y).toAlgebra; evR Xo c f C.y0

end FlagCpt

structure FlagTor (Z : Model Xo c β) (e : F ≃+* c.F) {σ : c.F →+* ℂ} {N : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ N) : Type where
  C : U.Comp → FlagCpt Z e
  dim_eq : ∀ k, (C k).Y.dim = Module.finrank ℚ E / 2 * (N * (N - 1) / 2)
  lifts : ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (x : Sp k ⟶ gen Z), x ≫ genStr Z = spMap φ →
    ∀ g : EigFrame Z φ (x ≫ genι Z), ∃! p : Σ i : U.Comp, (Sp k ⟶ (C i).Y.X), p.2 ≫ (C p.1).π = x ∧ (C p.1).Carries p.2 g
  label : ∀ (i : U.Comp) (x : (U.X i).dom) (s : Sp (CAt σ)),
    (GlobalTheory.AllWt.ptF (U.un i x) ≫ Z.jQ) s ∈ Set.range (C i).π

def keyEx (Dw : Datum H) : Ix Dw → ℤ
  | none => -2
  | some _ => 1

structure KeySec (Xo : Moduli Dw l) (c : Coeff l) : Type where
  ρ : (Rul Xo c)ˣ
  mem : (ρ : Rul Xo c) ∈ GlobalTheory.AllWt.secZ Xo c (keyEx Dw)

def FlagCpt.cmp {Z : Model Xo c β} {e : F ≃+* c.F} (C : FlagCpt Z e) (κ : KeySec Xo c) {c₀ : Coeff l} (hle : c₀.F ≤ c.F)
    (n : ℕ) (f : Rul Xo c₀) : C.Y.Fn :=
  C.val (GlobalTheory.FieldBC.rulBC hle f * (κ.ρ : Rul Xo c) ^ (n / 2))

def exKey (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Ix Dw → ℤ :=
  fun i => (ex Dw a n i : ℤ) + ((n / 2 : ℕ) : ℤ) * keyEx Dw i

theorem exKey_two_mul (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ) :
    exKey Dw a (2 * m) = GlobalTheory.AllWt.exOf Dw (GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) m) 0 := by
  have h : GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) (m : ℤ) =
      GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ) + (m : ℤ)) 0 := by
    funext τ j
    simp only [GlobalTheory.AllWt.weightOf]
    split_ifs <;> ring
  rw [h, GlobalTheory.AllWt.exOf_weightOf]
  funext i
  cases i <;> simp [exKey, keyEx, ex, exZ]
  ring

theorem FlagCpt.LEx_exKey {Z : Model Xo c β} {e : F ≃+* c.F} (C : FlagCpt Z e) (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ) :
    C.LEx (exKey Dw a (2 * m)) = C.Lw (GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) m) := by
  rw [exKey_two_mul, FlagCpt.Lw]

theorem KeySec.pow_mem (κ : KeySec Xo c) (m : ℕ) :
    (κ.ρ : Rul Xo c) ^ m ∈ GlobalTheory.AllWt.secZ Xo c (fun i => (m : ℤ) * keyEx Dw i) := by
  induction m with
  | zero =>
    have h : (fun i => ((0 : ℕ) : ℤ) * keyEx Dw i) = 0 := by funext i; simp
    rw [pow_zero, h]; exact GlobalTheory.AllWt.one_mem_secZ
  | succ m ih =>
    have h : (fun i => ((m + 1 : ℕ) : ℤ) * keyEx Dw i) = (fun i => (m : ℤ) * keyEx Dw i) + keyEx Dw := by
      funext i; simp only [Pi.add_apply]; push_cast; ring
    rw [pow_succ, h]; exact GlobalTheory.AllWt.mul_mem_secZ ih κ.mem

theorem KeySec.mul_pow_mem (κ : KeySec Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    f * (κ.ρ : Rul Xo c) ^ (n / 2) ∈ GlobalTheory.AllWt.secZ Xo c (exKey Dw a n) := by
  rw [← GlobalTheory.AllWt.secZ_nat] at hf
  exact GlobalTheory.AllWt.mul_mem_secZ hf (κ.pow_mem (n / 2))

end Free

abbrev FinalTheorems.Flag {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) : Type :=
  FlagTor s.T.Z κ.e (s.U κ.σ₀)

end GlobalTheory.ShFam
