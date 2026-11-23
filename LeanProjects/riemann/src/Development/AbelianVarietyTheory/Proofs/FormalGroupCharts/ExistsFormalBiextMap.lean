import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FBMap

variable {R k : Type} [CommRing R] [CommRing k] (f : R →+* k) {d : ℕ}

def NoConst {n : ℕ} (a : Pt R n d) : Prop := ∀ i, constantCoeff (a i) = 0

def mapPt {n : ℕ} (a : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map f (a i)

theorem hasSubst_of {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, NoConst (a j)) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2

theorem map_ev {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, NoConst (a j)) (g : PS R m d) :
    MvPowerSeries.map f (ev a g) = ev (fun j => mapPt f (a j)) (MvPowerSeries.map f g) := by
  unfold ev mapPt
  rw [MvPowerSeries.map_subst (hasSubst_of ha)]

theorem cc_ev {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, NoConst (a j)) {g : PS R m d}
    (hg : constantCoeff g = 0) : constantCoeff (ev a g) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of ha) (fun p => ha p.1 p.2) hg

theorem map_ev1 {n : ℕ} {a : Pt R n d} (ha : NoConst a) (g : PS R 1 d) :
    MvPowerSeries.map f (ev ![a] g) = ev ![mapPt f a] (MvPowerSeries.map f g) := by
  rw [map_ev f (fun j => by fin_cases j; exact ha)]
  congr 1
  funext j
  fin_cases j; rfl

theorem map_ev2 {n : ℕ} {a b : Pt R n d} (ha : NoConst a) (hb : NoConst b) (g : PS R 2 d) :
    MvPowerSeries.map f (ev ![a, b] g) = ev ![mapPt f a, mapPt f b] (MvPowerSeries.map f g) := by
  rw [map_ev f (fun j => by fin_cases j; exacts [ha, hb])]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem map_ev3 {n : ℕ} {a b c : Pt R n d} (ha : NoConst a) (hb : NoConst b) (hc : NoConst c)
    (g : PS R 3 d) :
    MvPowerSeries.map f (ev ![a, b, c] g) =
      ev ![mapPt f a, mapPt f b, mapPt f c] (MvPowerSeries.map f g) := by
  rw [map_ev f (fun j => by fin_cases j; exacts [ha, hb, hc])]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem nc_zero {n : ℕ} : NoConst (0 : Pt R n d) := fun _ => by simp

theorem nc_pt {n : ℕ} (j : Fin n) : NoConst (pt R d j) := fun _ => by simp [pt]

theorem nc_comp1 {n : ℕ} {φ : Pt R 1 d} {a : Pt R n d} (hφ : NoConst φ) (ha : NoConst a) :
    NoConst (comp1 φ a) := fun i =>
  cc_ev (fun j => by fin_cases j; exact ha) (hφ i)

theorem nc_addOf {n : ℕ} {F : Pt R 2 d} {a b : Pt R n d} (hF : NoConst F) (ha : NoConst a)
    (hb : NoConst b) : NoConst (addOf F a b) := fun i =>
  cc_ev (fun j => by fin_cases j; exacts [ha, hb]) (hF i)

theorem mapPt_zero {n : ℕ} : mapPt f (0 : Pt R n d) = 0 := by
  funext i; simp [mapPt]

theorem mapPt_pt {n : ℕ} (j : Fin n) : mapPt f (pt R d j) = pt k d j := by
  funext i; simp [mapPt, pt]

theorem mapPt_comp1 {n : ℕ} (φ : Pt R 1 d) {a : Pt R n d} (ha : NoConst a) :
    mapPt f (comp1 φ a) = comp1 (mapPt f φ) (mapPt f a) := by
  funext i; exact map_ev1 f ha (φ i)

theorem mapPt_addOf {n : ℕ} (F : Pt R 2 d) {a b : Pt R n d} (ha : NoConst a) (hb : NoConst b) :
    mapPt f (addOf F a b) = addOf (mapPt f F) (mapPt f a) (mapPt f b) := by
  funext i; exact map_ev2 f ha hb (F i)

theorem nc_law (G : FGLaw R d) : NoConst G.F := G.const

theorem nc_act {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) (a : O) :
    NoConst (A.act a) := A.const a

local macro "no_const" : tactic =>
  `(tactic| repeat' first
    | exact nc_zero
    | exact nc_pt _
    | exact nc_law _
    | exact nc_act _ _
    | apply nc_comp1
    | apply nc_addOf)

local macro "push_map" h:ident : tactic =>
  `(tactic| simp (disch := no_const) only [map_mul, map_one, map_ev1, map_ev2, map_ev3,
    mapPt_zero, mapPt_pt, mapPt_comp1, mapPt_addOf, FGLaw.add] at $h:ident)

def mapLaw (G : FGLaw R d) : FGLaw k d where
  F := mapPt f G.F
  const i := by simp [mapPt, G.const i]
  unit i := by
    have h := congrArg (MvPowerSeries.map f) (G.unit i)
    rw [map_X] at h
    push_map h
    exact h
  comm i := by
    have h := congrArg (MvPowerSeries.map f) (G.comm i)
    push_map h
    exact h
  assoc i := by
    have h0 : ev (n := 3) ![addOf G.F (pt R d 0) (pt R d 1), pt R d 2] (G.F i) =
        ev (n := 3) ![pt R d 0, addOf G.F (pt R d 1) (pt R d 2)] (G.F i) := G.assoc i
    have h := congrArg (MvPowerSeries.map f) h0
    push_map h
    exact h

def mapAct {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : OAct O (mapLaw f G) where
  act a := mapPt f (A.act a)
  const a i := by simp [mapPt, A.const a i]
  hom a := by
    have h := congrArg (mapPt f) (A.hom a)
    push_map h
    exact h
  add_act a b := by
    have h := congrArg (mapPt f) (A.add_act a b)
    push_map h
    exact h
  mul_act a b := by
    have h := congrArg (mapPt f) (A.mul_act a b)
    push_map h
    exact h
  one_act := by
    have h := congrArg (mapPt f) A.one_act
    push_map h
    exact h

def mapFB {O : Type} [CommRing O] [StarRing O] (B : FB R d O) : FB k d O where
  G := mapLaw f B.G
  A := mapAct f B.A
  ph1 := MvPowerSeries.map f B.ph1
  ph2 := MvPowerSeries.map f B.ph2
  sy := MvPowerSeries.map f B.sy
  ad a := MvPowerSeries.map f (B.ad a)
  cocycleLeft_zero_fst := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleLeft_zero_fst)
    push_map h
    exact h
  cocycleLeft_zero_snd := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleLeft_zero_snd)
    push_map h
    exact h
  cocycleLeft_zero_thd := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleLeft_zero_thd)
    push_map h
    exact h
  cocycleRight_zero_fst := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleRight_zero_fst)
    push_map h
    exact h
  cocycleRight_zero_snd := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleRight_zero_snd)
    push_map h
    exact h
  cocycleRight_zero_thd := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleRight_zero_thd)
    push_map h
    exact h
  symmetry_zero_fst := by
    have h := congrArg (MvPowerSeries.map f) (B.symmetry_zero_fst)
    push_map h
    exact h
  symmetry_zero_snd := by
    have h := congrArg (MvPowerSeries.map f) (B.symmetry_zero_snd)
    push_map h
    exact h
  adjoint_zero_fst a := by
    have h := congrArg (MvPowerSeries.map f) (B.adjoint_zero_fst a)
    push_map h
    exact h
  adjoint_zero_snd a := by
    have h := congrArg (MvPowerSeries.map f) (B.adjoint_zero_snd a)
    push_map h
    exact h
  cocycleLeft_assoc := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleLeft_assoc)
    push_map h
    exact h
  cocycleLeft_comm := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleLeft_comm)
    push_map h
    exact h
  cocycleRight_assoc := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleRight_assoc)
    push_map h
    exact h
  cocycleRight_comm := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleRight_comm)
    push_map h
    exact h
  interchange := by
    have h := congrArg (MvPowerSeries.map f) (B.interchange)
    push_map h
    exact h
  sy_inv := by
    have h := congrArg (MvPowerSeries.map f) (B.sy_inv)
    push_map h
    exact h
  sy_law := by
    have h := congrArg (MvPowerSeries.map f) (B.sy_law)
    push_map h
    exact h
  adjoint_compat_left a := by
    have h := congrArg (MvPowerSeries.map f) (B.adjoint_compat_left a)
    push_map h
    exact h
  adjoint_compat_right a := by
    have h := congrArg (MvPowerSeries.map f) (B.adjoint_compat_right a)
    push_map h
    exact h
  ad_one := by
    have h := congrArg (MvPowerSeries.map f) (B.ad_one)
    push_map h
    exact h
  ad_mul a b := by
    have h := congrArg (MvPowerSeries.map f) (B.ad_mul a b)
    push_map h
    exact h
  ad_add a b := by
    have h := congrArg (MvPowerSeries.map f) (B.ad_add a b)
    push_map h
    exact h
  ad_sy a := by
    have h := congrArg (MvPowerSeries.map f) (B.ad_sy a)
    push_map h
    exact h

end GlobalTheory.FBMap

namespace GlobalTheory

theorem exists_formalBiext_map :
    ∀ (R k : Type) [CommRing R] [CommRing k] (f : R →+* k) (d : ℕ) (O : Type) [CommRing O]
      [StarRing O] (B : FB R d O), ∃ B' : FB k d O,
      (∀ i, B'.G.F i = MvPowerSeries.map f (B.G.F i)) ∧
      (∀ a i, B'.A.act a i = MvPowerSeries.map f (B.A.act a i)) ∧
      B'.ph1 = MvPowerSeries.map f B.ph1 ∧ B'.ph2 = MvPowerSeries.map f B.ph2 ∧
      B'.sy = MvPowerSeries.map f B.sy ∧ ∀ a, B'.ad a = MvPowerSeries.map f (B.ad a) :=
  fun _ _ _ _ f _ _ _ _ B =>
    ⟨FBMap.mapFB f B, fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩

end GlobalTheory
