import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AddCharMemValuationSubring

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

variable {R : Type} [CommRing R] {d : ℕ}

def Z {n : ℕ} (a : Pt R n d) : Prop := ∀ i, constantCoeff (a i) = 0

def ZZ {m n : ℕ} (b : Fin m → Pt R n d) : Prop := ∀ j i, constantCoeff (b j i) = 0

def evP {m n : ℕ} (b : Fin m → Pt R n d) (a : Pt R m d) : Pt R n d := fun i => ev b (a i)

def evV {l m n : ℕ} (b : Fin m → Pt R n d) (a : Fin l → Pt R m d) : Fin l → Pt R n d := fun j => evP b (a j)

theorem ZZ_nil {n : ℕ} : ZZ (![] : Fin 0 → Pt R n d) := fun j => j.elim0

theorem ZZ_cons {m n : ℕ} {p : Pt R n d} {u : Fin m → Pt R n d} (hp : Z p) (hu : ZZ u) :
    ZZ (Matrix.vecCons p u) := fun j => Fin.cases hp (fun j => hu j) j

theorem Z_pt {n : ℕ} (j : Fin n) : Z (pt R d j) := fun i => by simp [pt]

theorem Z_zero {n : ℕ} : Z (0 : Pt R n d) := fun i => by simp

theorem cc_ev {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) {f : PS R m d}
    (hf : constantCoeff f = 0) : constantCoeff (ev b f) = 0 :=
  constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin d => b p.1 p.2) (hasSubst_ev b hb)
    (fun p => hb p.1 p.2) hf

theorem Z_comp1 {n : ℕ} {φ : Pt R 1 d} {a : Pt R n d} (hφ : Z φ) (ha : Z a) : Z (comp1 φ a) :=
  fun i => cc_ev (ZZ_cons ha ZZ_nil) (hφ i)

theorem Z_add {n : ℕ} (G : FGLaw R d) {a b : Pt R n d} (ha : Z a) (hb : Z b) : Z (addOf G.F a b) :=
  fun i => cc_ev (ZZ_cons ha (ZZ_cons hb ZZ_nil)) (G.const i)

theorem Z_act {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) (a : O) : Z (A.act a) := A.const a

macro "ztac" : tactic => `(tactic| repeat' (first
  | assumption | exact ZZ_nil | exact Z_pt _ | exact Z_zero | exact Z_act _ _
  | apply ZZ_cons | apply Z_comp1 | apply Z_add))

theorem ev_ev {l m n : ℕ} {b : Fin m → Pt R n d} {a : Fin l → Pt R m d} (hb : ZZ b) (ha : ZZ a)
    (f : PS R l d) : ev b (ev a f) = ev (evV b a) f :=
  subst_comp_subst_apply (hasSubst_ev a ha) (hasSubst_ev b hb) f

theorem evV_cons {l m n : ℕ} (b : Fin m → Pt R n d) (p : Pt R m d) (u : Fin l → Pt R m d) :
    evV b (Matrix.vecCons p u) = Matrix.vecCons (evP b p) (evV b u) :=
  funext fun j => Fin.cases rfl (fun _ => rfl) j

theorem evV_nil {m n : ℕ} (b : Fin m → Pt R n d) : evV b (![] : Fin 0 → Pt R m d) = ![] :=
  funext fun j => j.elim0

theorem evalPoints_coordinatePoint {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (j : Fin m) : evP b (pt R d j) = b j :=
  funext fun i => ev_X b hb j i

theorem ev_mul' {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (f g : PS R m d) :
    ev b (f * g) = ev b f * ev b g := ev_mul b hb f g

theorem ev_zero' {m n : ℕ} (b : Fin m → Pt R n d) : ev b (0 : PS R m d) = 0 := by
  simpa using ev_C b (0 : R)

theorem evalPoints_zero {m n : ℕ} (b : Fin m → Pt R n d) : evP b (0 : Pt R m d) = 0 :=
  funext fun _ => ev_zero' b

theorem evalPoints_comp {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (φ : Pt R 1 d) {a : Pt R m d} (ha : Z a) :
    evP b (comp1 φ a) = comp1 φ (evP b a) := by
  funext i
  change ev b (ev ![a] (φ i)) = ev ![evP b a] (φ i)
  rw [ev_ev hb (ZZ_cons ha ZZ_nil), evV_cons, evV_nil]

theorem evalPoints_add {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (F : Fin d → PS R 2 d) {x y : Pt R m d}
    (hx : Z x) (hy : Z y) : evP b (addOf F x y) = addOf F (evP b x) (evP b y) := by
  funext i
  change ev b (ev ![x, y] (F i)) = ev ![evP b x, evP b y] (F i)
  rw [ev_ev hb (ZZ_cons hx (ZZ_cons hy ZZ_nil)), evV_cons, evV_cons, evV_nil]

macro "evs" " at " h:ident : tactic => `(tactic| simp (disch := ztac) only [FGLaw.add, ev_mul', ev_one, ev_ev, evV_cons,
  evV_nil, evalPoints_coordinatePoint, evalPoints_zero, evalPoints_comp, evalPoints_add, Matrix.cons_val] at $h:ident)

theorem comp1_eq_evalPoint {n : ℕ} (φ : Pt R 1 d) (x : Pt R n d) : comp1 φ x = evP ![x] φ := rfl

theorem germComp1_germComp1_eq_substitute {n : ℕ} (φ : Pt R 1 d) {ψ : Pt R 1 d} (hψ : Z ψ) {x : Pt R n d} (hx : Z x) :
    comp1 (comp1 φ ψ) x = comp1 φ (comp1 ψ x) :=
  evalPoints_comp (ZZ_cons hx ZZ_nil) φ hψ

theorem eval_identity_two (f : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] f = f :=
  ev_pt_self _ (fun j => by fin_cases j <;> rfl) f

section Laws

variable {O : Type} [CommRing O] [StarRing O] (B : FB R d O) {n : ℕ}

theorem act_zero_at (x : Pt R n d) : comp1 (B.A.act ((0 : ℕ) : O)) x = 0 := by
  rw [Nat.cast_zero, GlobalTheory.FourierChainCompare.act_zero]
  exact evalPoints_zero _

theorem act_succ_at (k : ℕ) {x : Pt R n d} (hx : Z x) :
    comp1 (B.A.act ((k + 1 : ℕ) : O)) x = addOf B.G.F (comp1 (B.A.act (k : O)) x) x := by
  rw [Nat.cast_succ, B.A.add_act, B.A.one_act, comp1_eq_evalPoint, comp1_eq_evalPoint,
    evalPoints_add (ZZ_cons hx ZZ_nil) _ (Z_act _ _) (Z_pt _), evalPoints_coordinatePoint (ZZ_cons hx ZZ_nil)]
  rfl

theorem first_power_succ_at (k : ℕ) {x z : Pt R n d} (hx : Z x) (hz : Z z) :
    ev ![x, z] (pow1 B (k + 1)) = ev ![x, z] (pow1 B k) * ev ![comp1 (B.A.act (k : O)) x, x, z] B.ph1 := by
  have h : ev ![x, z] (pow1 B (k + 1)) = ev ![x, z] (pow1 B k *
      ev (n := 2) ![comp1 (B.A.act (k : O)) (pt R d 0), pt R d 0, pt R d 1] B.ph1) := by
    rw [pow1, Finset.prod_range_succ, pow1]
  evs at h
  exact h

theorem second_power_succ_at (k : ℕ) {x z : Pt R n d} (hx : Z x) (hz : Z z) :
    ev ![x, z] (pow2 B (k + 1)) = ev ![x, z] (pow2 B k) * ev ![x, comp1 (B.A.act (k : O)) z, z] B.ph2 := by
  have h : ev ![x, z] (pow2 B (k + 1)) = ev ![x, z] (pow2 B k *
      ev (n := 2) ![pt R d 0, comp1 (B.A.act (k : O)) (pt R d 1), pt R d 1] B.ph2) := by
    rw [pow2, Finset.prod_range_succ, pow2]
  evs at h
  exact h

theorem first_power_zero : pow1 B 0 = 1 := by simp [pow1]

theorem second_power_zero : pow2 B 0 = 1 := by simp [pow2]

theorem sy_law_at {x z w : Pt R n d} (hx : Z x) (hz : Z z) (hw : Z w) :
    ev ![x, z, w] B.ph2 * ev ![x, z] B.sy * ev ![x, w] B.sy =
      ev ![x, addOf B.G.F z w] B.sy * ev ![z, w, x] B.ph1 := by
  have h := congrArg (ev ![x, z, w]) B.sy_law
  evs at h
  exact h

theorem sy_inv_at {x z : Pt R n d} (hx : Z x) (hz : Z z) : ev ![x, z] B.sy * ev ![z, x] B.sy = 1 := by
  have h := congrArg (ev ![x, z]) B.sy_inv
  evs at h
  exact h

theorem symmetric_zero_right_at {x : Pt R n d} (hx : Z x) : ev ![x, 0] B.sy = 1 := by
  have h := congrArg (ev ![x]) B.symmetry_zero_snd
  evs at h
  exact h

theorem second_form_zero_left_at {x z : Pt R n d} (hx : Z x) (hz : Z z) : ev ![0, x, z] B.ph2 = 1 := by
  have h := congrArg (ev ![x, z]) B.cocycleRight_zero_fst
  evs at h
  exact h

theorem first_form_zero_right_at {x z : Pt R n d} (hx : Z x) (hz : Z z) : ev ![x, z, 0] B.ph1 = 1 := by
  have h := congrArg (ev ![x, z]) B.cocycleLeft_zero_thd
  evs at h
  exact h

theorem interchange_at {x y z w : Pt R n d} (hx : Z x) (hy : Z y) (hz : Z z) (hw : Z w) :
    ev ![x, y, z] B.ph1 * ev ![x, y, w] B.ph1 * ev ![addOf B.G.F x y, z, w] B.ph2 =
      ev ![x, z, w] B.ph2 * ev ![y, z, w] B.ph2 * ev ![x, y, addOf B.G.F z w] B.ph1 := by
  have h := congrArg (ev ![x, y, z, w]) B.interchange
  evs at h
  exact h

end Laws

end PositivityTheory.HtPt.Cc
