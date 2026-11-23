import Mathlib
import GroundTheory.LocalFields.FormalGroups.Inverse

namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries

variable {R : Type*} [CommRing R]

theorem hasSubst_powerSeries_subst {τ : Type*} {x : MvPowerSeries τ R}
    (hx : PowerSeries.HasSubst x) {φ : PowerSeries R} (hφ : PowerSeries.HasSubst φ) :
    PowerSeries.HasSubst (PowerSeries.subst x φ) := by
  simpa [PowerSeries.coe_substAlgHom] using hφ.comp hx

theorem subst_powerSeries_subst {τ υ : Type*} {a : MvPowerSeries τ R}
    (ha : PowerSeries.HasSubst a) {b : τ → MvPowerSeries υ R} (hb : HasSubst b)
    (φ : PowerSeries R) :
    subst b (PowerSeries.subst a φ) = PowerSeries.subst (subst b a) φ := by
  have ha' : HasSubst (fun _ : Unit => a) := PowerSeries.hasSubst_iff.mp ha
  rw [PowerSeries.subst_def, PowerSeries.subst_def, subst_comp_subst_apply ha' hb]

theorem subst_X_X (f : MvPowerSeries (Fin 2) R) : subst ![X 0, X 1] f = f := by
  have : (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = X := by
    funext i; fin_cases i <;> rfl
  rw [this, subst_self]
  rfl

theorem constantCoeff_powerSeries_subst {τ : Type*} {a : MvPowerSeries τ R}
    (ha : constantCoeff a = 0) {φ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0) :
    constantCoeff (PowerSeries.subst a φ) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha φ hφ

theorem constantCoeff_subst_of_powerSeries {φ ψ : PowerSeries R}
    (hψ : PowerSeries.constantCoeff ψ = 0) (hφ : PowerSeries.constantCoeff φ = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst ψ φ) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hψ φ hφ

theorem constantCoeff_subst_pair_of_powerSeries (G : FormalGroup R) {φ ψ : PowerSeries R}
    (hφ : PowerSeries.constantCoeff φ = 0) (hψ : PowerSeries.constantCoeff ψ = 0) :
    PowerSeries.constantCoeff (subst ![φ, ψ] G.toPowerSeries : PowerSeries R) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_pair hφ hψ)
    (fun i => by fin_cases i; exacts [hφ, hψ]) G.zero_constantCoeff

variable {F G H : FormalGroup R}

theorem point_hasSubst_pair {σ : Type*} (x y : F.Point σ) : HasSubst ![x.val, y.val] :=
  hasSubst_of_constantCoeff_nilpotent fun i => by fin_cases i; exacts [x.prop, y.prop]

noncomputable def substPoint (φ : PowerSeries R) (hφ : PowerSeries.constantCoeff φ = 0)
    {σ : Type*} (x : F.Point σ) : G.Point σ :=
  ⟨PowerSeries.subst x.val φ,
    hasSubst_powerSeries_subst x.prop (PowerSeries.HasSubst.of_constantCoeff_zero' hφ)⟩

theorem substPoint_val (φ : PowerSeries R) (hφ : PowerSeries.constantCoeff φ = 0)
    {σ : Type*} (x : F.Point σ) :
    (substPoint (G := G) φ hφ x).val = PowerSeries.subst x.val φ := rfl

theorem substPoint_congr {φ ψ : PowerSeries R} (e : φ = ψ) (hφ : PowerSeries.constantCoeff φ = 0)
    (hψ : PowerSeries.constantCoeff ψ = 0) {σ : Type*} (x : F.Point σ) :
    (substPoint φ hφ x : G.Point σ) = substPoint ψ hψ x := by
  subst e; rfl

theorem substPoint_X {σ : Type*} (x : F.Point σ) (h) :
    (substPoint PowerSeries.X h x : F.Point σ) = x :=
  Subtype.ext (PowerSeries.subst_X x.prop)

theorem substPoint_zero {σ : Type*} (x : F.Point σ) (h) :
    (substPoint 0 h x : G.Point σ) = 0 := by
  apply Subtype.ext
  rw [substPoint_val, ← PowerSeries.coe_substAlgHom x.prop, map_zero]
  rfl

theorem substPoint_zero_point {σ : Type*} (φ : PowerSeries R) (hφ) :
    (substPoint φ hφ (0 : F.Point σ) : G.Point σ) = 0 :=
  Subtype.ext (PowerSeries.subst_zero_of_constantCoeff_zero hφ)

theorem substPoint_substPoint {φ ψ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0)
    (hψ : PowerSeries.constantCoeff ψ = 0) (h) {σ : Type*} (x : F.Point σ) :
    (substPoint φ hφ (substPoint ψ hψ x : G.Point σ) : H.Point σ) =
      substPoint (PowerSeries.subst ψ φ) h x := by
  apply Subtype.ext
  simp only [substPoint_val]
  exact (PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hψ) x.prop φ).symm

theorem substPoint_subst_pair {φ ψ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0)
    (hψ : PowerSeries.constantCoeff ψ = 0) (h) {σ : Type*} (x : F.Point σ) :
    (substPoint (subst ![φ, ψ] G.toPowerSeries) h x : G.Point σ) =
      substPoint φ hφ x + substPoint ψ hψ x := by
  apply Subtype.ext
  rw [substPoint_val, FormalGroup.add_apply, substPoint_val, substPoint_val]
  exact subst_subst_pair (hasSubst_pair hφ hψ) x.prop _

theorem substPoint_inv_subst {φ : PowerSeries R} (hφ : PowerSeries.constantCoeff φ = 0) (h)
    {σ : Type*} (x : F.Point σ) :
    (substPoint (PowerSeries.subst φ (inv G)) h x : G.Point σ) = -substPoint φ hφ x := by
  apply Subtype.ext
  rw [substPoint_val, neg_point_val, substPoint_val]
  exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hφ)
    x.prop _

variable (F G) in

@[ext]
structure Hom where

  toPowerSeries : PowerSeries R

  constantCoeff_eq_zero : PowerSeries.constantCoeff toPowerSeries = 0

  map_add : PowerSeries.subst F.toPowerSeries toPowerSeries =
    subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) toPowerSeries,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) toPowerSeries] G.toPowerSeries

namespace Hom

theorem constantCoeff_eq_zero' (f : Hom F G) : constantCoeff f.toPowerSeries = 0 :=
  f.constantCoeff_eq_zero

noncomputable def apply (f : Hom F G) {σ : Type*} (x : F.Point σ) : G.Point σ :=
  substPoint f.toPowerSeries f.constantCoeff_eq_zero x

theorem apply_val (f : Hom F G) {σ : Type*} (x : F.Point σ) :
    (f.apply x).val = PowerSeries.subst x.val f.toPowerSeries := rfl

theorem apply_add (f : Hom F G) {σ : Type*} (x y : F.Point σ) :
    f.apply (x + y) = f.apply x + f.apply y := by
  apply Subtype.ext
  have hxy := point_hasSubst_pair x y
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) R) = 0 := fun i => by simp
  have hpair := hasSubst_pair (constantCoeff_powerSeries_subst (hX 0) f.constantCoeff_eq_zero)
    (constantCoeff_powerSeries_subst (hX 1) f.constantCoeff_eq_zero)
  have h := congrArg (subst ![x.val, y.val]) f.map_add
  rw [subst_powerSeries_subst hF hxy, subst_comp_subst_apply hpair hxy] at h
  rw [apply_val, FormalGroup.add_apply, h, FormalGroup.add_apply]
  congr 1
  funext i
  fin_cases i
  · simp [subst_powerSeries_subst (PowerSeries.HasSubst.X (0 : Fin 2)) hxy, subst_X hxy,
      apply_val]
  · simp [subst_powerSeries_subst (PowerSeries.HasSubst.X (1 : Fin 2)) hxy, subst_X hxy,
      apply_val]

theorem apply_zero (f : Hom F G) {σ : Type*} : f.apply (0 : F.Point σ) = 0 :=
  substPoint_zero_point _ _

private noncomputable def genPoint (F : FormalGroup R) (i : Fin 2) : F.Point (Fin 2) :=
  ⟨X i, PowerSeries.HasSubst.X i⟩

noncomputable def ofPoints (φ : PowerSeries R) (hφ : PowerSeries.constantCoeff φ = 0)
    (h : ∀ x y : F.Point (Fin 2),
      (substPoint φ hφ (x + y) : G.Point (Fin 2)) = substPoint φ hφ x + substPoint φ hφ y) :
    Hom F G where
  toPowerSeries := φ
  constantCoeff_eq_zero := hφ
  map_add := by
    have := congrArg Subtype.val (h (genPoint F 0) (genPoint F 1))
    rw [substPoint_val, FormalGroup.add_apply, FormalGroup.add_apply, substPoint_val,
      substPoint_val] at this
    simpa [genPoint, subst_X_X] using this

@[simp]
theorem ofPoints_toPowerSeries (φ : PowerSeries R) (hφ) (h) :
    (ofPoints (F := F) (G := G) φ hφ h).toPowerSeries = φ := rfl

noncomputable def comp (g : Hom G H) (f : Hom F G) : Hom F H :=
  ofPoints (PowerSeries.subst f.toPowerSeries g.toPowerSeries)
    (constantCoeff_subst_of_powerSeries f.constantCoeff_eq_zero g.constantCoeff_eq_zero)
    fun x y => by
      rw [← substPoint_substPoint g.constantCoeff_eq_zero f.constantCoeff_eq_zero,
        ← substPoint_substPoint g.constantCoeff_eq_zero f.constantCoeff_eq_zero,
        ← substPoint_substPoint g.constantCoeff_eq_zero f.constantCoeff_eq_zero]
      exact (congrArg g.apply (f.apply_add x y)).trans (g.apply_add _ _)

theorem toPowerSeries_comp (g : Hom G H) (f : Hom F G) :
    (g.comp f).toPowerSeries = PowerSeries.subst f.toPowerSeries g.toPowerSeries := rfl

theorem apply_comp (g : Hom G H) (f : Hom F G) {σ : Type*} (x : F.Point σ) :
    (g.comp f).apply x = g.apply (f.apply x) :=
  (substPoint_substPoint _ _ _ x).symm

variable (F) in

noncomputable def id : Hom F F :=
  ofPoints PowerSeries.X PowerSeries.constantCoeff_X fun x y => by
    rw [substPoint_X, substPoint_X, substPoint_X]

theorem toPowerSeries_id : (id F).toPowerSeries = PowerSeries.X := rfl

theorem comp_assoc {K : FormalGroup R} (h : Hom H K) (g : Hom G H) (f : Hom F G) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext1
  simp only [toPowerSeries_comp]
  exact PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' g.constantCoeff_eq_zero)
    (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero) _

theorem id_comp (f : Hom F G) : (id G).comp f = f := by
  ext1
  exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero)

theorem comp_id (f : Hom F G) : f.comp (id F) = f := by
  ext1
  exact PowerSeries.X_subst _

noncomputable instance : Monoid (Hom F F) where
  mul g f := g.comp f
  one := id F
  mul_assoc h g f := comp_assoc h g f
  one_mul := id_comp
  mul_one := comp_id

theorem mul_def (g f : Hom F F) : g * f = g.comp f := rfl

theorem one_def : (1 : Hom F F) = id F := rfl

noncomputable def toPoint (f : Hom F G) : G.Point Unit :=
  ⟨f.toPowerSeries, PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero⟩

theorem toPoint_injective : Function.Injective (toPoint : Hom F G → G.Point Unit) :=
  fun _ _ h => Hom.ext (congrArg Subtype.val h)

theorem toPoint_comp (g : Hom G H) (f : Hom F G) : (g.comp f).toPoint = g.apply f.toPoint := rfl

noncomputable instance : Zero (Hom F G) where
  zero := ofPoints 0 (map_zero _) fun _ _ => by
    rw [substPoint_zero, substPoint_zero, substPoint_zero, add_zero]

theorem toPowerSeries_zero : (0 : Hom F G).toPowerSeries = 0 := rfl

theorem toPoint_zero : (0 : Hom F G).toPoint = 0 := rfl

theorem zero_apply {σ : Type*} (x : F.Point σ) : (0 : Hom F G).apply x = 0 :=
  substPoint_zero x _

section Comm

variable [G.IsComm]

noncomputable instance : Add (Hom F G) where
  add f g := ofPoints (subst ![f.toPowerSeries, g.toPowerSeries] G.toPowerSeries)
    (constantCoeff_subst_pair_of_powerSeries G f.constantCoeff_eq_zero g.constantCoeff_eq_zero)
    fun x y => by
      rw [substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero,
        substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero,
        substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero]
      exact (congrArg₂ (· + ·) (f.apply_add x y) (g.apply_add x y)).trans
        (add_add_add_comm _ _ _ _)

noncomputable instance : Neg (Hom F G) where
  neg f := ofPoints (PowerSeries.subst f.toPowerSeries (inv G))
    (constantCoeff_subst_of_powerSeries f.constantCoeff_eq_zero (constantCoeff_inv G))
    fun x y => by
      rw [substPoint_inv_subst f.constantCoeff_eq_zero, substPoint_inv_subst
        f.constantCoeff_eq_zero, substPoint_inv_subst f.constantCoeff_eq_zero]
      exact (congrArg Neg.neg (f.apply_add x y)).trans (neg_add _ _)

noncomputable instance : Sub (Hom F G) where
  sub f g := f + -g

noncomputable instance : SMul ℕ (Hom F G) where
  smul := nsmulRec

noncomputable instance : SMul ℤ (Hom F G) where
  smul := zsmulRec

theorem toPowerSeries_add (f g : Hom F G) :
    (f + g).toPowerSeries = subst ![f.toPowerSeries, g.toPowerSeries] G.toPowerSeries := rfl

theorem toPowerSeries_neg (f : Hom F G) :
    (-f).toPowerSeries = PowerSeries.subst f.toPowerSeries (inv G) := rfl

theorem toPoint_add (f g : Hom F G) : (f + g).toPoint = f.toPoint + g.toPoint := rfl

theorem toPoint_neg (f : Hom F G) : (-f).toPoint = -f.toPoint := rfl

theorem toPoint_sub (f g : Hom F G) : (f - g).toPoint = f.toPoint - g.toPoint := by
  rw [sub_eq_add_neg, ← toPoint_neg, ← toPoint_add]
  rfl

theorem toPoint_nsmul (f : Hom F G) (n : ℕ) : (n • f).toPoint = n • f.toPoint := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih =>
    rw [succ_nsmul, ← ih, ← toPoint_add]
    rfl

theorem toPoint_zsmul (f : Hom F G) (n : ℤ) : (n • f).toPoint = n • f.toPoint := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, natCast_zsmul, ← toPoint_nsmul]
    rfl
  | negSucc n =>
    rw [negSucc_zsmul, ← toPoint_nsmul, ← toPoint_neg]
    rfl

noncomputable instance : AddCommGroup (Hom F G) :=
  toPoint_injective.addCommGroup _ toPoint_zero toPoint_add toPoint_neg toPoint_sub
    toPoint_nsmul toPoint_zsmul

theorem add_apply (f g : Hom F G) {σ : Type*} (x : F.Point σ) :
    (f + g).apply x = f.apply x + g.apply x :=
  substPoint_subst_pair f.constantCoeff_eq_zero g.constantCoeff_eq_zero _ x

theorem neg_apply (f : Hom F G) {σ : Type*} (x : F.Point σ) : (-f).apply x = -f.apply x :=
  substPoint_inv_subst f.constantCoeff_eq_zero _ x

theorem comp_add (g : Hom G H) [H.IsComm] (f₁ f₂ : Hom F G) :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ :=
  toPoint_injective (by rw [toPoint_comp, toPoint_add, apply_add, toPoint_add]; rfl)

omit [G.IsComm] in
theorem add_comp [H.IsComm] (g₁ g₂ : Hom G H) (f : Hom F G) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f :=
  toPoint_injective (by rw [toPoint_comp, add_apply, toPoint_add]; rfl)

variable (F) in

theorem toPowerSeries_neg_id [F.IsComm] : (-id F).toPowerSeries = inv F :=
  PowerSeries.X_subst _

end Comm

section Ring

variable [F.IsComm]

noncomputable instance : Ring (Hom F F) :=
  { (inferInstance : AddCommGroup (Hom F F)), (inferInstance : Monoid (Hom F F)) with
    left_distrib := fun f g h => comp_add f g h
    right_distrib := fun f g h => add_comp f g h
    zero_mul := fun f => toPoint_injective (by
      rw [mul_def, toPoint_comp, zero_apply]; rfl)
    mul_zero := fun f => toPoint_injective (by
      rw [mul_def, toPoint_comp]
      exact (apply_zero f).trans rfl) }

theorem one_apply {σ : Type*} (x : F.Point σ) : (1 : Hom F F).apply x = x :=
  substPoint_X x _

theorem intCast_apply (n : ℤ) {σ : Type*} (x : F.Point σ) : (n : Hom F F).apply x = n • x := by
  induction n using Int.induction_on with
  | zero => rw [Int.cast_zero, zero_apply, zero_zsmul]
  | succ n ih => rw [Int.cast_add, Int.cast_one, add_apply, ih, one_apply, add_zsmul, one_zsmul]
  | pred n ih =>
    rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg, add_apply, neg_apply, ih, one_apply,
      sub_zsmul, one_zsmul]

end Ring

end Hom

theorem two_le_order_subst_higher (F : FormalGroup R) {τ : Type*} {a b : MvPowerSeries τ R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    (2 : ℕ∞) ≤ order (subst ![a, b] (higher F)) := by
  have := le_order_subst_sub_subst (f := higher F) (g := 0) (hasSubst_pair ha hb)
    (fun i => by fin_cases i <;> simp [ha, hb]) (by simpa using two_le_order_higher F)
  rwa [← subst_sub (hasSubst_pair ha hb), sub_zero] at this

theorem coeff_one_subst_pair (F : FormalGroup R) {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (subst ![f, g] F.toPowerSeries : PowerSeries R) =
      PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  change coeff (Finsupp.single () 1) (subst ![f, g] F.toPowerSeries) =
    coeff (Finsupp.single () 1) f + coeff (Finsupp.single () 1) g
  rw [subst_eq_add_add_subst_higher F (hasSubst_pair hf hg), map_add, map_add,
    coeff_of_lt_order (lt_of_lt_of_le (by simp) (two_le_order_subst_higher F hf hg)), add_zero]

theorem coeff_one_subst {f g : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst g f) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 g := by
  set c := PowerSeries.coeff 1 f with hc
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have hdec : f = PowerSeries.C c * PowerSeries.X + (f - PowerSeries.C c * PowerSeries.X) := by
    ring
  have h2 : (2 : ℕ∞) ≤ (f - PowerSeries.C c * PowerSeries.X).order := by
    refine PowerSeries.nat_le_order _ 2 fun i hi => ?_
    interval_cases i
    · simp [hf]
    · simp [hc]
  have h2' : (2 : ℕ∞) ≤ PowerSeries.order
      (PowerSeries.subst g (f - PowerSeries.C c * PowerSeries.X)) :=
    h2.trans (PowerSeries.le_order_subst_left' hg)
  conv_lhs => rw [hdec]
  rw [PowerSeries.subst_add hgs, PowerSeries.subst_mul hgs, PowerSeries.subst_X hgs, map_add,
    PowerSeries.coeff_of_lt_order 1 (lt_of_lt_of_le (by norm_num) h2'), add_zero]
  change PowerSeries.coeff 1 (PowerSeries.subst g (PowerSeries.C c) * g) = _
  rw [PowerSeries.subst_C]
  exact PowerSeries.coeff_C_mul _ _ _

namespace Hom

theorem coeff_one_comp (g : Hom G H) (f : Hom F G) :
    PowerSeries.coeff 1 (g.comp f).toPowerSeries =
      PowerSeries.coeff 1 g.toPowerSeries * PowerSeries.coeff 1 f.toPowerSeries :=
  coeff_one_subst g.constantCoeff_eq_zero f.constantCoeff_eq_zero

theorem coeff_one_add [G.IsComm] (f g : Hom F G) :
    PowerSeries.coeff 1 (f + g).toPowerSeries =
      PowerSeries.coeff 1 f.toPowerSeries + PowerSeries.coeff 1 g.toPowerSeries :=
  coeff_one_subst_pair G f.constantCoeff_eq_zero g.constantCoeff_eq_zero

theorem coeff_one_id : PowerSeries.coeff 1 (id F).toPowerSeries = 1 := by
  simp [toPowerSeries_id]

end Hom

variable (F) in

noncomputable def linearCoeff [F.IsComm] : Hom F F →+* R where
  toFun f := PowerSeries.coeff 1 f.toPowerSeries
  map_one' := Hom.coeff_one_id
  map_mul' g f := Hom.coeff_one_comp g f
  map_zero' := by simp [Hom.toPowerSeries_zero]
  map_add' f g := Hom.coeff_one_add f g

theorem linearCoeff_apply [F.IsComm] (f : Hom F F) :
    linearCoeff F f = PowerSeries.coeff 1 f.toPowerSeries := rfl

variable (F G) in

structure Iso where

  hom : Hom F G

  inv : Hom G F
  hom_comp_inv : hom.comp inv = Hom.id G
  inv_comp_hom : inv.comp hom = Hom.id F

namespace Iso

variable (F) in

noncomputable def refl : Iso F F := ⟨Hom.id F, Hom.id F, Hom.id_comp _, Hom.id_comp _⟩

def symm (e : Iso F G) : Iso G F := ⟨e.inv, e.hom, e.inv_comp_hom, e.hom_comp_inv⟩

noncomputable def trans (e : Iso F G) (e' : Iso G H) : Iso F H where
  hom := e'.hom.comp e.hom
  inv := e.inv.comp e'.inv
  hom_comp_inv := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc e.hom, e.hom_comp_inv, Hom.id_comp, e'.hom_comp_inv]
  inv_comp_hom := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc e'.inv, e'.inv_comp_hom, Hom.id_comp, e.inv_comp_hom]

theorem isUnit_coeff_one (e : Iso F G) : IsUnit (PowerSeries.coeff 1 e.hom.toPowerSeries) := by
  have h := congrArg (fun f : Hom G G => PowerSeries.coeff 1 f.toPowerSeries) e.hom_comp_inv
  simp only [Hom.coeff_one_comp, Hom.coeff_one_id] at h
  exact IsUnit.of_mul_eq_one _ h

noncomputable def ofIsUnit (f : Hom F G) (hf : IsUnit (PowerSeries.coeff 1 f.toPowerSeries)) :
    Iso F G :=
  have hψ := PowerSeries.constantCoeff_substInvOfIsUnit f.toPowerSeries hf
  have hfψ : PowerSeries.subst (PowerSeries.substInvOfIsUnit f.toPowerSeries hf)
      f.toPowerSeries = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right _ f.constantCoeff_eq_zero hf
  have hψf : PowerSeries.subst f.toPowerSeries
      (PowerSeries.substInvOfIsUnit f.toPowerSeries hf) = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_left _ f.constantCoeff_eq_zero hf
  { hom := f
    inv := Hom.ofPoints (PowerSeries.substInvOfIsUnit f.toPowerSeries hf) hψ fun x y => by
      set u : F.Point (Fin 2) := substPoint _ hψ x + substPoint _ hψ y
      have hu : f.apply u = x + y := by
        rw [Hom.apply_add, Hom.apply, Hom.apply, substPoint_substPoint _ _
          (by rw [hfψ]; exact PowerSeries.constantCoeff_X), substPoint_substPoint _ _
          (by rw [hfψ]; exact PowerSeries.constantCoeff_X), substPoint_congr hfψ _
          PowerSeries.constantCoeff_X, substPoint_congr hfψ _ PowerSeries.constantCoeff_X,
          substPoint_X, substPoint_X]
      rw [← hu, Hom.apply, substPoint_substPoint _ _
          (by rw [hψf]; exact PowerSeries.constantCoeff_X),
        substPoint_congr hψf _ PowerSeries.constantCoeff_X, substPoint_X]
    hom_comp_inv := Hom.ext hfψ
    inv_comp_hom := Hom.ext hψf }

@[simp]
theorem ofIsUnit_hom (f : Hom F G) (hf : IsUnit (PowerSeries.coeff 1 f.toPowerSeries)) :
    (ofIsUnit f hf).hom = f := rfl

end Iso

theorem Hom.exists_iso_iff (f : Hom F G) :
    (∃ e : Iso F G, e.hom = f) ↔ IsUnit (PowerSeries.coeff 1 f.toPowerSeries) :=
  ⟨fun ⟨e, he⟩ => he ▸ e.isUnit_coeff_one, fun hf => ⟨Iso.ofIsUnit f hf, rfl⟩⟩

end GroundTheory.LocalField.FormalGroup
