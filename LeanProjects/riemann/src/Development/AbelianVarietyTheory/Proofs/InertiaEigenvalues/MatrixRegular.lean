import Mathlib

noncomputable section

namespace GlobalTheory.OppRad

open scoped Classical

section Ring

variable {R : Type} [Ring R]

def U (p q : R) : Subgroup Rˣ where
  carrier := {u | p * (u.val - 1) = u.val - 1 ∧ (u.val - 1) * q = u.val - 1}
  one_mem' := by simp
  mul_mem' := by
    rintro u v ⟨a1, a2⟩ ⟨b1, b2⟩
    constructor
    · have e : (u * v).val - 1 = (u.val - 1) * v.val + (v.val - 1) := by rw [Units.val_mul]; noncomm_ring
      rw [e, mul_add, ← mul_assoc, a1, b1]
    · have e : (u * v).val - 1 = u.val * (v.val - 1) + (u.val - 1) := by rw [Units.val_mul]; noncomm_ring
      rw [e, add_mul, mul_assoc, a2, b2]
  inv_mem' := by
    rintro u ⟨a1, a2⟩
    constructor
    · have e : (u⁻¹).val - 1 = -((u.val - 1) * (u⁻¹).val) := by rw [sub_mul, Units.mul_inv]; noncomm_ring
      rw [e, mul_neg, ← mul_assoc, a1]
    · have e : (u⁻¹).val - 1 = -((u⁻¹).val * (u.val - 1)) := by rw [mul_sub, Units.inv_mul]; noncomm_ring
      rw [e, neg_mul, mul_assoc, a2]

theorem mem_U {p q : R} {u : Rˣ} : u ∈ U p q ↔ p * (u.val - 1) = u.val - 1 ∧ (u.val - 1) * q = u.val - 1 := Iff.rfl

def un (x : R) (h : x * x = 0) : Rˣ :=
  ⟨1 + x, 1 - x, by rw [add_mul, mul_sub, mul_sub, h]; simp, by rw [sub_mul, mul_add, mul_add, h]; simp⟩

@[simp] theorem un_val (x : R) (h : x * x = 0) : (un x h).val = 1 + x := rfl

theorem un_mem {p q x : R} (h : x * x = 0) (h1 : p * x = x) (h2 : x * q = x) : un x h ∈ U p q := by
  simpa [mem_U] using ⟨h1, h2⟩

theorem conj_mem {p q p' q' : R} {w u : Rˣ} (hp : w.val * p' = p * w.val) (hq : w.val * q' = q * w.val)
    (hu : u ∈ U p' q') : w * u * w⁻¹ ∈ U p q := by
  have e : (w * u * w⁻¹).val - 1 = w.val * (u.val - 1) * (w⁻¹).val := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv]; rfl
  have hq' : (w⁻¹).val * q = q' * (w⁻¹).val := by
    rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, hq, Units.mul_inv_cancel_right]
  rw [mem_U, e]
  constructor
  · rw [← mul_assoc, ← mul_assoc, ← hp, mul_assoc w.val, hu.1]
  · rw [mul_assoc _ _ q, hq', ← mul_assoc, mul_assoc w.val, hu.2]

theorem inv_rel {p p' : R} {w : Rˣ} (hp : w.val * p' = p * w.val) : (w⁻¹).val * p = p' * (w⁻¹).val := by
  rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, hp, Units.mul_inv_cancel_right]

theorem U_comm {p q : R} (h : q * p = 0) {u v : Rˣ} (hu : u ∈ U p q) (hv : v ∈ U p q) : u * v = v * u := by
  have k : ∀ {u v : Rˣ}, u ∈ U p q → v ∈ U p q → (u * v).val = u.val + v.val - 1 := fun {u v} hu hv => by
    have : (u.val - 1) * (v.val - 1) = 0 := by rw [← hu.2, ← hv.1, mul_assoc, ← mul_assoc q, h]; simp
    rw [Units.val_mul, ← sub_zero (u.val * v.val), ← this]; noncomm_ring
  exact Units.ext (by rw [k hu hv, k hv hu, add_comm])

end Ring

section Sum

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)

def S (H : Subgroup G) : V →ₗ[ℂ] V := haveI := Fintype.ofFinite H; ∑ h : H, π h

theorem S_apply (H : Subgroup G) [Fintype H] (v : V) : S π H v = ∑ h : H, π h v := by
  rw [S, LinearMap.sum_apply]
  congr!

variable {π}

theorem S_conj {H K : Subgroup G} {w : G} (h1 : ∀ u ∈ H, w * u * w⁻¹ ∈ K) (h2 : ∀ u ∈ K, w⁻¹ * u * w⁻¹⁻¹ ∈ H)
    (v : V) : π w (S π H v) = S π K (π w v) := by
  haveI := Fintype.ofFinite H
  haveI := Fintype.ofFinite K
  rw [S_apply, S_apply, map_sum]
  refine Fintype.sum_equiv ⟨fun u => ⟨_, h1 u u.2⟩, fun u => ⟨_, h2 u u.2⟩, fun u => Subtype.ext (by simp [mul_assoc]),
    fun u => Subtype.ext (by simp [mul_assoc])⟩ _ _ fun u => ?_
  simp [← Module.End.mul_apply, ← map_mul]

theorem S_right {H : Subgroup G} {h : G} (hh : h ∈ H) (v : V) : S π H (π h v) = S π H v := by
  haveI := Fintype.ofFinite H
  rw [S_apply, S_apply]
  refine Fintype.sum_equiv (Equiv.mulRight (⟨h, hh⟩ : H)) _ _ fun u => ?_
  simp

theorem S_left {H : Subgroup G} {h : G} (hh : h ∈ H) (v : V) : π h (S π H v) = S π H v := by
  rw [S_conj (K := H) (fun u hu => mul_mem (mul_mem hh hu) (inv_mem hh))
    (fun u hu => mul_mem (mul_mem (inv_mem hh) hu) (inv_mem (inv_mem hh))), S_right hh]

theorem S_comm {H : Subgroup G} {h : G} (hh : ∀ u ∈ H, h * u = u * h) (v : V) :
    π h (S π H v) = S π H (π h v) :=
  S_conj (fun u hu => by rwa [hh u hu, mul_inv_cancel_right])
    (fun u hu => by rwa [inv_inv, mul_assoc, ← hh u hu, inv_mul_cancel_left]) v

theorem S_S {H K : Subgroup G} (hle : H ≤ K) {v : V} (hv : S π K v = 0) : S π K (S π H v) = 0 := by
  haveI := Fintype.ofFinite H
  rw [S_apply π H, map_sum]
  exact Finset.sum_eq_zero fun u _ => by rw [S_right (hle u.2), hv]

theorem eq_zero_of_S {H : Subgroup G} {v : V} (hv : ∀ h ∈ H, π h v = v) (h0 : S π H v = 0) : v = 0 := by
  haveI := Fintype.ofFinite H
  rw [S_apply, Finset.sum_congr rfl fun (u : H) _ => hv u u.2, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h0
  exact (smul_eq_zero.1 h0).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

end Sum

variable {R V : Type} [Ring R] [Finite R] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ Rˣ V}

theorem S_U {p q p' q' : R} {w : Rˣ} (hp : w.val * p' = p * w.val) (hq : w.val * q' = q * w.val) (v : V) :
    π w (S π (U p' q') v) = S π (U p q) (π w v) :=
  S_conj (fun _ => conj_mem hp hq) (fun _ => conj_mem (inv_rel hp) (inv_rel hq)) v

variable (π) in

def OppInj (p q : R) : Prop := ∀ v : V, (∀ u ∈ U p q, π u v = v) → S π (U q p) v = 0 → v = 0

theorem step {a b c d : R} (aa : a * a = a) (bb : b * b = b) (cc : c * c = c) (dd : d * d = d)
    (ab : a * b = 0) (ac : a * c = 0) (ad : a * d = 0) (ba : b * a = 0) (bc : b * c = 0) (bd : b * d = 0)
    (ca : c * a = 0) (cb : c * b = 0) (cd : c * d = 0) (da : d * a = 0) (db : d * b = 0) (dc : d * c = 0)
    (h1 : OppInj π a c) (h2 : OppInj π (a + b) d) {v : V} (hv : ∀ u ∈ U (a + b) (c + d), π u v = v)
    (h0 : S π (U (c + d) (a + b)) v = 0) : S π (U (a + c) (b + d)) v = 0 := by
  have t : ∀ {x y z : R}, x * y = z → ∀ r, x * (y * r) = z * r := fun h r => by rw [← mul_assoc, h]
  have dec : ∀ {p q : R} {u : Rˣ}, u ∈ U p q → ∃ x, u.val = 1 + p * (x * q) := fun {p q u} hu =>
    ⟨u.val - 1, by rw [hu.2, hu.1, add_sub_cancel]⟩
  have H := And.intro (And.intro (And.intro (And.intro aa (t aa)) (And.intro bb (t bb)))
      (And.intro (And.intro cc (t cc)) (And.intro dd (t dd))))
    (And.intro (And.intro (And.intro (And.intro (And.intro ab (t ab)) (And.intro ac (t ac)))
      (And.intro (And.intro ad (t ad)) (And.intro ba (t ba))))
      (And.intro (And.intro (And.intro bc (t bc)) (And.intro bd (t bd)))
      (And.intro (And.intro ca (t ca)) (And.intro cb (t cb)))))
      (And.intro (And.intro (And.intro cd (t cd)) (And.intro da (t da)))
      (And.intro (And.intro db (t db)) (And.intro dc (t dc)))))
  set z := S π (U (a + c) (b + d)) v with hz
  have k1 : ∀ u ∈ U a c, π u z = z := fun u hu => by
    obtain ⟨x, hx⟩ := dec hu
    rw [hz, S_U (p := a + c) (q := b + d), hv u] <;>
      simp [mem_U, hx, mul_add, add_mul, mul_assoc, H] <;> abel
  have k2 : ∀ u ∈ U (a + b + c) d, π u z = z := fun u hu => by
    obtain ⟨x, hx⟩ := dec hu
    have e : u = un (b * (x * d)) (by simp [mul_assoc, H]) *
        un ((a + c) * (x * d)) (by simp [mul_add, add_mul, mul_assoc, H]) :=
      Units.ext (by simp [hx, mul_add, add_mul, mul_assoc, H]; abel)
    rw [e, map_mul, Module.End.mul_apply, hz, S_left, S_U (p := a + c) (q := b + d), hv] <;>
      simp [mem_U, mul_add, add_mul, mul_assoc, H] <;> abel
  have k3 : S π (U (c + d) (a + b)) z = 0 := by
    haveI := Fintype.ofFinite (U (a + c) (b + d))
    rw [hz, S_apply π (U (a + c) (b + d)), map_sum]
    refine Finset.sum_eq_zero fun u _ => ?_
    obtain ⟨x, hx⟩ := dec u.2
    have e : u.1 = un (c * (x * b)) (by simp [mul_assoc, H]) *
        (un (a * (x * b) + c * (x * d)) (by simp [mul_add, add_mul, mul_assoc, H]) *
          un (a * (x * d)) (by simp [mul_assoc, H])) :=
      Units.ext (by simp [hx, mul_add, add_mul, mul_assoc, H]; abel)
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, S_right, hv,
      ← S_U (p' := c + d) (q' := a + b), h0, map_zero] <;>
      simp [mem_U, mul_add, add_mul, mul_assoc, H] <;> abel
  have hqp : (a + b) * (c + d) = 0 := by simp [mul_add, add_mul, H]
  have l1 : U c a ≤ U (c + d) (a + b) := fun u hu => by
    obtain ⟨x, hx⟩ := dec hu
    simp [mem_U, hx, mul_add, add_mul, mul_assoc, H]
  have l2 : U d (a + b) ≤ U (c + d) (a + b) := fun u hu => by
    obtain ⟨x, hx⟩ := dec hu
    simp [mem_U, hx, mul_add, add_mul, mul_assoc, H]
  refine h1 z k1 (h2 _ (fun u hu => ?_) (eq_zero_of_S (fun u hu => ?_) (S_S l2 (S_S l1 k3))))
  · haveI := Fintype.ofFinite (U c a)
    rw [S_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨x, hx⟩ := dec hu
    obtain ⟨y, hy⟩ := dec (inv_mem k.2)
    have : k.1⁻¹ * u * k.1⁻¹⁻¹ ∈ U (a + b + c) d := by
      refine conj_mem (p' := a + b + c) (q' := d) ?_ ?_ ?_ <;>
        simp [mem_U, hx, hy, mul_add, add_mul, mul_assoc, H] <;> abel
    conv_rhs => rw [← k2 _ this]
    simp [← Module.End.mul_apply, ← map_mul, mul_assoc]
  · obtain ⟨x, hx⟩ := dec hu
    have e : u = un (d * (x * (a + b))) (by simp [mul_add, add_mul, mul_assoc, H]) *
        (un (c * (x * a)) (by simp [mul_assoc, H]) * un (c * (x * b)) (by simp [mul_assoc, H])) :=
      Units.ext (by simp [hx, mul_add, add_mul, mul_assoc, H]; abel)
    have m1 : un (c * (x * a)) (by simp [mul_assoc, H]) ∈ U c a := by simp [mem_U, mul_assoc, H]
    have m2 : un (c * (x * b)) (by simp [mul_assoc, H]) ∈ U (c + d) (a + b) := by
      simp [mem_U, mul_add, add_mul, mul_assoc, H]
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      S_comm fun w hw => U_comm hqp m2 (l2 hw), S_comm fun w hw => U_comm hqp m2 (l1 hw),
      S_comm fun w hw => U_comm hqp (l1 m1) (l2 hw), S_left m1, hz, S_left, S_left] <;>
      simp [mem_U, mul_add, add_mul, mul_assoc, H]

theorem oppInj (hreg : ∀ x : R, ∃ y, x * y * x = x) {p q : R} (pp : p * p = p) (qq : q * q = q)
    (pq : p * q = 0) (qp : q * p = 0) : OppInj π p q := by
  generalize hn : {x : R | (p + q) * x = x}.ncard = n
  induction n using Nat.strong_induction_on generalizing p q with
  | _ n ih =>
  intro v hv h0
  haveI := Fintype.ofFinite (U q p)
  have h1 : S π (U p q) (S π (U q p) v) = 0 := by rw [h0, map_zero]
  rw [S_apply π (U q p), map_sum, Finset.sum_eq_single 1 (fun u _ hu => ?_) (by simp)] at h1
  · exact eq_zero_of_S hv (by simpa using h1)
  obtain ⟨X, hX⟩ : ∃ X, u.1.val = 1 + X := ⟨u.1.val - 1, by simp⟩
  have X0 : X ≠ 0 := fun e => hu (Subtype.ext (Units.ext (by simpa [e] using hX)))
  have qX : q * X = X := by simpa [hX] using u.2.1
  have Xp : X * p = X := by simpa [hX] using u.2.2
  obtain ⟨y, hy⟩ := hreg X
  have t : ∀ {x y z : R}, x * y = z → ∀ r, x * (y * r) = z * r := fun h r => by rw [← mul_assoc, h]
  obtain ⟨Y, pY, Yq, XYX, YXY⟩ : ∃ Y, p * Y = Y ∧ Y * q = Y ∧ X * (Y * X) = X ∧ Y * (X * Y) = Y := by
    have hy' : ∀ r, X * (y * (X * r)) = X * r := fun r => by rw [← mul_assoc, ← mul_assoc, hy]
    have hy'' : X * (y * X) = X := by rw [← mul_assoc, hy]
    refine ⟨p * (y * (X * (y * q))), ?_, ?_, ?_, ?_⟩ <;> simp [mul_assoc, t pp, qq, qX, t qX, t Xp, hy', hy'']
  have pX : p * X = 0 := by rw [← qX, t pq, zero_mul]
  have Xq : X * q = 0 := by rw [← Xp, mul_assoc, pq, mul_zero]
  have qY : q * Y = 0 := by rw [← pY, t qp, zero_mul]
  have Yp : Y * p = 0 := by rw [← Yq, mul_assoc, qp, mul_zero]
  have XX : X * X = 0 := by rw [← t Xp X, pX, mul_zero]
  have YY : Y * Y = 0 := by rw [← t Yq Y, qY, mul_zero]
  have XYX' : ∀ r, X * (Y * (X * r)) = X * r := fun r => by rw [← mul_assoc Y, t XYX]
  have YXY' : ∀ r, Y * (X * (Y * r)) = Y * r := fun r => by rw [← mul_assoc X, t YXY]
  have H := And.intro (And.intro (And.intro (And.intro pp (t pp)) (And.intro qq (t qq)))
      (And.intro (And.intro pq (t pq)) (And.intro qp (t qp))))
    (And.intro (And.intro (And.intro (And.intro (And.intro qX (t qX)) (And.intro Xp (t Xp)))
      (And.intro (And.intro pY (t pY)) (And.intro Yq (t Yq))))
      (And.intro (And.intro (And.intro pX (t pX)) (And.intro Xq (t Xq)))
      (And.intro (And.intro qY (t qY)) (And.intro Yp (t Yp)))))
      (And.intro (And.intro (And.intro XX (t XX)) (And.intro YY (t YY)))
      (And.intro (And.intro XYX XYX') (And.intro YXY YXY'))))
  have lt : ∀ {r s : R}, (p + q) * r = r → (p + q) * s = s → r * s = 0 → s ≠ 0 →
      {x : R | r * x = x}.ncard < n := fun {r s} a1 a2 a3 a4 => by
    rw [← hn]
    refine Set.ncard_lt_ncard ⟨fun x (hx : r * x = x) => ?_, fun h => a4 ?_⟩
    · show (p + q) * x = x
      rw [← hx, t a1]
    · exact (h (show s ∈ {x | (p + q) * x = x} from a2)).symm.trans a3
  have e1 : p - Y * X + Y * X = p := sub_add_cancel _ _
  have e2 : X * Y + (q - X * Y) = q := add_sub_cancel _ _
  have key := step (π := π) (a := p - Y * X) (b := Y * X) (c := X * Y) (d := q - X * Y) (v := v)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (ih _ (lt (s := Y * X) ?_ ?_ ?_ fun e => X0 (by rw [← XYX, e, mul_zero])) ?_ ?_ ?_ ?_ rfl)
    (ih _ (lt (s := X * Y) ?_ ?_ ?_ fun e => X0 (by rw [← XYX, ← mul_assoc, e, zero_mul])) ?_ ?_ ?_ ?_ rfl)
    (by rwa [e1, e2]) (by rwa [e1, e2])
  · have m : un Y YY ∈ U p q := un_mem YY pY Yq
    have e : u.1 = un Y YY * (((un Y YY)⁻¹ * u.1 * (un Y YY)⁻¹) * un Y YY) := by group
    have hw : ((un Y YY)⁻¹ * u.1 * (un Y YY)⁻¹).val = (1 - Y) * (1 + X) * (1 - Y) := by
      rw [Units.val_mul, Units.val_mul, hX]; rfl
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, S_right m, hv _ m,
      ← S_U (p' := p - Y * X + X * Y) (q' := Y * X + (q - X * Y)), key, map_zero] <;>
    · rw [hw]
      simp [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, H]
      try abel
  all_goals simp [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, H]

theorem matrix_regular {F n : Type} [Field F] [Fintype n] [DecidableEq n] (x : Matrix n n F) :
    ∃ y, x * y * x = x := by
  let f := Matrix.toLinAlgEquiv' x
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨r, hr⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  refine ⟨Matrix.toLinAlgEquiv'.symm (s ∘ₗ r), Matrix.toLinAlgEquiv'.injective ?_⟩
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  refine LinearMap.ext fun w => ?_
  have h1 : r (f w) = f.rangeRestrict w := LinearMap.congr_fun hr (f.rangeRestrict w)
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict w))
  change f (s (r (f w))) = f w
  rw [h1]
  exact h2

end GlobalTheory.OppRad
