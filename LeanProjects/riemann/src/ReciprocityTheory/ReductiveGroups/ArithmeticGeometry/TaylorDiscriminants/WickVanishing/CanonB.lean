import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CanonA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofComm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.TB.Canon

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {d n l : ℕ}

def ac (A : Q k d 1) (u : Q k d n) : Q k d n := sq ![u] A

private theorem sq_sq_lemma {m : ℕ} (b : Fin n → Q k d l) (a : Fin m → Q k d n) (p : Q k d m) :
    sq b (sq a p) = sq (fun j => sq b (a j)) p :=
  Subtype.ext (funext fun i => sb_sb b a (p.1 i))

@[simp] theorem sq_ac (b : Fin n → Q k d l) (A : Q k d 1) (u : Q k d n) : sq b (ac A u) = ac A (sq b u) := by
  show sq b (sq ![u] A) = sq ![sq b u] A
  have h : (fun j => sq b (![u] j)) = ![sq b u] := by
    funext j; fin_cases j; rfl
  rw [sq_sq_lemma, h]

theorem eval_two_add (f g : PS k 2 d) (u v : Q k d n) : E2 (f + g) u v = E2 f u v + E2 g u v := by
  unfold E2; exact map_add _ _ _
theorem eval_two_sub (f g : PS k 2 d) (u v : Q k d n) : E2 (f - g) u v = E2 f u v - E2 g u v := by
  unfold E2; exact map_sub _ _ _
theorem eval_two_eval_two (f : PS k 2 d) (p q : Q k d 2) (u v : Q k d n) : E2 (E2 f p q) u v = E2 f (sq ![u, v] p) (sq ![u, v] q) := by
  unfold E2
  have h : (fun j => sq ![u, v] (![p, q] j)) = ![sq ![u, v] p, sq ![u, v] q] := by
    funext j; fin_cases j <;> rfl
  rw [sb_sb, h]

variable [Algebra ℚ k]

theorem eval_two_smul (c : ℚ) (f : PS k 2 d) (u v : Q k d n) : E2 (c • f) u v = c • E2 f u v := by
  unfold E2; exact map_rat_smul _ _ _

variable (k d) in

def Bi : Submodule ℚ (PS k 2 d) where
  carrier := {f | (∀ (n) (x y v : Q k d n), E2 f (x + y) v = E2 f x v + E2 f y v) ∧
    ∀ (n) (x v w : Q k d n), E2 f x (v + w) = E2 f x v + E2 f x w}
  add_mem' := fun ha hb => ⟨fun n x y v => by simp only [eval_two_add, ha.1, hb.1]; ring,
    fun n x y v => by simp only [eval_two_add, ha.2, hb.2]; ring⟩
  zero_mem' := ⟨fun _ _ _ _ => by simp [E2], fun _ _ _ _ => by simp [E2]⟩
  smul_mem' := fun c f h => ⟨fun n x y v => by simp only [eval_two_smul, h.1, smul_add],
    fun n x y v => by simp only [eval_two_smul, h.2, smul_add]⟩

def biOp (A B : Q k d 1) (hA : ∀ (n) (u v : Q k d n), ac A (u + v) = ac A u + ac A v)
    (hB : ∀ (n) (u v : Q k d n), ac B (u + v) = ac B u + ac B v) : Module.End ℚ (Bi k d) where
  toFun f := ⟨E2 f.1 (ac A (gen 0)) (ac B (gen 1)), fun n x y v => by simp [eval_two_eval_two, hA, f.2.1],
    fun n x y v => by simp [eval_two_eval_two, hB, f.2.2]⟩
  map_add' _ _ := Subtype.ext (eval_two_add _ _ _ _)
  map_smul' _ _ := Subtype.ext (eval_two_smul _ _ _ _)

theorem bilinearOp_eval_two (A B : Q k d 1) (hA) (hB) (f : Bi k d) (x v : Q k d n) :
    E2 (biOp A B hA hB f).1 x v = E2 f.1 (ac A x) (ac B v) := by
  show E2 (E2 f.1 (ac A (gen 0 : Q k d 2)) (ac B (gen 1 : Q k d 2))) x v = _
  rw [eval_two_eval_two, sq_ac, sq_ac, sq_gen, sq_gen]
  rfl

theorem bi_ext {f g : Bi k d} (h : E2 f.1 (gen 0 : Q k d 2) (gen 1) = E2 g.1 (gen 0) (gen 1)) : f = g :=
  Subtype.ext ((formalSeriesValueAtTwoPoints_genericPoints f.1).symm.trans (h.trans (formalSeriesValueAtTwoPoints_genericPoints g.1)))

omit [Algebra ℚ k] in
theorem ac_gen (u : Q k d n) : ac (gen 0) u = u := by
  show sq ![u] (gen 0) = u
  rw [sq_gen]; rfl

set_option maxHeartbeats 1000000 in
theorem gauge_add {O : Type} [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O]
    (A : O → Q k d 1) (hA : ∀ a (n) (u v : Q k d n), ac (A a) (u + v) = ac (A a) u + ac (A a) v)
    (aadd : ∀ a b {n} (u : Q k d n), ac (A (a + b)) u = ac (A a) u + ac (A b) u)
    (amul : ∀ a b {n} (u : Q k d n), ac (A (a * b)) u = ac (A a) (ac (A b) u)) (aone : ∀ {n} (u : Q k d n), ac (A 1) u = u)
    (p q : PS k 3 d) (s : PS k 2 d) (ad : O → PS k 2 d)
    (p0 : ∀ {n} (y w : Q k d n), E3 p 0 y w = 0) (p2 : ∀ {n} (x y : Q k d n), E3 p x y 0 = 0)
    (q1 : ∀ {n} (x w : Q k d n), E3 q x 0 w = 0)
    (ps : ∀ {n} (x y w : Q k d n), E3 p x y w = E3 p y x w) (qs : ∀ {n} (x y w : Q k d n), E3 q x y w = E3 q x w y)
    (pc : ∀ {n} (x y t w : Q k d n), E3 p x y w + E3 p (x + y) t w = E3 p y t w + E3 p x (y + t) w)
    (qc : ∀ {n} (x y t w : Q k d n), E3 q x y t + E3 q x (y + t) w = E3 q x t w + E3 q x y (t + w))
    (int : ∀ {n} (x y v w : Q k d n), E3 p x y v + E3 p x y w + E3 q (x + y) v w = E3 q x v w + E3 q y v w + E3 p x y (v + w))
    (si : ∀ {n} (x v : Q k d n), E2 s x v + E2 s v x = 0)
    (sl : ∀ {n} (x v w : Q k d n), E3 q x v w + E2 s x v + E2 s x w = E2 s x (v + w) + E3 p v w x)
    (a1 : ∀ a {n} (x y v : Q k d n), E3 p (ac (A a) x) (ac (A a) y) v + E2 (ad a) (x + y) v =
      E2 (ad a) x v + E2 (ad a) y v + E3 p x y (ac (A (star a)) v))
    (a2 : ∀ a {n} (x v w : Q k d n), E3 q (ac (A a) x) v w + E2 (ad a) x (v + w) =
      E2 (ad a) x v + E2 (ad a) x w + E3 q x (ac (A (star a)) v) (ac (A (star a)) w))
    (am : ∀ a b {n} (x v : Q k d n), E2 (ad (a * b)) x v = E2 (ad a) (ac (A b) x) v + E2 (ad b) x (ac (A (star a)) v))
    (aa : ∀ a b {n} (x v : Q k d n), E3 p (ac (A a) x) (ac (A b) x) v + E2 (ad (a + b)) x v =
      E2 (ad a) x v + E2 (ad b) x v + E3 q x (ac (A (star a)) v) (ac (A (star b)) v))
    (as : ∀ a {n} (x v : Q k d n), E2 (ad a) x v + E2 (ad (star a)) v x + E2 s (ac (A a) x) v = E2 s x (ac (A (star a)) v)) :
    ∃ H : PS k 2 d, (∀ {n} (w : Q k d n), E2 H 0 w = 0) ∧ (∀ {n} (x : Q k d n), E2 H x 0 = 0) ∧
      (∀ {n} (x y w : Q k d n), E3 p x y w = E2 H x w + E2 H y w - E2 H (x + y) w) ∧
      (∀ {n} (x v w : Q k d n), E3 q x v w = E2 H x v + E2 H x w - E2 H x (v + w)) ∧
      (∀ {n} (x v : Q k d n), E2 s x v = E2 H v x - E2 H x v) ∧
      ∀ a {n} (x v : Q k d n), E2 (ad a) x v = E2 H (ac (A a) x) v - E2 H x (ac (A (star a)) v) := by
  obtain ⟨H₀, h₀, z₀, -⟩ := split p p0 ps pc
  let H₁ : PS k 2 d := H₀ - E2 H₀ (gen 0) 0
  have e₁ : ∀ {n} (x w : Q k d n), E2 H₁ x w = E2 H₀ x w - E2 H₀ x 0 := fun x w => by simp [H₁, eval_two_sub, eval_two_eval_two]
  have h₁ : ∀ {n} (x y w : Q k d n), E3 p x y w = E2 H₁ x w + E2 H₁ y w - E2 H₁ (x + y) w := fun x y w => by
    have := h₀ x y 0
    rw [p2] at this
    rw [e₁, e₁, e₁, h₀]; linear_combination -this
  have z₁ : ∀ {n} (x : Q k d n), E2 H₁ x 0 = 0 := fun x => by rw [e₁, sub_self]
  let b : PS k 3 d := E3 q (gen 2) (gen 0) (gen 1) -
    (E2 H₁ (gen 2) (gen 0) + E2 H₁ (gen 2) (gen 1) - E2 H₁ (gen 2) (gen 0 + gen 1))
  have eb : ∀ {n} (v w x : Q k d n), E3 b v w x = E3 q x v w - (E2 H₁ x v + E2 H₁ x w - E2 H₁ x (v + w)) := fun v w x => by
    show sb _ _ = _
    simp only [b, map_sub, map_add, formalPointSubstitutionSeries_valueAtThreePoints, formalPointSubstitutionSeries_valueAtTwoPoints, sq_gen]; rfl
  obtain ⟨H₂, h₂, z₂, n₂⟩ := split b (fun y w => by rw [eb, q1, z₁, zero_add, zero_add]; ring)
    (fun x y w => by rw [eb, eb, qs, add_comm x y]; ring)
    (fun x y t w => by rw [eb, eb, eb, eb, add_assoc x]; linear_combination qc w x y t)
  let D : PS k 3 d := E2 H₂ (gen 2) (gen 0) + E2 H₂ (gen 2) (gen 1) - E2 H₂ (gen 2) (gen 0 + gen 1)
  have eD : ∀ {n} (x y v : Q k d n), E3 D x y v = E2 H₂ v x + E2 H₂ v y - E2 H₂ v (x + y) := fun x y v => by
    show sb _ _ = _
    simp only [D, map_sub, map_add, formalPointSubstitutionSeries_valueAtTwoPoints, sq_gen]; rfl
  have D0 : D = 0 := zero_of_add D (fun x y v w => by
      have c₁ := h₂ v w x; have c₂ := h₂ v w y; have c₃ := h₂ v w (x + y)
      rw [eb] at c₁ c₂ c₃
      rw [eD, eD, eD]
      linear_combination c₁ + c₂ - c₃ + int x y v w - h₁ x y v - h₁ x y w + h₁ x y (v + w)) fun c x y => by
    have d₀ := dir_ne (k := k) (d := d) (show (0 : Fin 3) ≠ 2 by decide)
    have d₁ := dir_ne (k := k) (d := d) (show (1 : Fin 3) ≠ 2 by decide)
    rw [map_sub, map_add, pderiv_eval_two (dir_same 2) d₀, pderiv_eval_two (dir_same 2) d₁, pderiv_eval_two (dir_same 2) (d₀.add d₁)]
    simp [E3, n₂]
  have ad₂ : ∀ {n} (x y v : Q k d n), E2 H₂ v (x + y) = E2 H₂ v x + E2 H₂ v y := fun x y v => by
    have := eD x y v
    rw [D0, E3, map_zero] at this
    linear_combination this
  let H₃ : PS k 2 d := H₁ + E2 H₂ (gen 1) (gen 0)
  have e₃ : ∀ {n} (x w : Q k d n), E2 H₃ x w = E2 H₁ x w + E2 H₂ w x := fun x w => by simp [H₃, eval_two_add, eval_two_eval_two]
  have g₁ : ∀ {n} (x y w : Q k d n), E3 p x y w = E2 H₃ x w + E2 H₃ y w - E2 H₃ (x + y) w := fun x y w => by
    rw [e₃, e₃, e₃, h₁, ad₂]; ring
  have g₂ : ∀ {n} (x v w : Q k d n), E3 q x v w = E2 H₃ x v + E2 H₃ x w - E2 H₃ x (v + w) := fun x v w => by
    have := h₂ v w x
    rw [eb] at this
    rw [e₃, e₃, e₃]; linear_combination this
  let s' : PS k 2 d := s - (E2 H₃ (gen 1) (gen 0) - H₃)
  have es : ∀ {n} (x v : Q k d n), E2 s' x v = E2 s x v - (E2 H₃ v x - E2 H₃ x v) := fun x v => by simp [s', eval_two_sub, eval_two_eval_two]
  have s₂ : ∀ {n} (x v w : Q k d n), E2 s' x (v + w) = E2 s' x v + E2 s' x w := fun x v w => by
    rw [es, es, es]; linear_combination g₂ x v w - g₁ v w x - sl x v w
  have sa : ∀ {n} (x v : Q k d n), E2 s' x v = -E2 s' v x := fun x v => by rw [es, es]; linear_combination si x v
  have s₁ : ∀ {n} (x y v : Q k d n), E2 s' (x + y) v = E2 s' x v + E2 s' y v := fun x y v => by
    rw [sa, s₂, sa x, sa y]; ring
  let H₄ : PS k 2 d := H₃ - (1 / 2 : ℚ) • s'
  have e₄ : ∀ {n} (x w : Q k d n), E2 H₄ x w = E2 H₃ x w - (1 / 2 : ℚ) • E2 s' x w := fun x w => by
    rw [eval_two_sub, eval_two_smul]
  have f₁ : ∀ {n} (x y w : Q k d n), E3 p x y w = E2 H₄ x w + E2 H₄ y w - E2 H₄ (x + y) w := fun x y w => by
    rw [e₄, e₄, e₄, g₁, s₁]; module
  have f₂ : ∀ {n} (x v w : Q k d n), E3 q x v w = E2 H₄ x v + E2 H₄ x w - E2 H₄ x (v + w) := fun x v w => by
    rw [e₄, e₄, e₄, g₂, s₂]; module
  have f₃ : ∀ {n} (x v : Q k d n), E2 s x v = E2 H₄ v x - E2 H₄ x v := fun x v => by
    rw [e₄, e₄, sa v x, eq_add_of_sub_eq (es x v).symm]; module
  let dd : O → PS k 2 d := fun a => ad a - (E2 H₄ (ac (A a) (gen 0)) (gen 1) - E2 H₄ (gen 0) (ac (A (star a)) (gen 1)))
  have ed : ∀ a {n} (x v : Q k d n), E2 (dd a) x v = E2 (ad a) x v - (E2 H₄ (ac (A a) x) v - E2 H₄ x (ac (A (star a)) v)) :=
    fun a n x v => by simp [dd, eval_two_sub, eval_two_eval_two]
  have hdd : ∀ a, dd a ∈ Bi k d := fun a => ⟨fun n x y v => by
      rw [ed, ed, ed, hA]; linear_combination a1 a x y v - f₁ (ac (A a) x) (ac (A a) y) v + f₁ x y (ac (A (star a)) v),
    fun n x v w => by
      rw [ed, ed, ed, hA]
      linear_combination a2 a x v w - f₂ (ac (A a) x) v w + f₂ x (ac (A (star a)) v) (ac (A (star a)) w)⟩
  have h1 : ∀ (n) (u v : Q k d n), ac (gen 0) (u + v) = ac (gen 0) u + ac (gen 0) v := fun n u v => by simp only [ac_gen]
  have ext := @bi_ext k _ d _
  let Lh : O →+* Module.End ℚ (Bi k d) := RingHom.mk' ⟨⟨fun a => biOp (gen 0) (A (star a)) h1 (hA _),
      LinearMap.ext fun f => ext (by rw [bilinearOp_eval_two, ac_gen, star_one, aone]; rfl)⟩,
      fun a b => LinearMap.ext fun f => ext (by
        rw [Module.End.mul_apply, bilinearOp_eval_two, bilinearOp_eval_two, bilinearOp_eval_two, ac_gen, ac_gen, star_mul, amul])⟩
    fun a b => LinearMap.ext fun f => ext (by
      show E2 (biOp _ _ h1 (hA _) f).1 _ _ = E2 ((biOp _ _ h1 (hA _) f).1 + (biOp _ _ h1 (hA _) f).1) _ _
      rw [eval_two_add, bilinearOp_eval_two, bilinearOp_eval_two, bilinearOp_eval_two, star_add, aadd, f.2.2])
  let Rh : O →+* Module.End ℚ (Bi k d) := RingHom.mk' ⟨⟨fun a => biOp (A a) (gen 0) (hA _) h1,
      LinearMap.ext fun f => ext (by rw [bilinearOp_eval_two, ac_gen, aone]; rfl)⟩,
      fun a b => LinearMap.ext fun f => ext (by
        rw [Module.End.mul_apply, bilinearOp_eval_two, bilinearOp_eval_two, bilinearOp_eval_two, ac_gen, ac_gen, mul_comm, amul])⟩
    fun a b => LinearMap.ext fun f => ext (by
      show E2 (biOp _ _ (hA _) h1 f).1 _ _ = E2 ((biOp _ _ (hA _) h1 f).1 + (biOp _ _ (hA _) h1 f).1) _ _
      rw [eval_two_add, bilinearOp_eval_two, bilinearOp_eval_two, bilinearOp_eval_two, aadd, f.2.1])
  have eL : ∀ a (f : Bi k d) {n} (x v : Q k d n), E2 (Lh a f).1 x v = E2 f.1 x (ac (A (star a)) v) := fun a f n x v =>
    (bilinearOp_eval_two _ _ h1 (hA _) f x v).trans (by rw [ac_gen])
  have eR : ∀ a (f : Bi k d) {n} (x v : Q k d n), E2 (Rh a f).1 x v = E2 f.1 (ac (A a) x) v := fun a f n x v =>
    (bilinearOp_eval_two _ _ (hA _) h1 f x v).trans (by rw [ac_gen])
  obtain ⟨β, hβ⟩ := inner_of_derivation Lh Rh (fun a b => LinearMap.ext fun f => ext (by
      simp only [Module.End.mul_apply, eL, eR])) (AddMonoidHom.mk' (fun a => ⟨dd a, hdd a⟩) fun a b => ext (by
      show E2 (dd (a + b)) _ _ = E2 (dd a + dd b) _ _
      rw [eval_two_add, ed, ed, ed, star_add, aadd, aadd]
      linear_combination aa a b (gen 0 : Q k d 2) (gen 1) - f₁ (ac (A a) (gen 0 : Q k d 2)) (ac (A b) (gen 0)) (gen 1) +
        f₂ (gen 0 : Q k d 2) (ac (A (star a)) (gen 1)) (ac (A (star b)) (gen 1)))) fun a b => ext (by
      show E2 (dd (a * b)) _ _ = E2 ((Rh b ⟨dd a, hdd a⟩).1 + (Lh a ⟨dd b, hdd b⟩).1) _ _
      rw [eval_two_add, eR, eL, ed, ed, ed, am, star_mul, amul, amul]; ring)
  have hβ' : ∀ a {n} (x v : Q k d n), E2 (dd a) x v = E2 β.1 (ac (A a) x) v - E2 β.1 x (ac (A (star a)) v) :=
    fun a n x v => by rw [← eR, ← eL, ← eval_two_sub]; exact congrArg (fun f : Bi k d => E2 f.1 x v) (hβ a)
  let H : PS k 2 d := H₄ + (1 / 2 : ℚ) • (β.1 + E2 β.1 (gen 1) (gen 0))
  have e : ∀ {n} (x w : Q k d n), E2 H x w = E2 H₄ x w + (1 / 2 : ℚ) • (E2 β.1 x w + E2 β.1 w x) := fun x w => by
    simp only [H, eval_two_add, eval_two_smul, eval_two_eval_two, sq_gen]; rfl
  have r₁ : ∀ {n} (x y w : Q k d n), E3 p x y w = E2 H x w + E2 H y w - E2 H (x + y) w := fun x y w => by
    rw [e, e, e, f₁, β.2.1, β.2.2]; module
  have r₂ : ∀ {n} (x v w : Q k d n), E3 q x v w = E2 H x v + E2 H x w - E2 H x (v + w) := fun x v w => by
    rw [e, e, e, f₂, β.2.1, β.2.2]; module
  refine ⟨H, fun w => ?_, fun x => ?_, r₁, r₂, fun x v => by rw [e, e, f₃]; module, fun a n x v => ?_⟩
  · have := r₁ 0 0 w
    rw [p0, add_zero] at this; linear_combination -this
  · have := r₂ x 0 0
    rw [q1, add_zero] at this; linear_combination -this
  · have c₁ := hβ' a x v
    have c₂ := hβ' (star a) v x
    have c₃ := as a x v
    rw [ed] at c₁ c₂
    rw [star_star] at c₂
    rw [f₃, f₃] at c₃
    rw [e, e]
    linear_combination (norm := module) (1 / 2 : ℚ) • c₁ - (1 / 2 : ℚ) • c₂ + (1 / 2 : ℚ) • c₃

section Transfer

omit [Algebra ℚ k]

theorem formalSeriesValueAtTwoPoints_eq_ev (f : PS k 2 d) (u v : Q k d n) : E2 f u v = ev ![u.1, v.1] f := by
  show sb ![u, v] f = _
  rw [sb_apply]
  congr 1
  funext j; fin_cases j <;> rfl

theorem formalSeriesValueAtThreePoints_eq_ev (f : PS k 3 d) (u v w : Q k d n) : E3 f u v w = ev ![u.1, v.1, w.1] f := by
  show sb ![u, v, w] f = _
  rw [sb_apply]
  congr 1
  funext j; fin_cases j <;> rfl

theorem ac_val (A : Q k d 1) (u : Q k d n) : (ac A u).1 = comp1 A.1 u.1 := by
  funext i
  show sb ![u] (A.1 i) = ev ![u.1] (A.1 i)
  rw [sb_apply]
  congr 1
  funext j; fin_cases j; rfl

def op (F : Q k d 2) (u v : Q k d n) : Q k d n := sq ![u, v] F

theorem op_val (F : Q k d 2) (u v : Q k d n) : (op F u v).1 = addOf F.1 u.1 v.1 := by
  funext i
  show sb ![u, v] (F.1 i) = ev ![u.1, v.1] (F.1 i)
  rw [sb_apply]
  congr 1
  funext j; fin_cases j <;> rfl

theorem sq_op (b : Fin n → Q k d l) (F : Q k d 2) (u v : Q k d n) : sq b (op F u v) = op F (sq b u) (sq b v) := by
  show sq b (sq ![u, v] F) = sq ![sq b u, sq b v] F
  have h : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext j; fin_cases j <;> rfl
  rw [sq_sq_lemma, h]

theorem gen_val (j : Fin n) : (gen j : Q k d n).1 = pt k d j := rfl

variable {R : Type} [CommRing R] (φ : R →+* k)

def mq (p : Q R d n) : Q k d n := ⟨fun i => MvPowerSeries.map φ (p.1 i), fun i => by
  show constantCoeff (MvPowerSeries.map φ _) = 0
  rw [constantCoeff_map, p.2 i, map_zero]⟩

theorem map_sb {m : ℕ} (a : Fin m → Q R d n) (f : PS R m d) :
    MvPowerSeries.map φ (sb a f) = sb (fun j => mq φ (a j)) (MvPowerSeries.map φ f) := by
  rw [sb_apply, sb_apply]
  unfold ev
  rw [MvPowerSeries.map_subst (czQ a).hasSubst]
  rfl

theorem map_eval_two (f : PS R 2 d) (u v : Q R d n) :
    MvPowerSeries.map φ (E2 f u v) = E2 (MvPowerSeries.map φ f) (mq φ u) (mq φ v) := by
  unfold E2
  have h : (fun j => mq φ (![u, v] j)) = ![mq φ u, mq φ v] := by
    funext j; fin_cases j <;> rfl
  rw [map_sb, h]

theorem map_eval_three (f : PS R 3 d) (u v w : Q R d n) :
    MvPowerSeries.map φ (E3 f u v w) = E3 (MvPowerSeries.map φ f) (mq φ u) (mq φ v) (mq φ w) := by
  unfold E3
  have h : (fun j => mq φ (![u, v, w] j)) = ![mq φ u, mq φ v, mq φ w] := by
    funext j; fin_cases j <;> rfl
  rw [map_sb, h]

theorem mq_gen (j : Fin n) : mq φ (gen j : Q R d n) = gen j := by
  apply Subtype.ext; funext i
  show MvPowerSeries.map φ (pt R d j i) = pt k d j i
  unfold pt
  simp

theorem mq_zero : mq φ (0 : Q R d n) = 0 := by
  apply Subtype.ext; funext i
  exact map_zero (MvPowerSeries.map φ)

theorem mq_op (F : Q R d 2) (u v : Q R d n) : mq φ (op F u v) = op (mq φ F) (mq φ u) (mq φ v) := by
  apply Subtype.ext; funext i
  show MvPowerSeries.map φ (sb ![u, v] (F.1 i)) = sb ![mq φ u, mq φ v] (MvPowerSeries.map φ (F.1 i))
  have h : (fun j => mq φ (![u, v] j)) = ![mq φ u, mq φ v] := by
    funext j; fin_cases j <;> rfl
  rw [map_sb, h]

theorem mq_ac (A : Q R d 1) (u : Q R d n) : mq φ (ac A u) = ac (mq φ A) (mq φ u) := by
  apply Subtype.ext; funext i
  show MvPowerSeries.map φ (sb ![u] (A.1 i)) = sb ![mq φ u] (MvPowerSeries.map φ (A.1 i))
  have h : (fun j => mq φ (![u] j)) = ![mq φ u] := by
    funext j; fin_cases j; rfl
  rw [map_sb, h]

end Transfer

theorem sum_eq_of_exp (a b : List (PS k n d)) (ha : ∀ x ∈ a, constantCoeff x = 0) (hb : ∀ x ∈ b, constantCoeff x = 0)
    (h : (a.map (FB.expS k)).prod = (b.map (FB.expS k)).prod) : a.sum = b.sum := by
  have key : ∀ a : List (PS k n d), (∀ x ∈ a, constantCoeff x = 0) →
      constantCoeff a.sum = 0 ∧ FB.expS k a.sum = (a.map (FB.expS k)).prod := fun a ha => by
    induction a with
    | nil => exact ⟨map_zero _, WickVanishing.exp_zero⟩
    | cons x a ih =>
      obtain ⟨c, e⟩ := ih fun y hy => ha y (List.mem_cons_of_mem _ hy)
      have hx := ha x List.mem_cons_self
      exact ⟨by rw [List.sum_cons, map_add, hx, c, add_zero], by
        rw [List.sum_cons, WickVanishing.gt_expS_add _ _ hx c, e]; rfl⟩
  exact WickVanishing.exp_inj (key a ha).1 (key b hb).1 ((key a ha).2.trans (h.trans (key b hb).2.symm))

theorem exists_lg {m : ℕ} (f : PS k m d) (hf : constantCoeff f = 1) : ∃ g : PS k m d, FB.expS k g = f ∧
    ∀ {n} (a : Fin m → Q k d n), constantCoeff (sb a g) = 0 ∧ FB.expS k (sb a g) = sb a f :=
  ⟨_, WickVanishing.exp_log hf, fun a => ⟨by rw [sb_apply]; exact constantCoeff_ev (czQ a) (WickVanishing.constantCoeff_logS hf), by
    rw [sb_apply, sb_apply, ← WickVanishing.gt_ev_expS _ (fun j => (a j).2) _ (WickVanishing.constantCoeff_logS hf)]
    exact congrArg _ (WickVanishing.exp_log hf)⟩⟩

set_option maxHeartbeats 2000000 in
theorem canonGauge : CanonGaugeSt := by
  intro R _ d O _ _ _ _ _ k _ _ _ B
  let φ := algebraMap R k
  let F₀ : Q R d 2 := ⟨B.G.F, B.G.const⟩
  let A₀ : O → Q R d 1 := fun a => ⟨B.A.act a, B.A.const a⟩
  let F := mq φ F₀
  let A : O → Q k d 1 := fun a => mq φ (A₀ a)
  obtain ⟨l₀, l0, l1, ladd⟩ := logSt k d (WickVanishing.Nab.lawK k B)
  obtain ⟨e₀, ⟨e0, -, el, le⟩, -⟩ := WickVanishing.formal_exp_law k d (WickVanishing.Nab.lawK k B) l₀ l0 l1 ladd
  let lg : Q k d 1 := ⟨l₀, l0⟩
  let ex : Q k d 1 := ⟨e₀, e0⟩
  have acac : ∀ (S T : Q k d 1) {n} (u : Q k d n), ac S (ac T u) = ac (ac S T) u := fun S T n u => by
    rw [ac.eq_def (ac S T), sq_ac]; rfl
  have hel : ∀ {n} (u : Q k d n), ac ex (ac lg u) = u := fun u => by
    rw [acac, show ac ex lg = gen 0 from Subtype.ext ((ac_val _ _).trans el), ac_gen]
  have hle : ∀ {n} (u : Q k d n), ac lg (ac ex u) = u := fun u => by
    rw [acac, show ac lg ex = gen 0 from Subtype.ext ((ac_val _ _).trans le), ac_gen]
  have hl : ∀ {n} (u v : Q k d n), ac lg (op F u v) = ac lg u + ac lg v := fun u v => Subtype.ext (by
    rw [ac_val, op_val]
    exact (WickVanishing.add_at (WickVanishing.Nab.lawK k B) l₀ ladd u.1 v.1 u.2 v.2).trans (congrArg₂ (· + ·) (ac_val lg u).symm (ac_val lg v).symm))
  have he : ∀ {n} (u v : Q k d n), ac ex (u + v) = op F (ac ex u) (ac ex v) := fun u v => by
    rw [← hel (op F _ _), hl, hle, hle]
  have l00 : ∀ {n} (S : Q k d 1), ac S (0 : Q k d n) = 0 := fun {n} S => Subtype.ext (funext fun i => by
    have e := ev_zeroFam (n := n) (S.1 i)
    rw [S.2 i, map_zero] at e
    exact ((sb_apply _ _).trans (congrArg (ev · (S.1 i)) (funext fun j => by fin_cases j; rfl))).trans e)
  have tr : ∀ {n l} (b : Fin n → Q k d l) {x y : PS R n d}, x = y → sb b (MvPowerSeries.map φ x) = sb b (MvPowerSeries.map φ y) :=
    fun b _ _ h => by rw [h]
  have trq : ∀ {n l} (b : Fin n → Q k d l) {x y : Q R d n}, x = y → sq b (mq φ x) = sq b (mq φ y) := fun b _ _ h => by rw [h]
  have cc : ∀ {m} (f : PS R m d) (a : Fin m → Q R d (m - 1)), sb a f = 1 → constantCoeff (MvPowerSeries.map φ f) = 1 :=
    fun f a h => by rw [constantCoeff_map, ← cc_ev (czQ a), ← sb_apply, h, map_one, map_one]
  have x₁ : E3 B.ph1 (0 : Q R d 2) (gen 0) (gen 1) = 1 := (formalSeriesValueAtThreePoints_eq_ev _ _ _ _).trans B.cocycleLeft_zero_fst
  have x₂ : E3 B.ph1 (gen 0 : Q R d 2) (gen 1) 0 = 1 := (formalSeriesValueAtThreePoints_eq_ev _ _ _ _).trans B.cocycleLeft_zero_thd
  have x₃ : E3 B.ph2 (gen 0 : Q R d 2) 0 (gen 1) = 1 := (formalSeriesValueAtThreePoints_eq_ev _ _ _ _).trans B.cocycleRight_zero_snd
  obtain ⟨p, hp, vp⟩ := exists_lg _ (cc B.ph1 _ x₁)
  obtain ⟨q, hq, vq⟩ := exists_lg _ (cc B.ph2 _ x₃)
  obtain ⟨s, hs, vs⟩ := exists_lg _ (cc B.sy ![0, gen 0] ((formalSeriesValueAtTwoPoints_eq_ev _ _ _).trans B.symmetry_zero_fst))
  choose ad had vad using fun a => exists_lg _ (cc (B.ad a) ![0, gen 0] ((formalSeriesValueAtTwoPoints_eq_ev _ _ _).trans (B.adjoint_zero_fst a)))
  have cp : ∀ {n} (u v w : Q k d n), constantCoeff (E3 p u v w) = 0 := fun u v w => (vp _).1
  have cq : ∀ {n} (u v w : Q k d n), constantCoeff (E3 q u v w) = 0 := fun u v w => (vq _).1
  have cs : ∀ {n} (u v : Q k d n), constantCoeff (E2 s u v) = 0 := fun u v => (vs _).1
  have ca : ∀ a {n} (u v : Q k d n), constantCoeff (E2 (ad a) u v) = 0 := fun a n u v => (vad a _).1
  have ep : ∀ {n} (u v w : Q k d n), FB.expS k (E3 p u v w) = E3 (MvPowerSeries.map φ B.ph1) u v w := fun u v w => (vp _).2
  have eq : ∀ {n} (u v w : Q k d n), FB.expS k (E3 q u v w) = E3 (MvPowerSeries.map φ B.ph2) u v w := fun u v w => (vq _).2
  have es : ∀ {n} (u v : Q k d n), FB.expS k (E2 s u v) = E2 (MvPowerSeries.map φ B.sy) u v := fun u v => (vs _).2
  have ea : ∀ a {n} (u v : Q k d n), FB.expS k (E2 (ad a) u v) = E2 (MvPowerSeries.map φ (B.ad a)) u v :=
    fun a n u v => (vad a _).2
  have ax : ∀ a {n} (u : Q k d n), ac ex (ac (ac lg (ac (A a) ex)) u) = ac (A a) (ac ex u) := fun a n u => by
    rw [← acac, hel, ← acac]
  have E3x : ∀ (f : PS k 3 d) {n} (u v w : Q k d n), E3 (E3 f (ac ex (gen 0)) (ac ex (gen 1)) (ac ex (gen 2))) u v w =
      E3 f (ac ex u) (ac ex v) (ac ex w) := fun f n u v w => by rw [E3, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_ac, sq_ac, sq_gen, sq_gen, sq_gen]; rfl
  have E2x : ∀ (f : PS k 2 d) (S : Q k d 1) {n} (u v : Q k d n), E2 (E2 f (ac S (gen 0)) (ac S (gen 1))) u v =
      E2 f (ac S u) (ac S v) := fun f S n u v => by rw [eval_two_eval_two, sq_ac, sq_ac, sq_gen, sq_gen]; rfl
  obtain ⟨H, z₀, z₁, r₁, r₂, r₃, r₄⟩ := gauge_add (fun a => ac lg (ac (A a) ex))
    (fun a n u v => by
      have h := trq ![ac ex u, ac ex v] (show ac (A₀ a) (op F₀ (gen 0) (gen 1)) = op F₀ (ac (A₀ a) (gen 0)) (ac (A₀ a) (gen 1))
        from Subtype.ext (by simpa only [ac_val, op_val, gen_val] using B.A.hom a))
      simp only [mq_ac, mq_op, mq_gen, sq_ac, sq_op, sq_gen] at h
      simp only [← acac]
      rw [he, ← hl]; exact congrArg _ h)
    (fun a b n u => by
      have h := trq ![ac ex u] (show A₀ (a + b) = op F₀ (A₀ a) (A₀ b) from Subtype.ext ((B.A.add_act a b).trans (op_val F₀ (A₀ a) (A₀ b)).symm))
      simp only [mq_op, sq_op] at h
      simp only [← acac]
      rw [← hl]; exact congrArg _ h)
    (fun a b n u => by
      have h := trq ![ac ex u] (show A₀ (a * b) = ac (A₀ a) (A₀ b) from Subtype.ext ((B.A.mul_act a b).trans (ac_val (A₀ a) (A₀ b)).symm))
      simp only [mq_ac, sq_ac] at h
      simp only [← acac]
      rw [hel]; exact congrArg _ h)
    (fun u => by
      have h : A 1 = gen 0 := (congrArg (mq φ) (show A₀ 1 = gen 0 from Subtype.ext B.A.one_act)).trans (mq_gen φ 0)
      rw [h, ac_gen, ← acac, hle])
    (E3 p (ac ex (gen 0)) (ac ex (gen 1)) (ac ex (gen 2))) (E3 q (ac ex (gen 0)) (ac ex (gen 1)) (ac ex (gen 2)))
    (E2 s (ac ex (gen 0)) (ac ex (gen 1))) (fun a => E2 (ad a) (ac ex (gen 0)) (ac ex (gen 1)))
    (fun y w => by
      have h := tr ![ac ex y, ac ex w] (show E3 B.ph1 (0 : Q R d 2) (gen 0) (gen 1) = 1 from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val, ZeroMemClass.coe_zero] using B.cocycleLeft_zero_fst)
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 p 0 (ac ex y) (ac ex w)] [] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun x y => by
      have h := tr ![ac ex x, ac ex y] (show E3 B.ph1 (gen 0 : Q R d 2) (gen 1) 0 = 1 from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val, ZeroMemClass.coe_zero] using B.cocycleLeft_zero_thd)
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 p (ac ex x) (ac ex y) 0] [] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun x w => by
      have h := tr ![ac ex x, ac ex w] (show E3 B.ph2 (gen 0 : Q R d 2) 0 (gen 1) = 1 from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val, ZeroMemClass.coe_zero] using B.cocycleRight_zero_snd)
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 q (ac ex x) 0 (ac ex w)] [] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun x y w => by
      have h := tr ![ac ex x, ac ex y, ac ex w] (show E3 B.ph1 (gen 0 : Q R d 3) (gen 1) (gen 2) = E3 B.ph1 (gen 1) (gen 0) (gen 2) from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val] using ((formalSeriesValueAtThreePoints_eq_ev B.ph1 (gen 0) (gen 1) (gen 2)).symm.trans ((formalSeriesValueAtThreePoints_genericPoints _).trans B.cocycleLeft_comm.symm)))
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 p (ac ex x) (ac ex y) (ac ex w)] [E3 p (ac ex y) (ac ex x) (ac ex w)] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun x y w => by
      have h := tr ![ac ex x, ac ex y, ac ex w] (show E3 B.ph2 (gen 0 : Q R d 3) (gen 1) (gen 2) = E3 B.ph2 (gen 0) (gen 2) (gen 1) from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val] using ((formalSeriesValueAtThreePoints_eq_ev B.ph2 (gen 0) (gen 1) (gen 2)).symm.trans ((formalSeriesValueAtThreePoints_genericPoints _).trans B.cocycleRight_comm.symm)))
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 q (ac ex x) (ac ex y) (ac ex w)] [E3 q (ac ex x) (ac ex w) (ac ex y)] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun x y t w => by
      have h := tr ![ac ex x, ac ex y, ac ex t, ac ex w] (show E3 B.ph1 (gen 0 : Q R d 4) (gen 1) (gen 3) * E3 B.ph1 (op F₀ (gen 0) (gen 1)) (gen 2) (gen 3) = E3 B.ph1 (gen 1) (gen 2) (gen 3) * E3 B.ph1 (gen 0) (op F₀ (gen 1) (gen 2)) (gen 3) from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val, ZeroMemClass.coe_zero] using B.cocycleLeft_assoc)
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 p (ac ex x) (ac ex y) (ac ex w), E3 p (op F (ac ex x) (ac ex y)) (ac ex t) (ac ex w)] [E3 p (ac ex y) (ac ex t) (ac ex w), E3 p (ac ex x) (op F (ac ex y) (ac ex t)) (ac ex w)] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun x y t w => by
      have h := tr ![ac ex x, ac ex y, ac ex t, ac ex w] (show E3 B.ph2 (gen 0 : Q R d 4) (gen 1) (gen 2) * E3 B.ph2 (gen 0) (op F₀ (gen 1) (gen 2)) (gen 3) = E3 B.ph2 (gen 0) (gen 2) (gen 3) * E3 B.ph2 (gen 0) (gen 1) (op F₀ (gen 2) (gen 3)) from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val, ZeroMemClass.coe_zero] using B.cocycleRight_assoc)
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 q (ac ex x) (ac ex y) (ac ex t), E3 q (ac ex x) (op F (ac ex y) (ac ex t)) (ac ex w)] [E3 q (ac ex x) (ac ex t) (ac ex w), E3 q (ac ex x) (ac ex y) (op F (ac ex t) (ac ex w))] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun x y v w => by
      have h := tr ![ac ex x, ac ex y, ac ex v, ac ex w] (show E3 B.ph1 (gen 0 : Q R d 4) (gen 1) (gen 2) * E3 B.ph1 (gen 0) (gen 1) (gen 3) * E3 B.ph2 (op F₀ (gen 0) (gen 1)) (gen 2) (gen 3) = E3 B.ph2 (gen 0) (gen 2) (gen 3) * E3 B.ph2 (gen 1) (gen 2) (gen 3) * E3 B.ph1 (gen 0) (gen 1) (op F₀ (gen 2) (gen 3)) from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val] using B.interchange)
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 p (ac ex x) (ac ex y) (ac ex v), E3 p (ac ex x) (ac ex y) (ac ex w), E3 q (op F (ac ex x) (ac ex y)) (ac ex v) (ac ex w)] [E3 q (ac ex x) (ac ex v) (ac ex w), E3 q (ac ex y) (ac ex v) (ac ex w), E3 p (ac ex x) (ac ex y) (op F (ac ex v) (ac ex w))] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun x v => by
      have h := tr ![ac ex x, ac ex v] (show E2 B.sy (gen 0 : Q R d 2) (gen 1) * E2 B.sy (gen 1) (gen 0) = 1 from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val] using ((congrArg₂ (· * ·) (formalSeriesValueAtTwoPoints_genericPoints B.sy) rfl).trans B.sy_inv))
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E2 s (ac ex x) (ac ex v), E2 s (ac ex v) (ac ex x)] [] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun x v w => by
      have h := tr ![ac ex x, ac ex v, ac ex w] (show E3 B.ph2 (gen 0 : Q R d 3) (gen 1) (gen 2) * E2 B.sy (gen 0) (gen 1) * E2 B.sy (gen 0) (gen 2) = E2 B.sy (gen 0) (op F₀ (gen 1) (gen 2)) * E3 B.ph1 (gen 1) (gen 2) (gen 0) from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val] using ((congrArg (· * _ * _) (formalSeriesValueAtThreePoints_genericPoints B.ph2)).trans B.sy_law))
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 q (ac ex x) (ac ex v) (ac ex w), E2 s (ac ex x) (ac ex v), E2 s (ac ex x) (ac ex w)] [E2 s (ac ex x) (op F (ac ex v) (ac ex w)), E3 p (ac ex v) (ac ex w) (ac ex x)] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun a n x y v => by
      have h := tr ![ac ex x, ac ex y, ac ex v] (show E3 B.ph1 (ac (A₀ a) (gen 0 : Q R d 3)) (ac (A₀ a) (gen 1)) (gen 2) * E2 (B.ad a) (op F₀ (gen 0) (gen 1)) (gen 2) = E2 (B.ad a) (gen 0) (gen 2) * E2 (B.ad a) (gen 1) (gen 2) * E3 B.ph1 (gen 0) (gen 1) (ac (A₀ (star a)) (gen 2)) from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val] using B.adjoint_compat_left a)
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 p (ac (A a) (ac ex x)) (ac (A a) (ac ex y)) (ac ex v), E2 (ad a) (op F (ac ex x) (ac ex y)) (ac ex v)] [E2 (ad a) (ac ex x) (ac ex v), E2 (ad a) (ac ex y) (ac ex v), E3 p (ac ex x) (ac ex y) (ac (A (star a)) (ac ex v))] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun a n x v w => by
      have h := tr ![ac ex x, ac ex v, ac ex w] (show E3 B.ph2 (ac (A₀ a) (gen 0 : Q R d 3)) (gen 1) (gen 2) * E2 (B.ad a) (gen 0) (op F₀ (gen 1) (gen 2)) = E2 (B.ad a) (gen 0) (gen 1) * E2 (B.ad a) (gen 0) (gen 2) * E3 B.ph2 (gen 0) (ac (A₀ (star a)) (gen 1)) (ac (A₀ (star a)) (gen 2)) from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val] using B.adjoint_compat_right a)
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 q (ac (A a) (ac ex x)) (ac ex v) (ac ex w), E2 (ad a) (ac ex x) (op F (ac ex v) (ac ex w))] [E2 (ad a) (ac ex x) (ac ex v), E2 (ad a) (ac ex x) (ac ex w), E3 q (ac ex x) (ac (A (star a)) (ac ex v)) (ac (A (star a)) (ac ex w))] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun a b n x v => by
      have h := tr ![ac ex x, ac ex v] (show E2 (B.ad (a * b)) (gen 0 : Q R d 2) (gen 1) = E2 (B.ad a) (ac (A₀ b) (gen 0)) (gen 1) * E2 (B.ad b) (gen 0) (ac (A₀ (star a)) (gen 1)) from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val] using ((formalSeriesValueAtTwoPoints_genericPoints (B.ad (a * b))).trans (B.ad_mul a b)))
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E2 (ad (a * b)) (ac ex x) (ac ex v)] [E2 (ad a) (ac (A b) (ac ex x)) (ac ex v), E2 (ad b) (ac ex x) (ac (A (star a)) (ac ex v))] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun a b n x v => by
      have h := tr ![ac ex x, ac ex v] (show E3 B.ph1 (ac (A₀ a) (gen 0 : Q R d 2)) (ac (A₀ b) (gen 0)) (gen 1) * E2 (B.ad (a + b)) (gen 0) (gen 1) = E2 (B.ad a) (gen 0) (gen 1) * E2 (B.ad b) (gen 0) (gen 1) * E3 B.ph2 (gen 0) (ac (A₀ (star a)) (gen 1)) (ac (A₀ (star b)) (gen 1)) from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val] using ((congrArg (_ * ·) (formalSeriesValueAtTwoPoints_genericPoints (B.ad (a + b)))).trans ((B.ad_add a b).trans (congrArg₂ (· * · * _) (formalSeriesValueAtTwoPoints_genericPoints (B.ad a)).symm (formalSeriesValueAtTwoPoints_genericPoints (B.ad b)).symm))))
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E3 p (ac (A a) (ac ex x)) (ac (A b) (ac ex x)) (ac ex v), E2 (ad (a + b)) (ac ex x) (ac ex v)] [E2 (ad a) (ac ex x) (ac ex v), E2 (ad b) (ac ex x) (ac ex v), E3 q (ac ex x) (ac (A (star a)) (ac ex v)) (ac (A (star b)) (ac ex v))] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
    (fun a n x v => by
      have h := tr ![ac ex x, ac ex v] (show E2 (B.ad a) (gen 0 : Q R d 2) (gen 1) * E2 (B.ad (star a)) (gen 1) (gen 0) * E2 B.sy (ac (A₀ a) (gen 0)) (gen 1) = E2 B.sy (gen 0) (ac (A₀ (star a)) (gen 1)) from by
        simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, ac_val, op_val, gen_val] using ((congrArg (· * _ * _) (formalSeriesValueAtTwoPoints_genericPoints (B.ad a))).trans (B.ad_sy a)))
      simp only [map_mul, map_one, map_eval_two, map_eval_three, mq_ac, mq_op, mq_gen, mq_zero, formalPointSubstitutionSeries_valueAtTwoPoints, formalPointSubstitutionSeries_valueAtThreePoints, sq_ac, sq_op, sq_gen, map_zero,
        Matrix.cons_val] at h
      have := sum_eq_of_exp [E2 (ad a) (ac ex x) (ac ex v), E2 (ad (star a)) (ac ex v) (ac ex x), E2 s (ac (A a) (ac ex x)) (ac ex v)] [E2 s (ac ex x) (ac (A (star a)) (ac ex v))] (by simp [cp, cq, cs, ca]) (by simp [cp, cq, cs, ca])
        (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ep, eq, es, ea, mul_assoc] using h)
      simpa only [E3x, E2x, he, ax, l00, List.sum_cons, List.sum_nil, add_zero, add_assoc] using this)
  obtain ⟨h, back⟩ : ∃ h : PS k 2 d, ∀ {n} (u v : Q k d n), E2 H (ac lg u) (ac lg v) = ev ![u.1, v.1] h :=
    ⟨E2 H (ac lg (gen 0)) (ac lg (gen 1)), fun u v => (E2x H lg u v).symm.trans (formalSeriesValueAtTwoPoints_eq_ev _ u v)⟩
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · exact (back 0 (gen 0)).symm.trans (by rw [l00, z₀])
  · exact (back (gen 0) 0).symm.trans (by rw [l00, z₁])
  · have := r₁ (ac lg (gen 0 : Q k d 3)) (ac lg (gen 1)) (ac lg (gen 2))
    rw [E3x, hel, hel, hel, formalSeriesValueAtThreePoints_genericPoints, ← hl, back, back, back, op_val] at this
    exact hp.symm.trans (congrArg _ this)
  · have := r₂ (ac lg (gen 0 : Q k d 3)) (ac lg (gen 1)) (ac lg (gen 2))
    rw [E3x, hel, hel, hel, formalSeriesValueAtThreePoints_genericPoints, ← hl, back, back, back, op_val] at this
    exact hq.symm.trans (congrArg _ this)
  · have := r₃ (ac lg (gen 0 : Q k d 2)) (ac lg (gen 1))
    rw [E2x, hel, hel, formalSeriesValueAtTwoPoints_genericPoints, back, back, ← formalSeriesValueAtTwoPoints_eq_ev h (gen 0) (gen 1), formalSeriesValueAtTwoPoints_genericPoints] at this
    exact hs.symm.trans (congrArg _ this)
  · have := r₄ a (ac lg (gen 0 : Q k d 2)) (ac lg (gen 1))
    have w : ∀ b (u : Q k d 2), ac (ac lg (ac (A b) ex)) (ac lg u) = ac lg (ac (A b) u) := fun b u => by
      rw [← acac, ← acac, hel]
    rw [E2x, hel, hel, formalSeriesValueAtTwoPoints_genericPoints, w, w, back, back, ac_val, ac_val] at this
    exact (had a).symm.trans (congrArg _ this)

end ReciprocityTheory.ChartRestriction.G.TB.Canon
