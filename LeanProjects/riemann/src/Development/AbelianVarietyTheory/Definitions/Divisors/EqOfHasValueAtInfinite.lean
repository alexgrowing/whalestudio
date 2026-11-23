import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization

open MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.LGrp

section Rational
open Polynomial

def HasValueAt (R : RatFunc ℂ) (x w : ℂ) : Prop :=
  R.denom.eval x ≠ 0 ∧ w = R.eval (RingHom.id ℂ) x

theorem HasValueAt.unique {R : RatFunc ℂ} {x w w' : ℂ} (h : HasValueAt R x w) (h' : HasValueAt R x w') : w = w' :=
  h.2.trans h'.2.symm

theorem hasValueAt_iff {R : RatFunc ℂ} {x w : ℂ} :
    HasValueAt R x w ↔ ∃ a b : ℂ[X], b.eval x ≠ 0 ∧ R = algebraMap _ _ a / algebraMap _ _ b ∧
      w * b.eval x = a.eval x := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨R.num, R.denom, h, (RatFunc.num_div_denom R).symm, ?_⟩
    simp only [RatFunc.eval, eval₂_id]
    exact div_mul_cancel₀ _ h
  · rintro ⟨a, b, hb, hR, hw⟩
    have hb0 : b ≠ 0 := fun e => hb (by simp [e])
    have hd : R.denom.eval x ≠ 0 := fun e => by
      obtain ⟨c, hc⟩ := (RatFunc.denom_dvd (x := R) hb0).2 ⟨a, hR⟩
      exact hb (by rw [hc, eval_mul, e, zero_mul])
    refine ⟨hd, ?_⟩
    have := congrArg (eval x) ((RatFunc.num_mul_eq_mul_denom_iff hb0).2 hR)
    simp only [eval_mul] at this
    simp only [RatFunc.eval, eval₂_id]
    rw [eq_div_iff hd]
    apply mul_right_cancel₀ hb
    rw [this, ← hw]; ring

theorem hasValueAt_algebraMap (p : ℂ[X]) (x : ℂ) : HasValueAt (algebraMap _ _ p) x (p.eval x) :=
  hasValueAt_iff.2 ⟨p, 1, by simp, by simp, by simp⟩

theorem hasValueAt_C (a x : ℂ) : HasValueAt (RatFunc.C a) x a := by
  simpa using hasValueAt_algebraMap (C a) x

theorem hasValueAt_one (x : ℂ) : HasValueAt 1 x 1 := by simpa using hasValueAt_C 1 x

theorem hasValueAt_X (x : ℂ) : HasValueAt RatFunc.X x x := by
  simpa using hasValueAt_algebraMap X x

theorem HasValueAt.add {R S : RatFunc ℂ} {x v w : ℂ} (h : HasValueAt R x v) (h' : HasValueAt S x w) :
    HasValueAt (R + S) x (v + w) := by
  obtain ⟨a, b, hb, rfl, e⟩ := hasValueAt_iff.1 h
  obtain ⟨c, d, hd, rfl, e'⟩ := hasValueAt_iff.1 h'
  have hb0 : algebraMap ℂ[X] (RatFunc ℂ) b ≠ 0 := RatFunc.algebraMap_ne_zero fun e => hb (by simp [e])
  have hd0 : algebraMap ℂ[X] (RatFunc ℂ) d ≠ 0 := RatFunc.algebraMap_ne_zero fun e => hd (by simp [e])
  refine hasValueAt_iff.2 ⟨a * d + b * c, b * d, by simp [hb, hd], ?_, ?_⟩
  · rw [div_add_div _ _ hb0 hd0]; simp
  · simp only [eval_mul, eval_add, ← e, ← e']; ring

theorem HasValueAt.mul {R S : RatFunc ℂ} {x v w : ℂ} (h : HasValueAt R x v) (h' : HasValueAt S x w) :
    HasValueAt (R * S) x (v * w) := by
  obtain ⟨a, b, hb, rfl, e⟩ := hasValueAt_iff.1 h
  obtain ⟨c, d, hd, rfl, e'⟩ := hasValueAt_iff.1 h'
  refine hasValueAt_iff.2 ⟨a * c, b * d, by simp [hb, hd], ?_, ?_⟩
  · rw [div_mul_div_comm]; simp
  · simp only [eval_mul, ← e, ← e']; ring

theorem HasValueAt.inv {R : RatFunc ℂ} {x v : ℂ} (h : HasValueAt R x v) (hv : v ≠ 0) : HasValueAt R⁻¹ x v⁻¹ := by
  obtain ⟨a, b, hb, rfl, e⟩ := hasValueAt_iff.1 h
  refine hasValueAt_iff.2 ⟨b, a, e ▸ mul_ne_zero hv hb, inv_div _ _, ?_⟩
  rw [← e, inv_mul_cancel_left₀ hv]

theorem HasValueAt.neg {R : RatFunc ℂ} {x v : ℂ} (h : HasValueAt R x v) : HasValueAt (-R) x (-v) := by
  simpa using (hasValueAt_C (-1) x).mul h

theorem HasValueAt.sub {R S : RatFunc ℂ} {x v w : ℂ} (h : HasValueAt R x v) (h' : HasValueAt S x w) :
    HasValueAt (R - S) x (v - w) := by
  simpa [sub_eq_add_neg] using h.add h'.neg

theorem HasValueAt.pow {R : RatFunc ℂ} {x v : ℂ} (h : HasValueAt R x v) (m : ℕ) : HasValueAt (R ^ m) x (v ^ m) := by
  induction m with
  | zero => simpa using hasValueAt_one x
  | succ m ih => simpa [pow_succ] using ih.mul h

theorem HasValueAt.zpow {R : RatFunc ℂ} {x v : ℂ} (h : HasValueAt R x v) (hv : v ≠ 0) (m : ℤ) :
    HasValueAt (R ^ m) x (v ^ m) := by
  cases m with
  | ofNat m => simpa using h.pow m
  | negSucc m => simpa using (h.pow (m + 1)).inv (pow_ne_zero _ hv)

theorem HasValueAt.multiset_prod {ι : Type} (S : Multiset ι) {R : ι → RatFunc ℂ} {x : ℂ} {v : ι → ℂ}
    (h : ∀ i ∈ S, HasValueAt (R i) x (v i)) : HasValueAt (S.map R).prod x (S.map v).prod := by
  induction S using Multiset.induction_on with
  | empty => simpa using hasValueAt_one x
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))

theorem eq_of_hasValueAt_infinite {R S : RatFunc ℂ} {T : Set ℂ} (hT : T.Infinite)
    (h : ∀ x ∈ T, ∃ w, HasValueAt R x w ∧ HasValueAt S x w) : R = S := by
  have : (R - S).num = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ (hT.mono fun x hx => ?_)
    obtain ⟨w, h1, h2⟩ := h x hx
    obtain ⟨h3, h4⟩ := h1.sub h2
    simp only [RatFunc.eval, eval₂_id, sub_self] at h4
    exact (div_eq_zero_iff.1 h4.symm).resolve_right h3
  exact sub_eq_zero.1 (RatFunc.num_eq_zero_iff.1 this)

def IsRatIn (q : ℕ) (F : ℂ → ℂ) (R : RatFunc ℂ) : Prop :=
  ∃ r : ℝ, ∀ z : ℂ, r < z.re → HasValueAt R ((q : ℂ) ^ (-z)) (F z)

theorem IsRatIn.unique {q : ℕ} (hq : 2 ≤ q) {F : ℂ → ℂ} {R S : RatFunc ℂ} (h : IsRatIn q F R) (h' : IsRatIn q F S) :
    R = S := by
  obtain ⟨r, h⟩ := h
  obtain ⟨s, h'⟩ := h'
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hinj : Function.Injective fun t : ℝ => (q : ℂ) ^ (-(t : ℂ)) := by
    intro a b e
    have := congrArg norm e
    simp only [Complex.norm_natCast_cpow_of_pos (show 0 < q by omega), Complex.neg_re, Complex.ofReal_re] at this
    exact neg_injective ((Real.strictMono_rpow_of_base_gt_one hq1).injective this)
  refine eq_of_hasValueAt_infinite ((Set.Ioi_infinite (max r s)).image hinj.injOn) ?_
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨F t, h t (by simpa using (max_lt_iff.1 ht).1), h' t (by simpa using (max_lt_iff.1 ht).2)⟩

theorem IsRatIn.mul {q : ℕ} {F G : ℂ → ℂ} {R S : RatFunc ℂ} (h : IsRatIn q F R) (h' : IsRatIn q G S) :
    IsRatIn q (fun z => F z * G z) (R * S) := by
  obtain ⟨r, h⟩ := h
  obtain ⟨s, h'⟩ := h'
  exact ⟨max r s, fun z hz => (h z (max_lt_iff.1 hz).1).mul (h' z (max_lt_iff.1 hz).2)⟩

theorem IsRatIn.add {q : ℕ} {F G : ℂ → ℂ} {R S : RatFunc ℂ} (h : IsRatIn q F R) (h' : IsRatIn q G S) :
    IsRatIn q (fun z => F z + G z) (R + S) := by
  obtain ⟨r, h⟩ := h
  obtain ⟨s, h'⟩ := h'
  exact ⟨max r s, fun z hz => (h z (max_lt_iff.1 hz).1).add (h' z (max_lt_iff.1 hz).2)⟩

def HasContValue (q : ℕ) (F : ℂ → ℂ) (z₀ w : ℂ) : Prop :=
  ∃ R : RatFunc ℂ, IsRatIn q F R ∧ HasValueAt R ((q : ℂ) ^ (-z₀)) w

theorem HasContValue.unique {q : ℕ} (hq : 2 ≤ q) {F : ℂ → ℂ} {z₀ w w' : ℂ} (h : HasContValue q F z₀ w)
    (h' : HasContValue q F z₀ w') : w = w' := by
  obtain ⟨R, hR, e⟩ := h
  obtain ⟨S, hS, e'⟩ := h'
  exact e.unique (hS.unique hq hR ▸ e')

def IsLaurentPoly (R : RatFunc ℂ) : Prop :=
  ∃ (m : ℕ) (p : ℂ[X]), R * RatFunc.X ^ m = algebraMap _ _ p

def substRat (a : RatFunc ℂ) (ha : Transcendental ℂ a) : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ :=
  RatFunc.liftAlgHom (aeval a) fun p hp =>
    mem_nonZeroDivisors_of_ne_zero fun e => nonZeroDivisors.ne_zero hp (transcendental_iff.1 ha p e)

@[simp] theorem substRat_X (a : RatFunc ℂ) (ha : Transcendental ℂ a) : substRat a ha RatFunc.X = a := by
  have := RatFunc.liftAlgHom_apply_div (aeval a) (fun p hp =>
    mem_nonZeroDivisors_of_ne_zero fun e => nonZeroDivisors.ne_zero hp (transcendental_iff.1 ha p e)) X 1
  simpa [substRat] using this

@[simp] theorem substRat_C (a : RatFunc ℂ) (ha : Transcendental ℂ a) (c : ℂ) :
    substRat a ha (RatFunc.C c) = RatFunc.C c := (substRat a ha).commutes c

theorem HasValueAt.substRat {a R : RatFunc ℂ} (ha : Transcendental ℂ a) {x y w : ℂ} (h : HasValueAt a x y)
    (h' : HasValueAt R y w) : HasValueAt (substRat a ha R) x w := by
  have key : ∀ p : ℂ[X], HasValueAt (aeval a p) x (p.eval y) := fun p => by
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simpa using hp.add hr
    | monomial m c => simpa [aeval_monomial] using (hasValueAt_C c x).mul (h.pow m)
  obtain ⟨c, d, hd, rfl, e⟩ := hasValueAt_iff.1 h'
  have := (key c).mul ((key d).inv hd)
  rw [← e, mul_inv_cancel_right₀ hd, ← div_eq_mul_inv] at this
  exact (congrArg (HasValueAt · x w) (RatFunc.liftAlgHom_apply_div (aeval a) _ c d)).mpr this

theorem transcendental_C_mul_X (u : ℂˣ) : Transcendental ℂ (RatFunc.C (u : ℂ) * RatFunc.X) := by
  refine RatFunc.transcendental_of_ne_C _ ?_
  rintro ⟨c, e⟩
  have h : ∀ x : ℂ, u * x = c := fun x =>
    ((hasValueAt_C u x).mul (hasValueAt_X x)).unique (e ▸ hasValueAt_C c x)
  simpa using (h 1).trans (h 0).symm

def scaleRat (u : ℂˣ) : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ := substRat _ (transcendental_C_mul_X u)

def reflectRat (u : ℂˣ) : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ :=
  substRat (RatFunc.C (u : ℂ) * RatFunc.X)⁻¹ fun h => transcendental_C_mul_X u (IsAlgebraic.inv_iff.1 h)

@[simp] theorem scaleRat_X (u : ℂˣ) : scaleRat u RatFunc.X = RatFunc.C (u : ℂ) * RatFunc.X := substRat_X _ _

@[simp] theorem reflectRat_X (u : ℂˣ) : reflectRat u RatFunc.X = (RatFunc.C (u : ℂ) * RatFunc.X)⁻¹ := substRat_X _ _

@[simp] theorem scaleRat_C (u : ℂˣ) (c : ℂ) : scaleRat u (RatFunc.C c) = RatFunc.C c := substRat_C _ _ _

@[simp] theorem reflectRat_C (u : ℂˣ) (c : ℂ) : reflectRat u (RatFunc.C c) = RatFunc.C c := substRat_C _ _ _

def natUnit (q : ℕ) (hq : q ≠ 0) : ℂˣ := Units.mk0 (q : ℂ) (Nat.cast_ne_zero.2 hq)

@[simp] theorem natUnit_val (q : ℕ) (hq : q ≠ 0) : (natUnit q hq : ℂ) = q := rfl

def negPowUnit (q : ℕ) (hq : q ≠ 0) (s : ℂ) : ℂˣ :=
  Units.mk0 ((q : ℂ) ^ (-s)) (by simp [hq])

@[simp] theorem negPowUnit_val (q : ℕ) (hq : q ≠ 0) (s : ℂ) : (negPowUnit q hq s : ℂ) = (q : ℂ) ^ (-s) := rfl

theorem HasValueAt.reflectRat {q : ℕ} (hq : q ≠ 0) {R : RatFunc ℂ} {z w : ℂ}
    (h : HasValueAt R ((q : ℂ) ^ (-(1 - z))) w) : HasValueAt (reflectRat (natUnit q hq) R) ((q : ℂ) ^ (-z)) w := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  refine HasValueAt.substRat _ ?_ h
  have e : (q : ℂ) ^ (-(1 - z)) = ((q : ℂ) * (q : ℂ) ^ (-z))⁻¹ := by
    rw [Complex.cpow_neg, sub_eq_add_neg, Complex.cpow_add _ _ hq', Complex.cpow_one]
  rw [e]
  exact ((hasValueAt_C _ _).mul (hasValueAt_X _)).inv (by simp [hq])

theorem HasValueAt.scaleRat {q : ℕ} (hq : q ≠ 0) {R : RatFunc ℂ} {z s w : ℂ}
    (h : HasValueAt R ((q : ℂ) ^ (-(z + s))) w) :
    HasValueAt (scaleRat (negPowUnit q hq s) R) ((q : ℂ) ^ (-z)) w := by
  refine HasValueAt.substRat _ ?_ h
  rw [neg_add_rev, Complex.cpow_add _ _ (Nat.cast_ne_zero.2 hq)]
  exact (hasValueAt_C _ _).mul (hasValueAt_X _)

theorem IsRatIn.shift {q : ℕ} (hq : q ≠ 0) {F : ℂ → ℂ} {R : RatFunc ℂ} (h : IsRatIn q F R) (s : ℂ) :
    IsRatIn q (fun z => F (z + s)) (scaleRat (negPowUnit q hq s) R) := by
  obtain ⟨r, h⟩ := h
  exact ⟨r - s.re, fun z hz => (h (z + s) (by simpa using sub_lt_iff_lt_add.1 hz)).scaleRat hq⟩

def lFactor (S : Multiset ℂˣ) : RatFunc ℂ := (S.map fun a : ℂˣ => (1 - RatFunc.C (a : ℂ) * RatFunc.X)⁻¹).prod

def gammaFactor (u : ℂˣ) (S : Multiset ℂˣ) : RatFunc ℂ := reflectRat u (lFactor (S.map (·⁻¹))) / lFactor S

@[simp] theorem lFactor_zero : lFactor 0 = 1 := by simp [lFactor]

@[simp] theorem lFactor_singleton (a : ℂˣ) : lFactor {a} = (1 - RatFunc.C (a : ℂ) * RatFunc.X)⁻¹ := by simp [lFactor]

end Rational

section ZetaNonvanishing₂
open ValuativeRel GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

def checkFun {G : Type} [Group G] (c : G → ℂ) : G → ℂ := fun x => c x⁻¹

@[simp] theorem checkFun_apply {G : Type} [Group G] (c : G → ℂ) (x : G) : checkFun c x = c x⁻¹ := rfl

@[simp] theorem checkFun_checkFun {G : Type} [Group G] (c : G → ℂ) : checkFun (checkFun c) = c := by
  ext x; simp

def matFT [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (Ξ : Matrix n n k → ℂ) : Matrix n n k → ℂ :=
  fun y => ∫ x, Ξ x * (ψ (trace (x * y)) : ℂ) ∂(volM ν n n)

def gjIntegrand (Ξ : Matrix n n k → ℂ) (c : GL n k → ℂ) (z : ℂ) (x : GL n k) : ℂ :=
  Ξ x.val * c x * ((nabs k (GeneralLinearGroup.det x) : ℝ) : ℂ) ^ (z + ((Fintype.card n : ℂ) - 1) / 2)

variable [MeasurableSpace (GL n k)]

def gjZeta (μ : Measure (GL n k)) (Ξ : Matrix n n k → ℂ) (c : GL n k → ℂ) (z : ℂ) : ℂ :=
  ∫ x, gjIntegrand Ξ c z x ∂μ

def GJConverges (μ : Measure (GL n k)) (Ξ : Matrix n n k → ℂ) (c : GL n k → ℂ) : Prop :=
  ∃ r : ℝ, ∀ z : ℂ, r < z.re → Integrable (gjIntegrand Ξ c z) μ

def HasGJ (μ : Measure (GL n k)) (Ξ : Matrix n n k → ℂ) (c : GL n k → ℂ) (R : RatFunc ℂ) : Prop :=
  GJConverges μ Ξ c ∧ IsRatIn (resCard k) (gjZeta μ Ξ c) R

def HasGJValue (μ : Measure (GL n k)) (Ξ : Matrix n n k → ℂ) (c : GL n k → ℂ) (z₀ w : ℂ) : Prop :=
  GJConverges μ Ξ c ∧ HasContValue (resCard k) (gjZeta μ Ξ c) z₀ w

variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}

theorem HasGJ.unique {R S : RatFunc ℂ} (h : HasGJ μ Ξ c R) (h' : HasGJ μ Ξ c S) : R = S :=
  h.2.unique (one_lt_resCard k) h'.2

theorem HasGJValue.unique {z₀ w w' : ℂ} (h : HasGJValue μ Ξ c z₀ w) (h' : HasGJValue μ Ξ c z₀ w') : w = w' :=
  h.2.unique (one_lt_resCard k) h'.2

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in
private theorem valuation_det_le_one_of_entries_integer {y : GL n k}
    (h : ∀ i j, (y : Matrix n n k) i j ∈ (valuation k).integer) :
    valuation k (GeneralLinearGroup.det y : k) ≤ 1 := by
  set A : Matrix n n (valuation k).integer := Matrix.of fun i j => ⟨(y : Matrix n n k) i j, h i j⟩
  have e : (y : Matrix n n k) = ((valuation k).integer.subtype).mapMatrix A := by
    ext i j
    rfl
  have hd : (GeneralLinearGroup.det y : k) = (valuation k).integer.subtype A.det := by
    rw [GeneralLinearGroup.val_det_apply, RingHom.map_det, ← e]
  rw [hd]
  exact (Valuation.mem_integer_iff _ _).mp (SetLike.coe_mem _)

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in

theorem _root_.GlobalTheory.LGrp.nabs_det_of_mem_KO {x : GL n k}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det x) = 1 := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hx
  apply _root_.GlobalTheory.SmGL.nabs_eq_one
  have h1 := valuation_det_le_one_of_entries_integer hx.1
  have h2 := valuation_det_le_one_of_entries_integer hx.2
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at h2
  have hpos : 0 < valuation k (GeneralLinearGroup.det x : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
private theorem smGL_ord_pow_eq_mul (x : kˣ) (m : ℕ) :
    _root_.GlobalTheory.SmGL.ord k (x ^ m) = m * _root_.GlobalTheory.SmGL.ord k x := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp)
  | succ m ih =>
    rw [pow_succ, _root_.GlobalTheory.SmGL.ord_mul, ih]
    push_cast
    ring

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
private theorem exists_unit_ord_eq_one_and_nabs_eq_inv_resCard :
    ∃ ϖ : kˣ, _root_.GlobalTheory.SmGL.ord k ϖ = 1 ∧
      _root_.GlobalTheory.SplitWeil.nabs k ϖ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹ := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (valuation k).integer
  have hp0 : (p : k) ≠ 0 := by
    intro h
    exact hp.ne_zero (Subtype.ext h)
  obtain ⟨y, hy⟩ : ∃ y : k, valuation k y = uniformizer k := valuation_surjective _
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact (uniformizer_pos (R := k)).ne hy
  have hyint : y ∈ (valuation k).integer := by
    rw [Valuation.mem_integer_iff, hy]
    exact uniformizer_lt_one.le
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨y, hyint⟩ : (valuation k).integer)) (fun h => hy0 (congrArg Subtype.val h)) hp
  have hu0 : ((u : (valuation k).integer) : k) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  refine ⟨Units.mk0 (p : k) hp0, ?_, _root_.GlobalTheory.SplitWeil.nabs_uniformiser hp rfl⟩
  have hyo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 y hy0) = 1 :=
    _root_.GlobalTheory.SmGL.ord_eq_one hy
  have huo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 _ hu0) = 0 := by
    apply _root_.GlobalTheory.SmGL.ord_eq_zero
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
  have hsplit : Units.mk0 y hy0 = Units.mk0 _ hu0 * Units.mk0 (p : k) hp0 ^ m := by
    ext
    have := congrArg Subtype.val hu
    simpa using this
  rw [hsplit, _root_.GlobalTheory.SmGL.ord_mul, huo, smGL_ord_pow_eq_mul,
    zero_add] at hyo
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hyo with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · omega

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in

theorem _root_.GlobalTheory.LGrp.nabs_eq_zpow (x : kˣ) :
    _root_.GlobalTheory.SplitWeil.nabs k x =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-_root_.GlobalTheory.SmGL.ord k x) := by
  obtain ⟨ϖ, hord, habs⟩ := exists_unit_ord_eq_one_and_nabs_eq_inv_resCard (k := k)
  have hq : (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ≠ 0 := by
    have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
    positivity
  have hinv : _root_.GlobalTheory.SplitWeil.nabs k ϖ⁻¹ = _root_.GlobalTheory.SplitWeil.resCard k := by
    have h := _root_.GlobalTheory.SplitWeil.nabs_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, _root_.GlobalTheory.SplitWeil.nabs_one, habs] at h
    exact ((inv_mul_eq_one₀ hq).mp h.symm).symm
  have oinv : _root_.GlobalTheory.SmGL.ord k ϖ⁻¹ = -1 := by
    have h := _root_.GlobalTheory.SmGL.ord_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, hord,
      _root_.GlobalTheory.SmGL.ord_eq_zero (x := (1 : kˣ)) (by simp)] at h
    omega
  have key : ∀ m : ℤ, _root_.GlobalTheory.SplitWeil.nabs k (ϖ ^ m) =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) ∧ _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
    intro m
    refine Int.induction_on m ?_ ?_ ?_
    · refine ⟨by simp [_root_.GlobalTheory.SplitWeil.nabs_one], ?_⟩
      rw [zpow_zero]
      exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp)
    · intro i ih
      rw [_root_.zpow_add_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, habs, hord]
      refine ⟨?_, rfl⟩
      rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
    · intro i ih
      rw [_root_.zpow_sub_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, hinv, oinv]
      refine ⟨?_, by ring⟩
      rw [show -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 by ring, zpow_add₀ hq, _root_.zpow_one]
  set o := _root_.GlobalTheory.SmGL.ord k x
  have hy : _root_.GlobalTheory.SmGL.ord k (x * ϖ ^ (-o)) = 0 := by
    rw [_root_.GlobalTheory.SmGL.ord_mul, (key _).2]
    ring
  have hy1 : _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o)) = 1 :=
    _root_.GlobalTheory.SmGL.nabs_eq_one k
      (_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp hy)
  have hx : x * ϖ ^ (-o) * ϖ ^ o = x := by
    rw [mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
  calc _root_.GlobalTheory.SplitWeil.nabs k x
      = _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o) * ϖ ^ o) := by rw [hx]
    _ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-o) := by
      rw [_root_.GlobalTheory.SplitWeil.nabs_mul, hy1, (key o).1, one_mul]

def cosetInd (g : GL n k) : Matrix n n k → ℂ :=
  Set.indicator (Units.val '' {x : GL n k | g⁻¹ * x ∈ KO k n}) 1

omit [MeasurableSpace (GL n k)] in

theorem cosetInd_mem_SB (g : GL n k) : cosetInd g ∈ SB (Matrix n n k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have e : {x : GL n k | g⁻¹ * x ∈ KO k n} = (Homeomorph.mulLeft g⁻¹) ⁻¹' (KO k n : Set (GL n k)) := rfl
  have hc : IsCompact (Units.val '' {x : GL n k | g⁻¹ * x ∈ KO k n}) :=
    (e ▸ (Homeomorph.isCompact_preimage _).2 SplitFlip.isCompact_KO).image Units.continuous_val
  have hr : IsOpen (Set.range fun x : GL n k => x.val) := by
    have : (Set.range fun x : GL n k => x.val) = {A | A.det ≠ 0} := by
      ext A
      exact ⟨fun ⟨x, hx⟩ => hx ▸ x.det_ne_zero, fun h => ⟨GeneralLinearGroup.mkOfDetNeZero A h, rfl⟩⟩
    rw [this]
    exact isOpen_ne_fun continuous_id.matrix_det continuous_const
  have ho : IsOpen (Units.val '' {x : GL n k | g⁻¹ * x ∈ KO k n}) :=
    (Topology.IsOpenEmbedding.mk SplitFlip.isEmbedding_val_GL hr).isOpenMap _
      (SplitFlip.isOpen_KO.preimage (continuous_const_mul _))
  exact ⟨(LocallyConstant.charFn ℂ ⟨hc.isClosed, ho⟩).isLocallyConstant,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩

end ZetaNonvanishing₂

end GlobalTheory.LGrp
