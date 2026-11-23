import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsWeilFunction
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.ChTor GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

section Tate

variable (p : ℕ) (M : Type) [CommGroup M]

def tateSeq : Subgroup (ℕ → M) where
  carrier := {s | ∀ n, s n ^ p ^ n = 1 ∧ s (n + 1) ^ p = s n}
  mul_mem' := fun {s t} hs ht n => ⟨by rw [Pi.mul_apply, mul_pow, (hs n).1, (ht n).1, _root_.mul_one],
    by rw [Pi.mul_apply, mul_pow, (hs n).2, (ht n).2, Pi.mul_apply]⟩
  one_mem' := fun _ => ⟨one_pow _, one_pow _⟩
  inv_mem' := fun {s} hs n => ⟨by rw [Pi.inv_apply, inv_pow, (hs n).1, inv_one],
    by rw [Pi.inv_apply, inv_pow, (hs n).2, Pi.inv_apply]⟩

def Tate : Type := Additive (tateSeq p M)

instance : AddCommGroup (Tate p M) := inferInstanceAs (AddCommGroup (Additive (tateSeq p M)))

variable {p M}

namespace Tate

def lev (t : Tate p M) (n : ℕ) : M := (Additive.toMul (α := tateSeq p M) t).1 n

def mk (s : ℕ → M) (h : ∀ n, s n ^ p ^ n = 1 ∧ s (n + 1) ^ p = s n) : Tate p M :=
  Additive.ofMul (α := tateSeq p M) ⟨s, h⟩

@[simp] theorem lev_mk (s : ℕ → M) (h : ∀ n, s n ^ p ^ n = 1 ∧ s (n + 1) ^ p = s n) (n : ℕ) :
    (mk s h).lev n = s n := rfl

theorem lev_pow (t : Tate p M) (n : ℕ) : t.lev n ^ p ^ n = 1 := ((Additive.toMul (α := tateSeq p M) t).2 n).1

theorem lev_succ (t : Tate p M) (n : ℕ) : t.lev (n + 1) ^ p = t.lev n := ((Additive.toMul (α := tateSeq p M) t).2 n).2

@[ext] theorem ext {s t : Tate p M} (h : ∀ n, s.lev n = t.lev n) : s = t := Additive.toMul.injective (Subtype.ext (funext h))

@[simp] theorem lev_add (s t : Tate p M) (n : ℕ) : (s + t).lev n = s.lev n * t.lev n := rfl

@[simp] theorem lev_zero (n : ℕ) : (0 : Tate p M).lev n = 1 := rfl

theorem lev_add_pow (t : Tate p M) (n k : ℕ) : t.lev (n + k) ^ p ^ k = t.lev n := by
  induction k with
  | zero => rw [pow_zero, pow_one]; rfl
  | succ k ih =>
    show t.lev (n + k + 1) ^ p ^ (k + 1) = t.lev n
    rw [pow_succ', pow_mul, t.lev_succ, ih]

variable [Fact p.Prime]

instance : SMul ℤ_[p] (Tate p M) where
  smul a t := mk (fun n => t.lev n ^ digit n a) fun n =>
    ⟨by rw [← pow_mul, mul_comm, pow_mul, lev_pow, one_pow],
      by rw [← pow_mul, mul_comm, pow_mul, lev_succ, pow_digit_succ (t.lev_pow n)]⟩

theorem lev_smul (a : ℤ_[p]) (t : Tate p M) (n : ℕ) : (a • t).lev n = t.lev n ^ digit n a := rfl

instance : Module ℤ_[p] (Tate p M) where
  one_smul t := ext fun n => pow_digit_one (t.lev_pow n)
  mul_smul a b t := ext fun n => pow_digit_mul (t.lev_pow n) a b
  smul_zero _ := ext fun _ => one_pow _
  smul_add _ _ _ := ext fun _ => mul_pow _ _ _
  add_smul a b t := ext fun n => pow_digit_add (t.lev_pow n) a b
  zero_smul t := ext fun n => by rw [lev_smul, digit_zero, pow_zero, lev_zero]

variable (p) in

def map {M' : Type} [CommGroup M'] (f : M →* M') : Tate p M →ₗ[ℤ_[p]] Tate p M' where
  toFun t := mk (fun n => f (t.lev n)) fun n =>
    ⟨by rw [← map_pow, lev_pow, map_one], by rw [← map_pow, lev_succ]⟩
  map_add' _ _ := ext fun _ => map_mul f _ _
  map_smul' _ _ := ext fun _ => map_pow f _ _

@[simp] theorem lev_map {M' : Type} [CommGroup M'] (f : M →* M') (t : Tate p M) (n : ℕ) :
    (map p f t).lev n = f (t.lev n) := rfl

theorem map_injective {M' : Type} [CommGroup M'] {f : M →* M'} (hf : Function.Injective f) :
    Function.Injective (map p f) := fun s t h => Tate.ext fun n => hf (by simpa using congrArg (fun u => Tate.lev u n) h)

theorem map_smul_of_isHausdorff {T O : Type} [AddCommGroup T] [Module ℤ_[p] T] [CommRing O]
    [Algebra ℤ_[p] O] [IsHausdorff (Ideal.span {(p : O)}) O] (f : T →+ O) (a : ℤ_[p]) (t : T) :
    f (a • t) = a • f t := by
  have hH : IsHausdorff (Ideal.span {(p : O)}) O := inferInstance
  refine sub_eq_zero.1 (hH.haus _ fun n => ?_)
  obtain ⟨b, hb⟩ := pow_dvd_sub_digit (p := p) n a
  have ha : a = ((digit n a : ℕ) : ℤ_[p]) + ((p ^ n : ℕ) : ℤ_[p]) * b := by
    rw [Nat.cast_pow, ← hb]; ring
  have e1 : ∀ (m : ℕ) (x : T), f ((m : ℤ_[p]) • x) = (m : O) * f x := fun m x => by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
  have key : f (a • t) - a • f t = (p : O) ^ n * (f (b • t) - algebraMap ℤ_[p] O b * f t) := by
    rw [ha, add_smul, map_add, mul_smul, e1, e1, Algebra.smul_def]
    simp only [map_add, map_mul, map_pow, map_natCast, Nat.cast_pow]
    ring
  rw [SModEq.sub_mem, sub_zero, key, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)

end Tate

end Tate

section Cyclotomic

variable (p : ℕ) [Fact p.Prime] (C : Type) [Field C]

def Eps : Type := {ε : Tate p Cˣ // IsPrimitiveRoot (ε.lev 1) p}

variable {p C}

theorem Eps.isPrimitiveRoot (ε : Eps p C) (n : ℕ) : IsPrimitiveRoot (ε.1.lev n) (p ^ n) := by
  have hp : p.Prime := Fact.out
  cases n with
  | zero => simpa [IsPrimitiveRoot.one_right_iff] using ε.1.lev_pow 0
  | succ n =>
    have hord : orderOf (ε.1.lev (n + 1)) = p ^ (n + 1) := by
      apply orderOf_eq_prime_pow
      · intro h
        have h1 := ε.1.lev_add_pow 1 n
        rw [Nat.add_comm 1 n, h] at h1
        exact ε.2.ne_one hp.one_lt h1.symm
      · exact ε.1.lev_pow (n + 1)
    rw [← hord]
    exact IsPrimitiveRoot.orderOf _

theorem Eps.bijective (ε : Eps p C) :
    Function.Bijective (LinearMap.toSpanSingleton ℤ_[p] (Tate p Cˣ) ε.1) := by
  have hp : p.Prime := Fact.out
  have hε := ε.isPrimitiveRoot
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    have h1 : ε.1.lev n ^ digit n a = 1 := by
      have h2 := congrArg (fun u => Tate.lev u n) ha
      simpa only [LinearMap.toSpanSingleton_apply, Tate.lev_smul, Tate.lev_zero] using h2
    rw [map_zero, ← cast_digit, CharP.cast_eq_zero_iff (ZMod (p ^ n)) (p ^ n)]
    exact ((hε n).pow_eq_one_iff_dvd _).1 h1
  · intro t
    have hex : ∀ n, ∃ i : ℕ, ε.1.lev n ^ i = t.lev n := fun n => by
      have hC : IsPrimitiveRoot ((ε.1.lev n : Cˣ) : C) (p ^ n) := IsPrimitiveRoot.coe_units_iff.2 (hε n)
      obtain ⟨i, -, hi⟩ := hC.eq_pow_of_pow_eq_one (ξ := ((t.lev n : Cˣ) : C))
        (by rw [← Units.val_pow_eq_pow_val, t.lev_pow, Units.val_one])
      exact ⟨i, Units.ext (by rw [Units.val_pow_eq_pow_val, hi])⟩
    choose k hk using hex
    have hstep : ∀ n, ((k (n + 1) : ℕ) : ZMod (p ^ n)) = k n := fun n => by
      have h3 : ε.1.lev n ^ k (n + 1) = ε.1.lev n ^ k n := by
        rw [hk n, ← ε.1.lev_succ n, ← pow_mul, mul_comm, pow_mul, hk (n + 1), t.lev_succ]
      have h9 := pow_eq_pow_iff_modEq.1 h3
      rw [← (hε n).eq_orderOf] at h9
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h9
    have hcomp : ∀ n m, n ≤ m → ((k m : ℕ) : ZMod (p ^ n)) = k n := fun n m hnm => by
      induction m, hnm using Nat.le_induction with
      | base => rfl
      | succ m hnm ih =>
        rw [← ih]
        have h4 := congrArg (ZMod.castHom (pow_dvd_pow p hnm) (ZMod (p ^ n))) (hstep m)
        simpa only [map_natCast] using h4
    set x : ℕ → ℤ_[p] := fun m => (k m : ℤ_[p]) with hx
    have hmem : ∀ n m, n ≤ m → x m - x n ∈ Ideal.span {(p : ℤ_[p]) ^ n} := fun n m hnm => by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hx]
      simp only [map_natCast]
      rw [hcomp n m hnm, sub_self]
    have hnorm : ∀ n m, n ≤ m → ‖x m - x n‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := fun n m hnm =>
      (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 (hmem n m hnm)
    have hlim : Filter.Tendsto (fun N : ℕ => (p : ℝ) ^ (-(N : ℤ))) Filter.atTop (nhds 0) := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have h5 := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (zero_le_one.trans hp1.le)) (inv_lt_one_of_one_lt₀ hp1)
      refine h5.congr fun N => ?_
      rw [zpow_neg, zpow_natCast, inv_pow]
    have hcau : CauchySeq x := by
      refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => (p : ℝ) ^ (-(N : ℤ))) (fun m m' N hm hm' => ?_) hlim
      rw [dist_eq_norm]
      have h6 : x m - x m' = (x m - x N) - (x m' - x N) := by ring
      rw [h6]
      exact (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 (Ideal.sub_mem _ (hmem N m hm) (hmem N m' hm'))
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcau
    have hA : ∀ n, PadicInt.toZModPow n a = (k n : ZMod (p ^ n)) := fun n => by
      have h7 : ‖a - x n‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
        le_of_tendsto ((ha.sub_const (x n)).norm) (Filter.eventually_atTop.2 ⟨n, fun m hm => hnorm n m hm⟩)
      have h8 := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 h7
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h8
      rw [h8, hx]
      simp only [map_natCast]
    exact ⟨a, Tate.ext fun n => by
      rw [LinearMap.toSpanSingleton_apply, Tate.lev_smul, pow_digit_eq (ε.1.lev_pow n) (hA n).symm, hk]⟩

def Eps.equiv (ε : Eps p C) : ℤ_[p] ≃ₗ[ℤ_[p]] Tate p Cˣ :=
  LinearEquiv.ofBijective _ ε.bijective

theorem Eps.lev_equiv (ε : Eps p C) (a : ℤ_[p]) (n : ℕ) :
    (ε.equiv a).lev n = ε.1.lev n ^ digit n a := rfl

instance [IsAlgClosed C] [CharZero C] : Nonempty (Eps p C) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  have h1 : ∀ u : Cˣ, ∃ w : Cˣ, w ^ p = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : C) hp.pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext hz⟩
  choose r hr using h1
  let u : Cˣ := (hζ.isUnit hp.ne_zero).unit
  have hu : IsPrimitiveRoot u p := IsPrimitiveRoot.coe_units_iff.1 hζ
  let s : ℕ → Cˣ := fun n => Nat.casesOn n 1 fun m => r^[m] u
  have h2 : ∀ n, s (n + 1) ^ p = s n := by
    rintro (_ | n)
    · exact hu.pow_eq_one
    · change r^[n + 1] u ^ p = r^[n] u
      rw [Function.iterate_succ_apply', hr]
  have h3 : ∀ n, s n ^ p ^ n = 1 := fun n => by
    induction n with
    | zero => exact one_pow _
    | succ n ih => rw [pow_succ', pow_mul, h2, ih]
  exact ⟨⟨Tate.mk s fun n => ⟨h3 n, h2 n⟩, hu⟩⟩

end Cyclotomic

section Abelian

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C))

def weil : ℕ → Pts A.A → Pts A.A → Cˣ := (exists_weil_function C A).choose

variable {A} {k : ℕ}

theorem weilIs_iff (hk : 1 ≤ k) {z s : Pts A.A} (hz : z ^ k = 1) (hs : s ^ k = 1) (w : Cˣ) :
    Out.WeilIs A.A A.L (k : ℤ) z s (unitOn w) ↔ w = weil A k z s := ((exists_weil_function C A).choose_spec k hk).1 z s hz hs w

theorem weil_mul_left (hk : 1 ≤ k) {z z' s : Pts A.A} (hz : z ^ k = 1) (hz' : z' ^ k = 1)
    (hs : s ^ k = 1) : weil A k (z * z') s = weil A k z s * weil A k z' s := (((exists_weil_function C A).choose_spec k hk).2.1 z z' s hz hz' hs).1

theorem weil_mul_right (hk : 1 ≤ k) {z z' s : Pts A.A} (hz : z ^ k = 1) (hz' : z' ^ k = 1)
    (hs : s ^ k = 1) : weil A k s (z * z') = weil A k s z * weil A k s z' := (((exists_weil_function C A).choose_spec k hk).2.1 z z' s hz hz' hs).2

theorem weil_level (hk : 1 ≤ k) {l : ℕ} (hl : 1 ≤ l) {z s : Pts A.A} (hz : z ^ k = 1)
    (hs : s ^ (k * l) = 1) : weil A (k * l) z s = weil A k z (s ^ l) := ((exists_weil_function C A).choose_spec k hk).2.2.1 l z s hl hz hs

theorem weil_perfect (hk : 1 ≤ k) (κ : Pts A.A → Cˣ)
    (hκ : ∀ z z', z ^ k = 1 → z' ^ k = 1 → κ (z * z') = κ z * κ z') :
    ∃! s : Pts A.A, s ^ k = 1 ∧ ∀ z, z ^ k = 1 → weil A k z s = κ z := ((exists_weil_function C A).choose_spec k hk).2.2.2 κ hκ

theorem weil_self (hk : 1 ≤ k) {z : Pts A.A} (hz : z ^ k = 1) : weil A k z z = 1 := by
  have h1 := (GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.1 : Out.WeilSt)
  unfold Out.WeilSt at h1
  have h2 := (h1 _ A k _).2.2.1 z hz
  exact ((weilIs_iff hk hz hz 1).1 (by rw [unitOn_one']; exact h2)).symm

theorem weil_pow_left (hk : 1 ≤ k) {z s : Pts A.A} (hz : z ^ k = 1) (hs : s ^ k = 1) (m : ℕ) :
    weil A k (z ^ m) s = weil A k z s ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero]
    have h := weil_mul_left (A := A) hk (one_pow k) (one_pow k) hs
    rw [_root_.mul_one] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  | succ m ih =>
    rw [pow_succ, pow_succ, weil_mul_left hk (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]) hz hs, ih]

theorem weil_pow_right (hk : 1 ≤ k) {z s : Pts A.A} (hz : z ^ k = 1) (hs : s ^ k = 1) (m : ℕ) :
    weil A k s (z ^ m) = weil A k s z ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero]
    have h := weil_mul_right (A := A) hk (one_pow k) (one_pow k) hs
    rw [_root_.mul_one] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  | succ m ih =>
    rw [pow_succ, pow_succ, weil_mul_right hk (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]) hz hs, ih]

variable (p : ℕ) [Fact p.Prime]

omit [IsAlgClosed C] [CharZero C] in
theorem one_le_ppow (n : ℕ) : 1 ≤ p ^ n := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos

variable (A)

abbrev TateA : Type := Tate p (Pts A.A)

def weilT : TateA A p →ₗ[ℤ_[p]] TateA A p →ₗ[ℤ_[p]] Tate p Cˣ :=
  LinearMap.mk₂ ℤ_[p]
    (fun s t => Tate.mk (fun n => weil A (p ^ n) (s.lev n) (t.lev n)) fun n =>
      ⟨by
        rw [← weil_pow_left (one_le_ppow p n) (s.lev_pow n) (t.lev_pow n), s.lev_pow]
        simpa using weil_pow_left (one_le_ppow p n) (s.lev_pow n) (t.lev_pow n) 0, by
        rw [← weil_pow_left (one_le_ppow p _) (s.lev_pow _) (t.lev_pow _), s.lev_succ, pow_succ,
          weil_level (one_le_ppow p n) (Fact.out : p.Prime).pos (s.lev_pow n) (t.lev_pow (n + 1)),
          t.lev_succ]⟩)
    (fun s s' t => Tate.ext fun n =>
      weil_mul_left (one_le_ppow p n) (s.lev_pow n) (s'.lev_pow n) (t.lev_pow n))
    (fun _ s t => Tate.ext fun n => weil_pow_left (one_le_ppow p n) (s.lev_pow n) (t.lev_pow n) _)
    (fun s t t' => Tate.ext fun n =>
      weil_mul_right (one_le_ppow p n) (t.lev_pow n) (t'.lev_pow n) (s.lev_pow n))
    (fun _ s t => Tate.ext fun n => weil_pow_right (one_le_ppow p n) (t.lev_pow n) (s.lev_pow n) _)

theorem lev_weilT (s t : TateA A p) (n : ℕ) :
    (weilT A p s t).lev n = weil A (p ^ n) (s.lev n) (t.lev n) := rfl

variable {p}

def pairT (ε : Eps p C) : LinearMap.BilinForm ℤ_[p] (TateA A p) :=
  (weilT A p).compr₂ ε.equiv.symm.toLinearMap

theorem pow_pairT (ε : Eps p C) (s t : TateA A p) (n : ℕ) :
    ε.1.lev n ^ digit n (pairT A ε s t) = weil A (p ^ n) (s.lev n) (t.lev n) := by
  have h : pairT A ε s t = ε.equiv.symm (weilT A p s t) := rfl
  rw [h, ← Eps.lev_equiv, LinearEquiv.apply_symm_apply, lev_weilT]

theorem isAlt_pairT (ε : Eps p C) : (pairT A ε).IsAlt := by
  intro s
  have h0 : weilT A p s s = 0 := Tate.ext fun n => by
    rw [lev_weilT, Tate.lev_zero, weil_self (one_le_ppow p n) (s.lev_pow n)]
  have e : pairT A ε s s = ε.equiv.symm (weilT A p s s) := rfl
  rw [e, h0, map_zero]

end Abelian

section Action

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {Λ : Type} [CommRing Λ]
  (α : Out.RingAct G Λ)

def actPts (T : Over S) (a : Λ) : (T ⟶ G) →* (T ⟶ G) :=
  haveI := α.hom a
  MonoidHom.mk' (fun x => x ≫ α.act a) fun x y => MonObj.mul_comp x y _

theorem actPts_add (T : Over S) (a b : Λ) (x : T ⟶ G) :
    x ≫ α.act (a + b) = (x ≫ α.act a) * (x ≫ α.act b) := by rw [α.map_add]; exact MonObj.comp_mul _ _ _

def actTate (p : ℕ) [Fact p.Prime] (T : Over S) : Λ →+* Module.End ℤ_[p] (Tate p (T ⟶ G)) :=
  RingHom.mk' (MonoidHom.mk (OneHom.mk (fun a => Tate.map p (actPts α T a))
      (LinearMap.ext fun t => Tate.ext fun n => by
        change t.lev n ≫ α.act 1 = t.lev n
        rw [α.map_one, Category.comp_id]))
      (fun a b => LinearMap.ext fun t => Tate.ext fun n => by
        change t.lev n ≫ α.act (a * b) = (t.lev n ≫ α.act b) ≫ α.act a
        rw [α.map_mul, Category.assoc]))
    fun a b => LinearMap.ext fun t => Tate.ext fun n => actPts_add α T a b (t.lev n)

theorem lev_actTate (p : ℕ) [Fact p.Prime] (T : Over S) (a : Λ) (t : Tate p (T ⟶ G)) (n : ℕ) :
    (actTate α p T a t).lev n = t.lev n ≫ α.act a := rfl

end Action

section Rosati

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {A : Out.PolAV (Sp C)}
  {Λ : Type} [CommRing Λ] [StarRing Λ] (o : A.OAct Λ)

theorem weil_act {k : ℕ} (hk : 1 ≤ k) (a : Λ) {z s : Pts A.A} (hz : z ^ k = 1) (hs : s ^ k = 1) :
    weil A k (z ≫ o.act a) s = weil A k z (s ≫ o.act (star a)) := by
  have hG : Out.GlobalFnsSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hC : Out.CubeSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.1
  haveI := o.toRingAct.hom a
  haveI := o.toRingAct.hom (star a)
  have hz' : (z ≫ o.act a) ^ k = 1 := by
    have h3 := map_pow (actPts o.toRingAct _ a) z k
    rw [hz, map_one] at h3
    exact h3.symm
  have hs' : (s ≫ o.act (star a)) ^ k = 1 := by
    have h3 := map_pow (actPts o.toRingAct _ (star a)) s k
    rw [hs, map_one] at h3
    exact h3.symm
  have h1 := (weilIs_iff hk hz hs' (weil A k z (s ≫ o.act (star a)))).2 rfl
  have h2 := (GlobalTheory.weilIs_rosati_iff hG hC A (o.act a) (o.act (star a)) (o.rosati a) k z s hz hs _).2 h1
  exact ((weilIs_iff hk hz' hs _).1 h2).symm

theorem pairT_act {p : ℕ} [Fact p.Prime] (ε : Eps p C) (a : Λ) (s t : TateA A p) :
    pairT A ε (actTate o.toRingAct p _ a s) t = pairT A ε s (actTate o.toRingAct p _ (star a) t) := by
  have h : weilT A p (actTate o.toRingAct p _ a s) t = weilT A p s (actTate o.toRingAct p _ (star a) t) :=
    Tate.ext fun n => by
      rw [lev_weilT, lev_weilT, lev_actTate, lev_actTate]
      exact weil_act o (one_le_ppow p n) a (s.lev_pow n) (t.lev_pow n)
  have e : ∀ x y, pairT A ε x y = ε.equiv.symm (weilT A p x y) := fun _ _ => rfl
  rw [e, e, h]

end Rosati

end GlobalTheory.HTLat
