import Mathlib

noncomputable section

open IsLocalRing

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (A : Type*) [CommRing A] [Algebra O A]

abbrev As : Subalgebra O A := integralClosure O A

abbrev Pts : Type _ := MaximalSpectrum ↥(As O A)

variable {O A}

abbrev Loc (ζ : Pts O A) : Type _ := Localization.AtPrime ζ.asIdeal

class IsDVRAt (ζ : Pts O A) : Prop where

  isDomain : IsDomain (Loc ζ)

  isDVR : IsDiscreteValuationRing (Loc ζ)

attribute [instance] IsDVRAt.isDomain IsDVRAt.isDVR

theorem comap_eq_maximalIdeal (ζ : Pts O A) :
    ζ.asIdeal.comap (algebraMap O ↥(As O A)) = maximalIdeal O :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ζ.asIdeal)

instance isLocalHom_algebraMap (ζ : Pts O A) : IsLocalHom (algebraMap O (Loc ζ)) := by
  constructor
  intro a ha
  by_contra hna
  have h1 : a ∈ maximalIdeal O := (IsLocalRing.mem_maximalIdeal a).2 hna
  rw [← comap_eq_maximalIdeal ζ, Ideal.mem_comap] at h1
  rw [IsScalarTower.algebraMap_apply O ↥(As O A) (Loc ζ),
    IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal] at ha
  exact ha h1

def vL (ζ : Pts O A) (a : ↥(As O A)) : ℕ∞ := Ring.ord (Loc ζ) (algebraMap ↥(As O A) (Loc ζ) a)

def ep (ϖ : O) (ζ : Pts O A) : ℕ := (vL ζ (algebraMap O ↥(As O A) ϖ)).toNat

def fdeg (ζ : Pts O A) : ℕ := Module.finrank (ResidueField O) (ResidueField (Loc ζ))

def ordAt (ϖ : O) (ζ : Pts O A) (n : ℕ) (a : ↥(As O A)) : WithTop ℤ :=
  (vL ζ a).map (Nat.cast : ℕ → ℤ) + ((-((n : ℤ) * (ep ϖ ζ : ℤ)) : ℤ) : WithTop ℤ)

open Classical in

def ord (ϖ : O) (ζ : Pts O A) (x : A) : WithTop ℤ :=
  if h : ∃ n : ℕ, ϖ ^ n • x ∈ As O A then ordAt ϖ ζ h.choose ⟨ϖ ^ h.choose • x, h.choose_spec⟩ else ⊤

variable (A) in

structure IsUnif (ϖ : O) : Prop where

  irreducible : Irreducible ϖ

  isUnit : IsUnit (algebraMap O A ϖ)

  denom : ∀ x : A, ∃ n : ℕ, ϖ ^ n • x ∈ As O A

theorem isUnif_of_field (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra K A]
    [IsScalarTower O K A] [Algebra.IsIntegral K A] {ϖ : O} (hϖ : Irreducible ϖ) : IsUnif A ϖ where
  irreducible := hϖ
  isUnit := by
    rw [IsScalarTower.algebraMap_apply O K A]
    refine IsUnit.map _ (IsUnit.mk0 _ ?_)
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  denom := fun x => by
    obtain ⟨⟨d, hd⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors O) x (Algebra.IsIntegral.isIntegral (R := K) x)
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hd) hϖ
    refine ⟨n, ?_⟩
    have h2 : ϖ ^ n • x = (↑u⁻¹ : O) • (((u : O) * ϖ ^ n) • x) := by
      rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2]
    exact (As O A).smul_mem hint _

section Val

theorem vL_one (ζ : Pts O A) : vL ζ 1 = 0 := by simp [vL]

variable (ζ : Pts O A) [IsDVRAt ζ]

theorem vL_eq_addVal (a : ↥(As O A)) :
    vL ζ a = IsDiscreteValuationRing.addVal (Loc ζ) (algebraMap ↥(As O A) (Loc ζ) a) :=
  Ring.ord_eq_addVal _

theorem vL_zero : vL ζ 0 = ⊤ := by simp [vL_eq_addVal]

theorem vL_mul (a b : ↥(As O A)) : vL ζ (a * b) = vL ζ a + vL ζ b := by
  simp [vL_eq_addVal, map_mul]

theorem vL_pow (a : ↥(As O A)) (n : ℕ) : vL ζ (a ^ n) = n • vL ζ a := by
  simp [vL_eq_addVal, map_pow]

theorem vL_add (a b : ↥(As O A)) : min (vL ζ a) (vL ζ b) ≤ vL ζ (a + b) := by
  simp only [vL_eq_addVal, map_add]
  exact IsDiscreteValuationRing.addVal_add

theorem vL_eq_top_iff (a : ↥(As O A)) : vL ζ a = ⊤ ↔ algebraMap ↥(As O A) (Loc ζ) a = 0 := by
  rw [vL_eq_addVal, IsDiscreteValuationRing.addVal_eq_top_iff]

theorem vL_ne_top {a : ↥(As O A)} (ha : a ∈ nonZeroDivisors ↥(As O A)) : vL ζ a ≠ ⊤ := by
  rw [Ne, vL_eq_top_iff, IsLocalization.map_eq_zero_iff ζ.asIdeal.primeCompl]
  rintro ⟨⟨m, hm⟩, h⟩
  have : m = 0 := (mem_nonZeroDivisors_iff_right.1 ha) m h
  exact hm (this ▸ ζ.asIdeal.zero_mem)

theorem vL_eq_zero_iff (a : ↥(As O A)) : vL ζ a = 0 ↔ a ∉ ζ.asIdeal := by
  rw [vL_eq_addVal, IsDiscreteValuationRing.addVal_eq_zero_iff,
    IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal]
  rfl

end Val

section Ord

variable {ϖ : O}

theorem unif_mem_nonZeroDivisors (h : IsUnif A ϖ) :
    algebraMap O ↥(As O A) ϖ ∈ nonZeroDivisors ↥(As O A) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  have h1 : (b : A) * algebraMap O A ϖ = 0 := by
    have := congrArg (Subtype.val) hb
    simpa using this
  exact Subtype.ext (by simpa using (h.isUnit.mul_left_eq_zero).1 h1)

theorem unif_mem (h : IsUnif A ϖ) (ζ : Pts O A) : algebraMap O ↥(As O A) ϖ ∈ ζ.asIdeal := by
  rw [← Ideal.mem_comap, comap_eq_maximalIdeal, IsLocalRing.mem_maximalIdeal]
  exact h.irreducible.not_isUnit

variable (ζ : Pts O A) [IsDVRAt ζ]

theorem coe_ep (h : IsUnif A ϖ) : (ep ϖ ζ : ℕ∞) = vL ζ (algebraMap O ↥(As O A) ϖ) :=
  ENat.natCast_toNat (vL_ne_top ζ (unif_mem_nonZeroDivisors h))

theorem ep_pos (h : IsUnif A ϖ) : 0 < ep ϖ ζ := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  have h1 := coe_ep ζ h
  rw [h0, Nat.cast_zero, eq_comm, vL_eq_zero_iff] at h1
  exact h1 (unif_mem h ζ)

theorem ordAt_shift (h : IsUnif A ϖ) (n k : ℕ) (a : ↥(As O A)) :
    ordAt ϖ ζ (n + k) ((algebraMap O ↥(As O A) ϖ) ^ k * a) = ordAt ϖ ζ n a := by
  unfold ordAt
  rw [vL_mul, vL_pow, ← coe_ep ζ h]
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe j =>
    have h1 : k • (ep ϖ ζ : ℕ∞) + (j : ℕ∞) = ((k * ep ϖ ζ + j : ℕ) : ℕ∞) := by
      push_cast; simp [nsmul_eq_mul]
    rw [h1, ENat.map_natCast, ENat.map_natCast, ← WithTop.coe_add, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

theorem ordAt_indep (h : IsUnif A ϖ) {x : A} {n m : ℕ} (hn : ϖ ^ n • x ∈ As O A)
    (hm : ϖ ^ m • x ∈ As O A) :
    ordAt ϖ ζ n ⟨ϖ ^ n • x, hn⟩ = ordAt ϖ ζ m ⟨ϖ ^ m • x, hm⟩ := by
  rw [← ordAt_shift ζ h n m ⟨ϖ ^ n • x, hn⟩, ← ordAt_shift ζ h m n ⟨ϖ ^ m • x, hm⟩, add_comm m n]
  congr 1
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Algebra.smul_def, map_pow]
  have : ((algebraMap O ↥(As O A) ϖ : ↥(As O A)) : A) = algebraMap O A ϖ := rfl
  rw [this]
  ring

theorem ord_eq (h : IsUnif A ϖ) {x : A} {n : ℕ} (hn : ϖ ^ n • x ∈ As O A) :
    ord ϖ ζ x = ordAt ϖ ζ n ⟨ϖ ^ n • x, hn⟩ := by
  have hex : ∃ n : ℕ, ϖ ^ n • x ∈ As O A := ⟨n, hn⟩
  rw [ord, dif_pos hex]
  exact ordAt_indep ζ h _ _

theorem ord_of_mem (h : IsUnif A ϖ) {x : A} (hx : x ∈ As O A) :
    ord ϖ ζ x = (vL ζ ⟨x, hx⟩).map (Nat.cast : ℕ → ℤ) := by
  have h0 : ϖ ^ 0 • x ∈ As O A := by simpa using hx
  rw [ord_eq ζ h h0]
  simp [ordAt]

theorem ord_nonneg (h : IsUnif A ϖ) {x : A} (hx : x ∈ As O A) : 0 ≤ ord ϖ ζ x := by
  rw [ord_of_mem ζ h hx]
  exact ENat.map_natCast_nonneg

theorem ord_unif (h : IsUnif A ϖ) : ord ϖ ζ (algebraMap O A ϖ) = ((ep ϖ ζ : ℤ) : WithTop ℤ) := by
  have hm : algebraMap O A ϖ ∈ As O A := (algebraMap O ↥(As O A) ϖ).2
  rw [ord_of_mem ζ h hm]
  have : (⟨algebraMap O A ϖ, hm⟩ : ↥(As O A)) = algebraMap O ↥(As O A) ϖ :=
    rfl
  rw [this, ← coe_ep ζ h, ENat.map_natCast]

theorem ord_zero (h : IsUnif A ϖ) : ord ϖ ζ 0 = ⊤ := by
  rw [ord_of_mem ζ h (As O A).zero_mem]
  have : (⟨0, (As O A).zero_mem⟩ : ↥(As O A)) = 0 := rfl
  rw [this, vL_zero, ENat.map_top]

theorem ord_one (h : IsUnif A ϖ) : ord ϖ ζ 1 = 0 := by
  rw [ord_of_mem ζ h (As O A).one_mem]
  have : (⟨1, (As O A).one_mem⟩ : ↥(As O A)) = 1 := rfl
  rw [this, vL_one]
  rfl

theorem ordAt_mul (n m : ℕ) (a b : ↥(As O A)) :
    ordAt ϖ ζ (n + m) (a * b) = ordAt ϖ ζ n a + ordAt ϖ ζ m b := by
  unfold ordAt
  rw [vL_mul]
  have h1 : (vL ζ a + vL ζ b).map (Nat.cast : ℕ → ℤ)
      = (vL ζ a).map (Nat.cast : ℕ → ℤ) + (vL ζ b).map (Nat.cast : ℕ → ℤ) :=
    ENat.map_add (Nat.castAddMonoidHom ℤ) _ _
  have h2 : ((-(((n + m : ℕ) : ℤ) * (ep ϖ ζ : ℤ)) : ℤ) : WithTop ℤ)
      = ((-((n : ℤ) * (ep ϖ ζ : ℤ)) : ℤ) : WithTop ℤ) + ((-((m : ℤ) * (ep ϖ ζ : ℤ)) : ℤ) : WithTop ℤ) := by
    rw [← WithTop.coe_add]
    congr 1
    push_cast
    ring
  rw [h1, h2, add_add_add_comm]

theorem ord_mul (h : IsUnif A ϖ) (x y : A) : ord ϖ ζ (x * y) = ord ϖ ζ x + ord ϖ ζ y := by
  obtain ⟨n, hn⟩ := h.denom x
  obtain ⟨m, hm⟩ := h.denom y
  have e : ϖ ^ (n + m) • (x * y) = (ϖ ^ n • x) * (ϖ ^ m • y) := by
    rw [smul_mul_smul_comm, pow_add]
  have hnm : ϖ ^ (n + m) • (x * y) ∈ As O A := e ▸ (As O A).mul_mem hn hm
  rw [ord_eq ζ h hn, ord_eq ζ h hm, ord_eq ζ h hnm, ← ordAt_mul]
  congr 1
  exact Subtype.ext e

theorem ordAt_add (n : ℕ) (a b : ↥(As O A)) :
    min (ordAt ϖ ζ n a) (ordAt ϖ ζ n b) ≤ ordAt ϖ ζ n (a + b) := by
  unfold ordAt
  rw [min_add_add_right]
  refine add_le_add_left ?_ _
  have hm : Monotone (ENat.map (Nat.cast : ℕ → ℤ)) := ENat.monotone_map_iff.2 Nat.mono_cast
  rw [← hm.map_min]
  exact hm (vL_add ζ a b)

theorem ord_add (h : IsUnif A ϖ) (x y : A) :
    min (ord ϖ ζ x) (ord ϖ ζ y) ≤ ord ϖ ζ (x + y) := by
  obtain ⟨n, hn⟩ := h.denom x
  obtain ⟨m, hm⟩ := h.denom y
  have hx : ϖ ^ (n + m) • x ∈ As O A := by
    rw [add_comm, pow_add, mul_smul]; exact (As O A).smul_mem hn _
  have hy : ϖ ^ (n + m) • y ∈ As O A := by
    rw [pow_add, mul_smul]; exact (As O A).smul_mem hm _
  have hxy : ϖ ^ (n + m) • (x + y) ∈ As O A := by
    rw [smul_add]; exact (As O A).add_mem hx hy
  rw [ord_eq ζ h hx, ord_eq ζ h hy, ord_eq ζ h hxy]
  refine (ordAt_add ζ _ _ _).trans (le_of_eq ?_)
  congr 1
  exact Subtype.ext (smul_add _ _ _).symm

theorem ord_ne_top (h : IsUnif A ϖ) {x : A} (hx : x ∈ nonZeroDivisors A) : ord ϖ ζ x ≠ ⊤ := by
  obtain ⟨n, hn⟩ := h.denom x
  rw [ord_eq ζ h hn, ordAt]
  have h1 : (⟨ϖ ^ n • x, hn⟩ : ↥(As O A)) ∈ nonZeroDivisors ↥(As O A) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro b hb
    have h2 : (b : A) * (ϖ ^ n • x) = 0 := congrArg Subtype.val hb
    rw [Algebra.smul_def, map_pow, mul_left_comm] at h2
    have h3 := ((h.isUnit.pow n).mul_right_eq_zero).1 h2
    exact Subtype.ext ((mem_nonZeroDivisors_iff_right.1 hx) _ h3)
  have h2 := vL_ne_top ζ h1
  rw [Ne, WithTop.add_eq_top, not_or]
  exact ⟨by simpa using h2, WithTop.coe_ne_top⟩

end Ord

section Ord2

variable {ϖ : O}

theorem ord_pow (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (x : A) (k : ℕ) :
    ord ϖ ζ (x ^ k) = k • ord ϖ ζ x := by
  induction k with
  | zero => simp [ord_one ζ h]
  | succ k ih => rw [pow_succ, ord_mul ζ h, ih, succ_nsmul]

theorem ord_pow_smul (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (k : ℕ) (x : A) :
    ord ϖ ζ (ϖ ^ k • x) = (((k : ℤ) * (ep ϖ ζ : ℤ) : ℤ) : WithTop ℤ) + ord ϖ ζ x := by
  rw [Algebra.smul_def, map_pow, ord_mul ζ h, ord_pow ζ h, ord_unif ζ h]
  rw [← WithTop.coe_nsmul, nsmul_eq_mul]

theorem ord_eq_zero_of_isUnit (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) {a : ↥(As O A)}
    (ha : IsUnit a) : ord ϖ ζ (a : A) = 0 := by
  rw [ord_of_mem ζ h a.2]
  have h1 : vL ζ a = 0 := by
    rw [vL_eq_zero_iff]
    exact fun hm => ζ.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hm ha)
  change (vL ζ a).map (Nat.cast : ℕ → ℤ) = 0
  rw [h1]
  rfl

theorem ord_algebraMap_unit (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (u : Oˣ) :
    ord ϖ ζ (algebraMap O A u) = 0 :=
  ord_eq_zero_of_isUnit ζ h (a := algebraMap O ↥(As O A) u) (u.isUnit.map _)

theorem ordAt_nonneg_iff (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (n : ℕ) (a : ↥(As O A)) :
    0 ≤ ordAt ϖ ζ n a ↔ vL ζ ((algebraMap O ↥(As O A) ϖ) ^ n) ≤ vL ζ a := by
  unfold ordAt
  rw [vL_pow, ← coe_ep ζ h]
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe j =>
    have h1 : n • (ep ϖ ζ : ℕ∞) = ((n * ep ϖ ζ : ℕ) : ℕ∞) := by
      push_cast; simp [nsmul_eq_mul]
    rw [h1, ENat.map_natCast, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe,
      Nat.cast_le]
    constructor
    · intro hh
      have : ((n * ep ϖ ζ : ℕ) : ℤ) ≤ (j : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · intro hh
      have : ((n * ep ϖ ζ : ℕ) : ℤ) ≤ (j : ℤ) := by exact_mod_cast hh
      push_cast at this
      linarith

theorem mem_As_iff [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (x : A) :
    x ∈ As O A ↔ ∀ ζ : Pts O A, 0 ≤ ord ϖ ζ x := by
  refine ⟨fun hx ζ => ord_nonneg ζ h hx, fun hx => ?_⟩
  obtain ⟨n, hn⟩ := h.denom x
  have key : (⟨ϖ ^ n • x, hn⟩ : ↥(As O A)) ∈ Ideal.span {(algebraMap O ↥(As O A) ϖ) ^ n} := by
    have h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) ⟨ϖ ^ n • x, hn⟩ ∈
        Ideal.map (algebraMap ↥(As O A) (Loc ζ))
          (Ideal.span {(algebraMap O ↥(As O A) ϖ) ^ n}) := by
      intro ζ
      have h1 := hx ζ
      rw [ord_eq ζ h hn, ordAt_nonneg_iff ζ h, vL_eq_addVal, vL_eq_addVal,
        IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
      rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
      exact h1
    exact Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 key
  have h2 : (algebraMap O A ϖ) ^ n * x = (algebraMap O A ϖ) ^ n * (b : A) := by
    have := congrArg Subtype.val hb
    simpa [Algebra.smul_def] using this
  rw [(h.isUnit.pow n).mul_right_inj.1 h2]
  exact b.2

end Ord2

section Ball

variable {V : Type*} [AddCommGroup V] [Module A V]

variable (A) in

def IsGen (e : V) : Prop := Function.Bijective (fun a : A => a • e)

def coord (e v : V) : A := Function.invFun (fun a : A => a • e) v

theorem coord_smul_self {e : V} (he : IsGen A e) (v : V) : (coord e v : A) • e = v :=
  Function.invFun_eq (f := fun a : A => a • e) (he.2 v)

theorem coord_smul_gen {e : V} (he : IsGen A e) (a : A) : coord e (a • e) = a :=
  Function.leftInverse_invFun (f := fun a : A => a • e) he.1 a

theorem coord_gen {e : V} (he : IsGen A e) : (coord e e : A) = 1 := by
  simpa using coord_smul_gen he (1 : A)

theorem coord_zero {e : V} (he : IsGen A e) : (coord e (0 : V) : A) = 0 := by
  simpa using coord_smul_gen he (0 : A)

theorem coord_add {e : V} (he : IsGen A e) (v w : V) :
    (coord e (v + w) : A) = coord e v + coord e w := by
  conv_lhs => rw [← coord_smul_self he v, ← coord_smul_self he w, ← add_smul]
  exact coord_smul_gen he _

theorem coord_smul {e : V} (he : IsGen A e) (a : A) (v : V) :
    (coord e (a • v) : A) = a * coord e v := by
  conv_lhs => rw [← coord_smul_self he v, smul_smul]
  exact coord_smul_gen he _

def ordV (ϖ : O) (ζ : Pts O A) (e : V) (c : Pts O A → ℤ) (v : V) : WithTop ℤ :=
  ord ϖ ζ (coord e v) + ((c ζ : ℤ) : WithTop ℤ)

def ballSet (ϖ : O) (e : V) (c : Pts O A → ℤ) : Set V := {v | ∀ ζ : Pts O A, 0 ≤ ordV ϖ ζ e c v}

def ball (ϖ : O) (e : V) (c : Pts O A → ℤ) : Submodule ↥(As O A) V :=
  Submodule.span ↥(As O A) (ballSet ϖ e c)

def ballO [Module O V] [IsScalarTower O A V] (ϖ : O) (e : V) (c : Pts O A → ℤ) : Submodule O V :=
  (ball ϖ e c).restrictScalars O

variable {ϖ : O} {e : V} (c : Pts O A → ℤ)

theorem ordV_gen (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) :
    ordV ϖ ζ e c e = ((c ζ : ℤ) : WithTop ℤ) := by
  rw [ordV, coord_gen he, ord_one ζ h, zero_add]

theorem ordV_zero (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) :
    ordV ϖ ζ e c 0 = ⊤ := by
  rw [ordV, coord_zero he, ord_zero ζ h, top_add]

theorem ordV_smul (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) (a : A) (v : V) :
    ordV ϖ ζ e c (a • v) = ord ϖ ζ a + ordV ϖ ζ e c v := by
  rw [ordV, ordV, coord_smul he, ord_mul ζ h, add_assoc]

theorem ordV_add (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) (v w : V) :
    min (ordV ϖ ζ e c v) (ordV ϖ ζ e c w) ≤ ordV ϖ ζ e c (v + w) := by
  rw [ordV, ordV, ordV, coord_add he, min_add_add_right]
  exact add_le_add_left (ord_add ζ h _ _) _

theorem mem_ball_iff [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) (v : V) :
    v ∈ ball ϖ e c ↔ ∀ ζ : Pts O A, 0 ≤ ordV ϖ ζ e c v := by
  refine ⟨fun hv => ?_, fun hv => Submodule.subset_span hv⟩
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro ζ; rw [ordV_zero c ζ h he]; exact le_top
  | add x y _ _ hx hy => exact fun ζ => (le_min (hx ζ) (hy ζ)).trans (ordV_add c ζ h he x y)
  | smul a x _ hx =>
    intro ζ
    have : a • x = (a : A) • x := rfl
    rw [this, ordV_smul c ζ h he]
    exact add_nonneg (ord_nonneg ζ h a.2) (hx ζ)

theorem mem_ballO_iff [Module O V] [IsScalarTower O A V] [∀ ζ : Pts O A, IsDVRAt ζ]
    (h : IsUnif A ϖ) (he : IsGen A e) (v : V) :
    v ∈ ballO ϖ e c ↔ ∀ ζ : Pts O A, 0 ≤ ordV ϖ ζ e c v :=
  mem_ball_iff c h he v

theorem mem_ball_zero_iff [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) (v : V) :
    v ∈ ball ϖ e (0 : Pts O A → ℤ) ↔ (coord e v : A) ∈ As O A := by
  rw [mem_ball_iff _ h he, mem_As_iff h]
  simp [ordV]

theorem ball_mono [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e)
    {c c' : Pts O A → ℤ} (hc : c ≤ c') : ball ϖ e c ≤ ball ϖ e c' := by
  intro v hv
  rw [mem_ball_iff _ h he] at hv ⊢
  exact fun ζ => (hv ζ).trans (add_le_add_right (WithTop.coe_le_coe.2 (hc ζ)) _)

theorem pow_smul_mem_ball_iff [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e)
    (k : ℕ) (v : V) :
    (algebraMap O A ϖ) ^ k • v ∈ ball ϖ e c ↔
      v ∈ ball ϖ e (fun ζ => c ζ + (k : ℤ) * (ep ϖ ζ : ℤ)) := by
  rw [mem_ball_iff _ h he, mem_ball_iff _ h he]
  refine forall_congr' (fun ζ => ?_)
  rw [ordV_smul c ζ h he, ord_pow ζ h, ord_unif ζ h, ordV, ordV, ← WithTop.coe_nsmul,
    nsmul_eq_mul, WithTop.coe_add, add_left_comm, add_comm (((c ζ : ℤ) : WithTop ℤ))]

end Ball

section Compare

theorem ep_eq_ramificationIdx {ϖ : O} (hϖ : Irreducible ϖ) (ζ : Pts O A) :
    ep ϖ ζ = ζ.asIdeal.ramificationIdx O := by
  have h1 : (ζ.asIdeal.under O).map (algebraMap O (Loc ζ))
      = Ideal.span {algebraMap ↥(As O A) (Loc ζ) (algebraMap O ↥(As O A) ϖ)} := by
    rw [Ideal.under_def, comap_eq_maximalIdeal, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton, ← IsScalarTower.algebraMap_apply]
  rw [Ideal.ramificationIdx_def, h1]
  rfl

theorem ep_congr {ϖ ϖ' : O} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (ζ : Pts O A) :
    ep ϖ ζ = ep ϖ' ζ := by
  rw [ep_eq_ramificationIdx hϖ, ep_eq_ramificationIdx hϖ']

theorem fdeg_eq_inertiaDeg (ζ : Pts O A) : fdeg ζ = ζ.asIdeal.inertiaDeg O := by
  have : ζ.asIdeal.LiesOver (maximalIdeal O) := ⟨(comap_eq_maximalIdeal ζ).symm⟩
  let _ : Algebra (O ⧸ maximalIdeal O) (ResidueField O) :=
    show Algebra (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O) from Algebra.id _
  have : IsFractionRing (O ⧸ maximalIdeal O) (ResidueField O) := by
    let _ : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
    show IsFractionRing (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O)
    infer_instance
  have : IsScalarTower O (O ⧸ maximalIdeal O) (ResidueField O) :=
    show IsScalarTower O (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O) from inferInstance
  exact (Ideal.inertiaDeg_eq_of_isFractionRing (maximalIdeal O) ζ.asIdeal (ResidueField O)
    (ResidueField (Loc ζ))).symm

theorem ord_congr {ϖ ϖ' : O} (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (h' : IsUnif A ϖ')
    (x : A) : ord ϖ ζ x = ord ϖ' ζ x := by
  obtain ⟨n, hn⟩ := h.denom x
  have hm : algebraMap O A ϖ ∈ As O A := (algebraMap O ↥(As O A) ϖ).2
  have hm' : (⟨algebraMap O A ϖ, hm⟩ : ↥(As O A)) = algebraMap O ↥(As O A) ϖ := rfl
  have key : ∀ ϖ'' : O, IsUnif A ϖ'' → ord ϖ'' ζ (ϖ ^ n • x)
      = (((n : ℤ) * (ep ϖ ζ : ℤ) : ℤ) : WithTop ℤ) + ord ϖ'' ζ x := by
    intro ϖ'' h''
    rw [Algebra.smul_def, map_pow, ord_mul ζ h'', ord_pow ζ h'', ord_of_mem ζ h'' hm, hm',
      ← coe_ep ζ h, ENat.map_natCast, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have h1 : ord ϖ ζ (ϖ ^ n • x) = ord ϖ' ζ (ϖ ^ n • x) := by
    rw [ord_of_mem ζ h hn, ord_of_mem ζ h' hn]
  rw [key ϖ h, key ϖ' h'] at h1
  exact (WithTop.add_left_inj WithTop.coe_ne_top).1 h1

end Compare

section OrdZ

variable {ϖ : O} (ζ : Pts O A) [IsDVRAt ζ]

theorem ord_units_add_inv (h : IsUnif A ϖ) (u : Aˣ) :
    ord ϖ ζ (u : A) + ord ϖ ζ ((u⁻¹ : Aˣ) : A) = 0 := by
  rw [← ord_mul ζ h, Units.mul_inv, ord_one ζ h]

def ordZ (ϖ : O) (ζ : Pts O A) (x : A) : ℤ := (ord ϖ ζ x).untopD 0

theorem coe_ordZ (h : IsUnif A ϖ) {x : A} (hx : x ∈ nonZeroDivisors A) :
    ((ordZ ϖ ζ x : ℤ) : WithTop ℤ) = ord ϖ ζ x := by
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 (ord_ne_top ζ h hx)
  rw [ordZ, ← hz]
  rfl

theorem ordZ_mul (h : IsUnif A ϖ) {x y : A} (hx : x ∈ nonZeroDivisors A)
    (hy : y ∈ nonZeroDivisors A) : ordZ ϖ ζ (x * y) = ordZ ϖ ζ x + ordZ ϖ ζ y := by
  apply WithTop.coe_injective
  rw [WithTop.coe_add, coe_ordZ ζ h hx, coe_ordZ ζ h hy, coe_ordZ ζ h (mul_mem hx hy),
    ord_mul ζ h]

theorem ordZ_unif (h : IsUnif A ϖ) : ordZ ϖ ζ (algebraMap O A ϖ) = ep ϖ ζ := by
  rw [ordZ, ord_unif ζ h]
  rfl

theorem ordZ_units_inv (h : IsUnif A ϖ) (u : Aˣ) :
    ordZ ϖ ζ ((u⁻¹ : Aˣ) : A) = - ordZ ϖ ζ (u : A) := by
  have h1 := ord_units_add_inv ζ h u
  rw [← coe_ordZ ζ h u.isUnit.mem_nonZeroDivisors,
    ← coe_ordZ ζ h (u⁻¹).isUnit.mem_nonZeroDivisors, ← WithTop.coe_add, ← WithTop.coe_zero,
    WithTop.coe_inj] at h1
  linarith

end OrdZ

section Ball2

variable {V : Type*} [AddCommGroup V] [Module A V] {ϖ : O} {e : V} (c : Pts O A → ℤ)

theorem isScalarTower_of_field (K : Type*) [Field K] [Algebra O K] [Algebra K A]
    [IsScalarTower O K A] [Module K V] [IsScalarTower K A V] [Module O V] [IsScalarTower O K V] :
    IsScalarTower O A V :=
  ⟨fun o a v => by
    rw [← algebraMap_smul K o a, ← algebraMap_smul K o (a • v), smul_assoc]⟩

def coordEquiv (he : IsGen A e) : V ≃ₗ[A] A :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton A V e) he).symm

theorem coordEquiv_apply (he : IsGen A e) (v : V) : coordEquiv he v = coord e v :=
  (LinearEquiv.symm_apply_eq _).2 (coord_smul_self he v).symm

theorem isGen_units_smul (he : IsGen A e) (u : Aˣ) : IsGen A ((u : A) • e) := by
  have : (fun a : A => a • ((u : A) • e)) = (fun a : A => a • e) ∘ (fun a : A => a * u) := by
    funext a
    simp [smul_smul]
  rw [IsGen, this]
  exact he.comp (Units.mulRight_bijective u)

theorem coord_units_smul (he : IsGen A e) (u : Aˣ) (v : V) :
    (coord ((u : A) • e) v : A) * u = coord e v := by
  apply he.1
  change ((coord ((u : A) • e) v : A) * u) • e = (coord e v : A) • e
  rw [mul_smul, coord_smul_self (isGen_units_smul he u), coord_smul_self he]

theorem ordV_units_smul_gen (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) (u : Aˣ)
    (v : V) : ordV ϖ ζ e c v = ord ϖ ζ (u : A) + ordV ϖ ζ ((u : A) • e) c v := by
  rw [ordV, ← coord_units_smul he u, ord_mul ζ h, ordV, add_comm (ord ϖ ζ (coord _ v)), add_assoc]

theorem le_mul_ep (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (N : ℕ) :
    (N : ℤ) ≤ (N : ℤ) * (ep ϖ ζ : ℤ) := by
  exact_mod_cast Nat.le_mul_of_pos_right N (ep_pos ζ h)

theorem exists_pow_smul_mem_ball [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e)
    {N : ℕ} (hc : ∀ ζ, -(N : ℤ) ≤ c ζ) (v : V) :
    ∃ k : ℕ, (algebraMap O A ϖ) ^ k • v ∈ ball ϖ e c := by
  obtain ⟨n, hn⟩ := h.denom (coord e v : A)
  refine ⟨N + n, ?_⟩
  rw [mem_ball_iff c h he]
  intro ζ
  have h1 : 0 ≤ ord ϖ ζ ((algebraMap O A ϖ) ^ n) + ord ϖ ζ (coord e v : A) := by
    have := ord_nonneg ζ h hn
    rwa [Algebra.smul_def, map_pow, ord_mul ζ h] at this
  have h2 : 0 ≤ ord ϖ ζ ((algebraMap O A ϖ) ^ N) + ((c ζ : ℤ) : WithTop ℤ) := by
    rw [ord_pow ζ h, ord_unif ζ h, ← WithTop.coe_nsmul, nsmul_eq_mul, ← WithTop.coe_add,
      ← WithTop.coe_zero, WithTop.coe_le_coe]
    have := le_mul_ep ζ h N
    have := hc ζ
    linarith
  rw [ordV_smul c ζ h he, pow_add, ord_mul ζ h, ordV, add_comm (ord ϖ ζ (coord e v : A)),
    add_add_add_comm]
  exact add_nonneg h2 h1

theorem pow_smul_coord_mem_As [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e)
    {N : ℕ} (hc : ∀ ζ, c ζ ≤ (N : ℤ)) {v : V} (hv : v ∈ ball ϖ e c) :
    ϖ ^ N • (coord e v : A) ∈ As O A := by
  rw [mem_ball_iff c h he] at hv
  rw [mem_As_iff h]
  intro ζ
  rw [ord_pow_smul ζ h, add_comm]
  refine (hv ζ).trans (add_le_add_right (WithTop.coe_le_coe.2 ?_) _)
  exact (hc ζ).trans (le_mul_ep ζ h N)

end Ball2

section FieldCase

theorem isDVRAt_of_field_ext (K : Type*) {L : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    [Field L] [Algebra O L] [Algebra K L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (ζ : Pts O L) : IsDVRAt ζ := by
  have : IsDedekindDomain ↥(As O L) := integralClosure.isDedekindDomain O K L
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h : IsUnif L ϖ := isUnif_of_field K hϖ
  have hne : ζ.asIdeal ≠ ⊥ := by
    intro h0
    have h1 := unif_mem h ζ
    rw [h0, Ideal.mem_bot] at h1
    exact nonZeroDivisors.ne_zero (unif_mem_nonZeroDivisors h) h1
  have hd : IsDomain (Loc ζ) := inferInstance
  exact ⟨hd, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hne _⟩

end FieldCase

end Formalism.MainNotions.Gaps.EtaleWeightGaps
