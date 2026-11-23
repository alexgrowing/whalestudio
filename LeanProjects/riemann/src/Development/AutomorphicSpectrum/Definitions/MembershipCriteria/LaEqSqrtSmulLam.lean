import Mathlib

noncomputable section

namespace GlobalTheory.CompanionTheory.FinHeis

structure Sys (X M : Type) [AddCommGroup X] [AddCommGroup M] [Module ℂ M] where

  c : X → X → ℂ

  rho : X → M →ₗ[ℂ] M

  B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ
  c_add_left : ∀ x x' y, c (x + x') y = c x y * c x' y
  c_add_right : ∀ x y y', c x (y + y') = c x y * c x y'
  c_self : ∀ x, c x x = 1
  c_norm : ∀ x y, ‖c x y‖ = 1
  rho_zero : ∀ v, rho 0 v = v
  rho_rho : ∀ x y v, rho x (rho y v) = c x y • rho (x + y) v
  B_conj : ∀ u v, (starRingEnd ℂ) (B u v) = B v u
  B_pos : ∀ v, v ≠ 0 → 0 < (B v v).re
  B_rho : ∀ x u v, B (rho x u) (rho x v) = B u v

variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)

def SelfDual (Γ : AddSubgroup X) : Prop := ∀ x, x ∈ Γ ↔ ∀ γ ∈ Γ, S.c γ x ^ 2 = 1

def IsSemi (al : X → ℂ) (Γ : AddSubgroup X) : Prop :=
  (∀ x ∈ Γ, al x = 1 ∨ al x = -1) ∧ ∀ x ∈ Γ, ∀ y ∈ Γ, al (x + y) = al x * al y * S.c x y

def Law (al : X → ℂ) (Γ : AddSubgroup X) (φ : M) : Prop := ∀ γ ∈ Γ, S.rho γ φ = (al γ)⁻¹ • φ

def Cyclic (φ : M) : Prop := Submodule.span ℂ (Set.range fun x => S.rho x φ) = ⊤

def UnitVac (al : X → ℂ) (Γ : AddSubgroup X) (φ : M) : Prop := Law S al Γ φ ∧ S.B φ φ = 1

def la (al : X → ℂ) (Γ' Γ : AddSubgroup X) (φ : M) : M :=
  ∑ᶠ q : Γ' ⧸ Γ.addSubgroupOf Γ', al ((Quotient.out q : Γ') : X) • S.rho ((Quotient.out q : Γ') : X) φ

def abelian₂ (al : X → ℂ) (Γ' Γ : AddSubgroup X) (φ : M) : M :=
  ((Real.sqrt (Γ.relIndex Γ' : ℝ) : ℝ) : ℂ)⁻¹ • la S al Γ' Γ φ

def Implements (g : X ≃+ X) (T : M →ₗ[ℂ] M) : Prop :=
  (∀ x v, T (S.rho x v) = S.rho (g x) (T v)) ∧ ∀ u v, S.B (T u) (T v) = S.B u v

def ip : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ := S.B.flip

@[simp] theorem ip_apply (u v : M) : ip S u v = S.B v u := rfl

theorem ip_smul_left (a : ℂ) (u v : M) : ip S (a • u) v = a * ip S u v := by simp

theorem ip_smul_right (a : ℂ) (u v : M) : ip S u (a • v) = (starRingEnd ℂ) a * ip S u v := by simp

theorem ip_conj (u v : M) : (starRingEnd ℂ) (ip S u v) = ip S v u := S.B_conj v u

theorem ip_pos (v : M) (hv : v ≠ 0) : 0 < (ip S v v).re := S.B_pos v hv

theorem ip_rho (x : X) (u v : M) : ip S (S.rho x u) (S.rho x v) = ip S u v := S.B_rho x v u

theorem unitVac_iff_ip (al : X → ℂ) (Γ : AddSubgroup X) (φ : M) :
    UnitVac S al Γ φ ↔ Law S al Γ φ ∧ ip S φ φ = 1 := Iff.rfl

theorem implements_iff_ip (g : X ≃+ X) (T : M →ₗ[ℂ] M) :
    Implements S g T ↔ (∀ x v, T (S.rho x v) = S.rho (g x) (T v)) ∧ ∀ u v, ip S (T u) (T v) = ip S u v :=
  ⟨fun h => ⟨h.1, fun u v => h.2 v u⟩, fun h => ⟨h.1, fun u v => h.2 v u⟩⟩

namespace Sys

theorem c_mul_c_swap (x y : X) : S.c x y * S.c y x = 1 := by
  have h := S.c_self (x + y)
  rw [S.c_add_left, S.c_add_right, S.c_add_right, S.c_self, S.c_self] at h
  simpa using h

theorem c_ne_zero (x y : X) : S.c x y ≠ 0 := by
  intro h
  have := S.c_norm x y
  rw [h] at this
  simp at this

theorem c_zero_right (x : X) : S.c x 0 = 1 := by
  have h := S.c_add_right x 0 0
  rw [add_zero] at h
  exact (mul_eq_left₀ (S.c_ne_zero x 0)).1 h.symm

theorem c_zero_left (x : X) : S.c 0 x = 1 := by
  have h := S.c_mul_c_swap x 0
  rwa [S.c_zero_right, one_mul] at h

theorem c_neg_self (x : X) : S.c x (-x) = 1 := by
  have h := S.c_add_right x x (-x)
  rw [add_neg_cancel, S.c_zero_right, S.c_self, one_mul] at h
  exact h.symm

theorem rho_rho_neg (x : X) (v : M) : S.rho x (S.rho (-x) v) = v := by
  rw [S.rho_rho, S.c_neg_self, add_neg_cancel, S.rho_zero, one_smul]

theorem rho_neg_rho (x : X) (v : M) : S.rho (-x) (S.rho x v) = v := by
  simpa using S.rho_rho_neg (-x) v

theorem rho_bijective (x : X) : Function.Bijective (S.rho x) :=
  Function.bijective_iff_has_inverse.2 ⟨S.rho (-x), S.rho_neg_rho x, S.rho_rho_neg x⟩

theorem rho_comm (x y : X) (v : M) : S.rho x (S.rho y v) = S.c x y ^ 2 • S.rho y (S.rho x v) := by
  rw [S.rho_rho, S.rho_rho, smul_smul, add_comm y x]
  congr 1
  linear_combination (-(S.c x y)) * S.c_mul_c_swap x y

end Sys

variable {S}

theorem IsSemi.mul_self {al : X → ℂ} {Γ : AddSubgroup X} (h : IsSemi S al Γ) {x : X} (hx : x ∈ Γ) :
    al x * al x = 1 := by
  rcases h.1 x hx with e | e <;> rw [e] <;> norm_num

theorem IsSemi.inv_eq {al : X → ℂ} {Γ : AddSubgroup X} (h : IsSemi S al Γ) {x : X} (hx : x ∈ Γ) :
    (al x)⁻¹ = al x := by
  rcases h.1 x hx with e | e <;> rw [e] <;> norm_num

theorem IsSemi.conj_eq {al : X → ℂ} {Γ : AddSubgroup X} (h : IsSemi S al Γ) {x : X} (hx : x ∈ Γ) :
    (starRingEnd ℂ) (al x) = al x := by
  rcases h.1 x hx with e | e <;> rw [e] <;> simp

theorem IsSemi.op_op {al : X → ℂ} {Γ : AddSubgroup X} (h : IsSemi S al Γ) {x y : X} (hx : x ∈ Γ) (hy : y ∈ Γ)
    (v : M) : al x • S.rho x (al y • S.rho y v) = al (x + y) • S.rho (x + y) v := by
  rw [map_smul, S.rho_rho, h.2 x hx y hy]
  simp only [smul_smul, mul_assoc]

theorem IsSemi.law_iff {al : X → ℂ} {Γ : AddSubgroup X} (h : IsSemi S al Γ) (φ : M) :
    Law S al Γ φ ↔ ∀ γ ∈ Γ, al γ • S.rho γ φ = φ := by
  refine ⟨fun hφ γ hγ => ?_, fun hφ γ hγ => ?_⟩
  · rw [hφ γ hγ, h.inv_eq hγ, smul_smul, h.mul_self hγ, one_smul]
  · rw [h.inv_eq hγ]
    conv_rhs => rw [← hφ γ hγ]
    rw [smul_smul, h.mul_self hγ, one_smul]

theorem term_add {al : X → ℂ} {Γ Γ' : AddSubgroup X} (h' : IsSemi S al Γ') {φ : M} (hφ : Law S al Γ φ)
    {x γ : X} (hx : x ∈ Γ') (hγ : γ ∈ Γ) (hγ' : γ ∈ Γ') :
    al (x + γ) • S.rho (x + γ) φ = al x • S.rho x φ := by
  rw [← h'.op_op hx hγ', hφ γ hγ, h'.inv_eq hγ', smul_smul (al γ) (al γ), h'.mul_self hγ', one_smul]

theorem la_eq_finsum {al : X → ℂ} {Γ Γ' : AddSubgroup X} (h' : IsSemi S al Γ') {φ : M} (hφ : Law S al Γ φ)
    (s : Γ' ⧸ Γ.addSubgroupOf Γ' → Γ') (hs : ∀ q, (QuotientAddGroup.mk (s q) : Γ' ⧸ Γ.addSubgroupOf Γ') = q) :
    la S al Γ' Γ φ = ∑ᶠ q, al (s q : X) • S.rho (s q : X) φ := by
  unfold la
  congr 1
  funext q
  have hq : (QuotientAddGroup.mk (s q) : Γ' ⧸ Γ.addSubgroupOf Γ') = QuotientAddGroup.mk (Quotient.out q) := by
    rw [hs]; exact (Quotient.out_eq q).symm
  have hd := AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 hq)
  have := term_add h' hφ (s q).2 hd (-(s q) + Quotient.out q).2
  rw [← AddSubgroup.coe_add, add_neg_cancel_left] at this
  exact this

theorem la_eq_sum {al : X → ℂ} {Γ Γ' : AddSubgroup X} [Fintype (Γ' ⧸ Γ.addSubgroupOf Γ')] (h' : IsSemi S al Γ')
    {φ : M} (hφ : Law S al Γ φ) (s : Γ' ⧸ Γ.addSubgroupOf Γ' → Γ')
    (hs : ∀ q, (QuotientAddGroup.mk (s q) : Γ' ⧸ Γ.addSubgroupOf Γ') = q) :
    la S al Γ' Γ φ = ∑ q, al (s q : X) • S.rho (s q : X) φ := by
  rw [la_eq_finsum h' hφ s hs, finsum_eq_sum_of_fintype]

theorem la_eq_sqrt_smul_Lam (al : X → ℂ) {Γ Γ' : AddSubgroup X} (hN : Γ.relIndex Γ' ≠ 0) (φ : M) :
    la S al Γ' Γ φ = ((Real.sqrt (Γ.relIndex Γ' : ℝ) : ℝ) : ℂ) • abelian₂ S al Γ' Γ φ := by
  have : ((Real.sqrt (Γ.relIndex Γ' : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (Γ.relIndex Γ' : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
    exact_mod_cast (Real.sqrt_pos.2 this).ne'
  rw [abelian₂, smul_smul, mul_inv_cancel₀ this, one_smul]

theorem Lam_self {al : X → ℂ} {Γ : AddSubgroup X} (h : IsSemi S al Γ) {φ : M} (hφ : Law S al Γ φ) :
    abelian₂ S al Γ Γ φ = φ := by
  have hsub : Subsingleton (Γ ⧸ Γ.addSubgroupOf Γ) := by
    rw [AddSubgroup.addSubgroupOf_self]; exact QuotientAddGroup.subsingleton_quotient_top
  letI : Unique (Γ ⧸ Γ.addSubgroupOf Γ) := uniqueOfSubsingleton 0
  rw [abelian₂, AddSubgroup.relIndex_self, la, finsum_unique, (h.law_iff φ).1 hφ _ (Subtype.prop _)]
  simp

theorem ip_rho_eq_zero {al : X → ℂ} {Γ : AddSubgroup X} (hΓ : SelfDual S Γ) (h : IsSemi S al Γ) {φ : M}
    (hφ : Law S al Γ φ) {x : X} (hx : x ∉ Γ) : ip S (S.rho x φ) φ = 0 := by
  have : ¬ ∀ γ ∈ Γ, S.c γ x ^ 2 = 1 := fun hh => hx ((hΓ x).2 hh)
  push Not at this
  obtain ⟨γ, hγ, hne⟩ := this
  have e1 := ip_rho S γ (S.rho x φ) φ
  rw [S.rho_comm γ x, hφ γ hγ, h.inv_eq hγ, map_smul (S.rho x), ip_smul_left, ip_smul_left, ip_smul_right,
    h.conj_eq hγ] at e1
  have : (S.c γ x ^ 2 - 1) * ip S (S.rho x φ) φ = 0 := by
    linear_combination e1 - S.c γ x ^ 2 * ip S (S.rho x φ) φ * h.mul_self hγ
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

theorem Implements.refl : Implements S (AddEquiv.refl X) LinearMap.id := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem Implements.comp {g g' : X ≃+ X} {T T' : M →ₗ[ℂ] M} (h : Implements S g T) (h' : Implements S g' T') :
    Implements S (g'.trans g) (T ∘ₗ T') :=
  ⟨fun x v => by simp [h'.1, h.1], fun u v => by simp [h.2, h'.2]⟩

theorem Implements.injective {g : X ≃+ X} {T : M →ₗ[ℂ] M} (h : Implements S g T) : Function.Injective T := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  have := S.B_pos v hne
  rw [← h.2, hv] at this
  simp at this

theorem Implements.c_map [Nontrivial M] {g : X ≃+ X} {T : M →ₗ[ℂ] M} (h : Implements S g T) (x y : X) :
    S.c (g x) (g y) = S.c x y := by
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  have e : T (S.rho x (S.rho y v)) = T (S.c x y • S.rho (x + y) v) := by rw [S.rho_rho]
  rw [h.1, h.1, S.rho_rho, map_smul, h.1, map_add] at e
  have hne : S.rho (g x + g y) (T v) ≠ 0 := by
    intro h0
    apply hv
    apply h.injective
    apply (S.rho_bijective (g x + g y)).1
    rw [h0]; simp
  exact smul_left_injective ℂ hne e

theorem Implements.law {g : X ≃+ X} {T : M →ₗ[ℂ] M} (h : Implements S g T) {al : X → ℂ} {Γ : AddSubgroup X}
    (hal : ∀ γ ∈ Γ, al (g γ) = al γ) {φ : M} (hφ : Law S al Γ φ) : Law S al (Γ.map g.toAddMonoidHom) (T φ) := by
  rintro _ ⟨γ, hγ, rfl⟩
  change S.rho (g γ) (T φ) = (al (g γ))⁻¹ • T φ
  rw [← h.1, hφ γ hγ, map_smul, hal γ hγ]

theorem Implements.unitVac {g : X ≃+ X} {T : M →ₗ[ℂ] M} (h : Implements S g T) {al : X → ℂ} {Γ : AddSubgroup X}
    (hal : ∀ γ ∈ Γ, al (g γ) = al γ) {φ : M} (hφ : UnitVac S al Γ φ) :
    UnitVac S al (Γ.map g.toAddMonoidHom) (T φ) :=
  ⟨h.law hal hφ.1, by rw [h.2, hφ.2]⟩

namespace Inh

def e (n : ZMod 4) : ℂ := Complex.I ^ n.val

theorem e_add (m n : ZMod 4) : e (m + n) = e m * e n := by
  unfold e
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (m.val + n.val) 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

theorem e_zero : e 0 = 1 := by simp [e]

theorem e_one : e 1 = Complex.I := by
  have : (1 : ZMod 4).val = 1 := by decide
  simp [e, this]

theorem e_two : e 2 = -1 := by
  have : (2 : ZMod 4).val = 2 := by decide
  simp [e, this]

theorem e_norm (n : ZMod 4) : ‖e n‖ = 1 := by simp [e]

theorem e_conj (n : ZMod 4) : (starRingEnd ℂ) (e n) * e n = 1 := by
  rw [Complex.conj_mul', e_norm]; simp

theorem e_eq_one (n : ZMod 4) (h : 2 * n = 0) : e n = 1 ∨ e n = -1 := by
  have : n = 0 ∨ n = 2 := by revert n; decide
  rcases this with rfl | rfl
  · exact Or.inl e_zero
  · exact Or.inr e_two

theorem e_sq (n : ZMod 4) : e n ^ 2 = 1 ↔ 2 * n = 0 := by
  rw [sq, ← e_add, ← two_mul]
  have : 2 * n = 0 ∨ 2 * n = 2 := by revert n; decide
  rcases this with h | h
  · rw [h, e_zero]; simp
  · rw [h, e_two]
    constructor
    · intro hh; norm_num at hh
    · intro hh; exact absurd hh (by decide)

def dbl (t : ZMod 2) : ZMod 4 := 2 * (t.val : ZMod 4)

def red (a : ZMod 4) : ZMod 2 := (a.val : ZMod 2)

theorem red_add (a b : ZMod 4) : red (a + b) = red a + red b := by revert a b; decide

theorem dbl_add (t : ZMod 2) (a : ZMod 4) : dbl (t + red a) = dbl t + 2 * a := by revert t a; decide

def rhoEx (x : ZMod 4 × ZMod 4) : (ZMod 2 → ℂ) →ₗ[ℂ] (ZMod 2 → ℂ) where
  toFun f t := e (x.1 * x.2 + x.2 * dbl t) * f (t + red x.1)
  map_add' f g := by ext t; simp [mul_add]
  map_smul' a f := by ext t; simp; ring

def BEx : (ZMod 2 → ℂ) →ₗ⋆[ℂ] (ZMod 2 → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun f g => (starRingEnd ℂ) (f 0) * g 0 + (starRingEnd ℂ) (f 1) * g 1)
    (by intro f f' g; simp; ring) (by intro a f g; simp; ring) (by intro f g g'; simp; ring) (by intro a f g; simp; ring)

theorem BEx_apply (f g : ZMod 2 → ℂ) :
    BEx f g = (starRingEnd ℂ) (f 0) * g 0 + (starRingEnd ℂ) (f 1) * g 1 := rfl

theorem zmod2 (t : ZMod 2) : t = 0 ∨ t = 1 := by revert t; decide

def sysEx : Sys (ZMod 4 × ZMod 4) (ZMod 2 → ℂ) where
  c x y := e (x.1 * y.2 - y.1 * x.2)
  rho := rhoEx
  B := BEx
  c_add_left x x' y := by rw [← e_add]; congr 1; simp; ring
  c_add_right x y y' := by rw [← e_add]; congr 1; simp; ring
  c_self x := by rw [sub_self, e_zero]
  c_norm x y := e_norm _
  rho_zero v := by
    ext t
    have : red 0 = 0 := by decide
    simp [rhoEx, e_zero, this]
  rho_rho x y v := by
    ext t
    simp only [rhoEx, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add,
      red_add, dbl_add, ← mul_assoc, ← e_add, add_assoc]
    congr 2
    ring
  B_conj u v := by simp [BEx_apply]; ring
  B_pos v hv := by
    rw [BEx_apply, Complex.conj_mul', Complex.conj_mul']
    have : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra hh
      push Not at hh
      apply hv
      ext t
      rcases zmod2 t with rfl | rfl
      · exact hh.1
      · exact hh.2
    norm_cast
    rcases this with h | h
    · have := norm_pos_iff.2 h; positivity
    · have := norm_pos_iff.2 h; positivity
  B_rho x u v := by
    simp only [BEx_apply, rhoEx, LinearMap.coe_mk, AddHom.coe_mk, map_mul]
    have h0 := e_conj (x.1 * x.2 + x.2 * dbl 0)
    have h1 := e_conj (x.1 * x.2 + x.2 * dbl 1)
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases zmod2 (red x.1) with h | h <;> rw [h]
    · simp only [add_zero]
      linear_combination ((starRingEnd ℂ) (u 0) * v 0) * h0 + ((starRingEnd ℂ) (u 1) * v 1) * h1
    · simp only [zero_add, h11]
      linear_combination ((starRingEnd ℂ) (u 1) * v 1) * h0 + ((starRingEnd ℂ) (u 0) * v 0) * h1

def G₁ : AddSubgroup (ZMod 4 × ZMod 4) where
  carrier := {x | 2 * x.2 = 0}
  add_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq, Prod.snd_add] at *; rw [mul_add, hx, hy, add_zero]
  zero_mem' := by simp
  neg_mem' := by intro x hx; simp only [Set.mem_setOf_eq, Prod.snd_neg] at *; rw [mul_neg, hx, neg_zero]

def G₂ : AddSubgroup (ZMod 4 × ZMod 4) where
  carrier := {x | 2 * x.1 = 0}
  add_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq, Prod.fst_add] at *; rw [mul_add, hx, hy, add_zero]
  zero_mem' := by simp
  neg_mem' := by intro x hx; simp only [Set.mem_setOf_eq, Prod.fst_neg] at *; rw [mul_neg, hx, neg_zero]

theorem mem_G₁ (x : ZMod 4 × ZMod 4) : x ∈ G₁ ↔ 2 * x.2 = 0 := Iff.rfl

theorem mem_G₂ (x : ZMod 4 × ZMod 4) : x ∈ G₂ ↔ 2 * x.1 = 0 := Iff.rfl

def alEx (x : ZMod 4 × ZMod 4) : ℂ := e (x.1 * x.2)

theorem selfDual_G₁ : SelfDual sysEx G₁ := by
  intro x
  simp only [mem_G₁, sysEx, e_sq]
  revert x; decide

theorem selfDual_G₂ : SelfDual sysEx G₂ := by
  intro x
  simp only [mem_G₂, sysEx, e_sq]
  revert x; decide

theorem isSemi_G₁ : IsSemi sysEx alEx G₁ := by
  refine ⟨fun x hx => e_eq_one _ ?_, fun x hx y hy => ?_⟩
  · rw [mem_G₁] at hx; linear_combination x.1 * hx
  · simp only [alEx, sysEx, ← e_add, Prod.fst_add, Prod.snd_add]
    congr 1
    rw [mem_G₁] at hx; linear_combination y.1 * hx

theorem isSemi_G₂ : IsSemi sysEx alEx G₂ := by
  refine ⟨fun x hx => e_eq_one _ ?_, fun x hx y hy => ?_⟩
  · rw [mem_G₂] at hx; linear_combination x.2 * hx
  · simp only [alEx, sysEx, ← e_add, Prod.fst_add, Prod.snd_add]
    congr 1
    rw [mem_G₂] at hy; linear_combination x.2 * hy

theorem alEx_nontrivial : ((1, 2) : ZMod 4 × ZMod 4) ∈ G₁ ∧ alEx (1, 2) = -1 ∧ alEx (1, 0) = 1 ∧ alEx (0, 2) = 1 := by
  refine ⟨by rw [mem_G₁]; decide, ?_, ?_, ?_⟩ <;> simp [alEx, e_two, e_zero]

def vac : ZMod 2 → ℂ := fun t => if t = 0 then 1 else 0

theorem unitVac_vac : UnitVac sysEx alEx G₂ vac := by
  refine ⟨fun g hg => ?_, ?_⟩
  · rw [isSemi_G₂.inv_eq hg]
    rw [mem_G₂] at hg
    have h : red g.1 = 0 := by
      generalize g.1 = a at hg
      revert a; decide
    have d0 : dbl 0 = 0 := by decide
    ext t
    rcases zmod2 t with rfl | rfl <;> simp [sysEx, rhoEx, vac, h, d0, alEx]
  · simp [sysEx, BEx_apply, vac]

theorem cyclic_vac : Cyclic sysEx vac := by
  unfold Cyclic
  rw [eq_top_iff]
  intro f _
  have r0 : red 0 = 0 := by decide
  have r1 : red 1 = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have : f = f 0 • sysEx.rho (0, 0) vac + f 1 • sysEx.rho (1, 0) vac := by
    ext t
    rcases zmod2 t with rfl | rfl <;> simp [sysEx, rhoEx, vac, r0, r1, h11, e_zero]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem relIndex_ex : G₂.relIndex G₁ = 2 := by
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_two_iff]
  refine ⟨⟨(1, 0), by rw [mem_G₁]; decide⟩, ?_⟩
  rintro ⟨⟨a, b⟩, hb⟩
  simp only [AddSubgroup.mem_addSubgroupOf, mem_G₂, AddSubgroup.coe_add, Prod.fst_add, Xor']
  clear hb
  revert a; decide

def shear : (ZMod 4 × ZMod 4) ≃+ (ZMod 4 × ZMod 4) where
  toFun x := (x.1, x.2 + x.1)
  invFun x := (x.1, x.2 - x.1)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by ext <;> simp; ring

def ph (t : ZMod 2) : ZMod 4 := -(t.val : ZMod 4)

def TEx : (ZMod 2 → ℂ) →ₗ[ℂ] (ZMod 2 → ℂ) where
  toFun f t := e (ph t) * f t
  map_add' f g := by ext t; simp [mul_add]
  map_smul' a f := by ext t; simp; ring

theorem implements_ex : Implements sysEx shear TEx := by
  refine ⟨fun x v => ?_, fun u v => ?_⟩
  · ext t
    obtain ⟨a, b⟩ := x
    show e (ph t) * (e (a * b + b * dbl t) * v (t + red a))
      = e (a * (b + a) + (b + a) * dbl t) * (e (ph (t + red a)) * v (t + red a))
    rw [← mul_assoc, ← mul_assoc, ← e_add, ← e_add]
    congr 2
    revert a b t; decide
  · show BEx _ _ = BEx _ _
    simp only [BEx_apply, TEx, LinearMap.coe_mk, AddHom.coe_mk, map_mul]
    linear_combination ((starRingEnd ℂ) (u 0) * v 0) * e_conj (ph 0) + ((starRingEnd ℂ) (u 1) * v 1) * e_conj (ph 1)

theorem Lam_vac : abelian₂ sysEx alEx G₁ G₂ vac = fun _ => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  have hN : G₂.relIndex G₁ ≠ 0 := by rw [relIndex_ex]; norm_num
  have : Finite (G₁ ⧸ G₂.addSubgroupOf G₁) := Nat.finite_of_card_ne_zero hN
  letI : Fintype (G₁ ⧸ G₂.addSubgroupOf G₁) := Fintype.ofFinite _
  let a : G₁ := ⟨(1, 0), by rw [mem_G₁]; decide⟩
  have ha : (QuotientAddGroup.mk a : G₁ ⧸ G₂.addSubgroupOf G₁) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, mem_G₂]
    decide
  have hall : ∀ q : G₁ ⧸ G₂.addSubgroupOf G₁, q = 0 ∨ q = QuotientAddGroup.mk a := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H z =>
      obtain ⟨⟨x, y⟩, hz⟩ := z
      rw [QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf,
        AddSubgroup.mem_addSubgroupOf, mem_G₂, mem_G₂]
      show 2 * x = 0 ∨ 2 * (-x + 1) = 0
      clear hz
      revert x; decide
  classical
  have hu : (Finset.univ : Finset (G₁ ⧸ G₂.addSubgroupOf G₁)) = {0, QuotientAddGroup.mk a} := by
    ext q; simpa using hall q
  rw [abelian₂, relIndex_ex, la_eq_sum isSemi_G₁ unitVac_vac.1 (fun q => if q = 0 then 0 else a)
    (fun q => by rcases hall q with rfl | rfl <;> simp [ha]), hu, Finset.sum_pair ha.symm]
  have r0 : red 0 = 0 := by decide
  have r1 : red 1 = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  funext t
  rcases zmod2 t with rfl | rfl <;> simp [ha, a, sysEx, rhoEx, vac, alEx, r0, r1, h11, e_zero]

example : sysEx.c (1, 0) (0, 1) ^ 2 = -1 := by simp [sysEx, e_one]

example : ip sysEx (Complex.I • vac) vac = Complex.I ∧ sysEx.B (Complex.I • vac) vac = -Complex.I := by
  have h := unitVac_vac.2
  constructor
  · rw [ip_smul_left, ip_apply, h, mul_one]
  · rw [← ip_apply, ip_smul_right, ip_apply, h]; simp

example : ip sysEx (abelian₂ sysEx alEx G₁ G₂ vac) vac = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [Lam_vac]; simp [sysEx, BEx_apply, vac]

end Inh

end GlobalTheory.CompanionTheory.FinHeis
