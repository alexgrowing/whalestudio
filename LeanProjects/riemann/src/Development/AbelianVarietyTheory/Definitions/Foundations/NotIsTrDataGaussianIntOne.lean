import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

noncomputable section

namespace GlobalTheory.AlmostEt

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

structure IsDerOn (B : Subalgebra A S) (D : S → M) : Prop where
  add : ∀ x ∈ B, ∀ y ∈ B, D (x + y) = D x + D y
  mul : ∀ x ∈ B, ∀ y ∈ B, D (x * y) = x • D y + y • D x
  alg : ∀ a : A, D (algebraMap A S a) = 0

structure IsTrData (B C : Subalgebra A S) (tr : S → S) {n : ℕ} (a b : Fin n → S) (e : S) : Prop where
  le : B ≤ C
  e_mem : e ∈ B
  a_mem : ∀ i, a i ∈ C
  b_mem : ∀ i, b i ∈ C
  tr_mem : ∀ x ∈ C, tr x ∈ B
  tr_add : ∀ x ∈ C, ∀ y ∈ C, tr (x + y) = tr x + tr y
  tr_mul : ∀ β ∈ B, ∀ x ∈ C, tr (β * x) = β * tr x
  left : ∀ x ∈ C, ∑ i, a i * tr (b i * x) = e * x
  right : ∀ x ∈ C, ∑ i, b i * tr (a i * x) = e * x
  sum : ∑ i, a i * b i = e

end General

section Tower

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem qq_pow (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  induction n with
  | zero => simpa using T.q0
  | succ n ih => rw [pow_succ', pow_mul, T.qpow, ih]

def zS (T : Tower p Ω) (n : ℕ) : integralClosure (O0 p) Ω :=
  ⟨T.ζ n, IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) (by
    rw [(T.prim n).pow_eq_one]; exact isIntegral_one)⟩

def qS (T : Tower p Ω) (n : ℕ) : integralClosure (O0 p) Ω :=
  ⟨T.qq n, IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) (by
    rw [qq_pow]; exact isIntegral_algebraMap)⟩

def levelAlg (T : Tower p Ω) (n : ℕ) : Subalgebra (O0 p) (integralClosure (O0 p) Ω) :=
  Algebra.adjoin (O0 p) {zS T n, qS T n}

def towerAlg (T : Tower p Ω) : Subalgebra (O0 p) (integralClosure (O0 p) Ω) :=
  Algebra.adjoin (O0 p) (Set.range (zS T) ∪ Set.range (qS T))

abbrev Frac (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] : Type _ :=
  Ω ⧸ LinearMap.range (Algebra.linearMap (integralClosure (O0 p) Ω) Ω)

end Tower

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt.Inhab

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

theorem isDerOn_derivation [Module A M] (D : Derivation A S M) (B : Subalgebra A S) :
    IsDerOn B (D : S → M) :=
  ⟨fun x _ y _ => D.map_add x y, fun x _ y _ => D.leibniz x y, fun a => D.map_algebraMap a⟩

theorem isDerOn_zero (B : Subalgebra A S) : IsDerOn B (fun _ : S => (0 : M)) :=
  ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ => rfl⟩

theorem isDerOn_mono {B C : Subalgebra A S} (h : B ≤ C) {D : S → M} (hD : IsDerOn C D) :
    IsDerOn B D :=
  ⟨fun x hx y hy => hD.add x (h hx) y (h hy), fun x hx y hy => hD.mul x (h hx) y (h hy), hD.alg⟩

theorem isDerOn_algebraMap_mul {B : Subalgebra A S} {D : S → M} (hD : IsDerOn B D) (a : A)
    {x : S} (hx : x ∈ B) : D (algebraMap A S a * x) = algebraMap A S a • D x := by
  rw [hD.mul _ (B.algebraMap_mem a) x hx, hD.alg, smul_zero, add_zero]

theorem isTrData_self (B : Subalgebra A S) :
    IsTrData B B id (fun _ : Fin 1 => (1 : S)) (fun _ => 1) 1 where
  le := le_rfl
  e_mem := B.one_mem
  a_mem := fun _ => B.one_mem
  b_mem := fun _ => B.one_mem
  tr_mem := fun _ hx => hx
  tr_add := fun _ _ _ _ => rfl
  tr_mul := fun _ _ _ _ => rfl
  left := fun _ _ => by simp
  right := fun _ _ => by simp
  sum := by simp

theorem isTrData_symm {B C : Subalgebra A S} {tr : S → S} {n : ℕ} {a b : Fin n → S} {e : S}
    (h : IsTrData B C tr a b e) : IsTrData B C tr b a e :=
  { h with
    a_mem := h.b_mem
    b_mem := h.a_mem
    left := h.right
    right := h.left
    sum := by rw [← h.sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _ }

end General

section Examples

theorem isDerOn_derivative :
    IsDerOn (⊤ : Subalgebra ℚ (Polynomial ℚ))
      (Polynomial.derivative : Polynomial ℚ → Polynomial ℚ) ∧
    Polynomial.derivative (Polynomial.X : Polynomial ℚ) = 1 :=
  ⟨isDerOn_derivation (Polynomial.derivative' : Derivation ℚ (Polynomial ℚ) (Polynomial ℚ)) ⊤,
    Polynomial.derivative_X⟩

theorem not_isDerOn_id :
    ¬ IsDerOn (⊤ : Subalgebra ℚ (Polynomial ℚ)) (id : Polynomial ℚ → Polynomial ℚ) := by
  intro h
  simpa using h.alg 1

theorem isTrData_prod :
    IsTrData (⊥ : Subalgebra ℤ (ℤ × ℤ)) ⊤ (fun x => (x.1 + x.2, x.1 + x.2))
      ![((1 : ℤ), (0 : ℤ)), (0, 1)] ![((1 : ℤ), (0 : ℤ)), (0, 1)] 1 where
  le := bot_le
  e_mem := Subalgebra.one_mem _
  a_mem := fun _ => trivial
  b_mem := fun _ => trivial
  tr_mem := fun x _ => by
    rw [Algebra.mem_bot]; exact ⟨x.1 + x.2, by ext <;> simp⟩
  tr_add := fun x _ y _ => by ext <;> simp <;> ring
  tr_mul := fun β hβ x _ => by
    rw [Algebra.mem_bot] at hβ; obtain ⟨n, rfl⟩ := hβ
    ext <;> simp <;> ring
  left := fun x _ => by ext <;> simp [Fin.sum_univ_two]
  right := fun x _ => by ext <;> simp [Fin.sum_univ_two]
  sum := by ext <;> simp [Fin.sum_univ_two]

theorem isTrData_gaussianInt :
    IsTrData (⊥ : Subalgebra ℤ GaussianInt) ⊤ (fun x => x + star x)
      ![1, ⟨0, 1⟩] ![1, ⟨0, -1⟩] 2 where
  le := bot_le
  e_mem := by rw [Algebra.mem_bot]; exact ⟨2, by simp⟩
  a_mem := fun _ => trivial
  b_mem := fun _ => trivial
  tr_mem := fun x _ => by
    rw [Algebra.mem_bot]; exact ⟨2 * x.re, by ext <;> simp <;> ring⟩
  tr_add := fun x _ y _ => by rw [star_add]; ring
  tr_mul := fun β hβ x _ => by
    rw [Algebra.mem_bot] at hβ; obtain ⟨n, rfl⟩ := hβ
    ext <;> simp <;> ring
  left := fun x _ => by ext <;> simp [Fin.sum_univ_two] <;> ring
  right := fun x _ => by ext <;> simp [Fin.sum_univ_two] <;> ring
  sum := by ext <;> simp [Fin.sum_univ_two]

theorem bot_ne_top_gaussianInt : (⊥ : Subalgebra ℤ GaussianInt) ≠ ⊤ := by
  intro h
  have hi : (⟨0, 1⟩ : GaussianInt) ∈ (⊥ : Subalgebra ℤ GaussianInt) := h ▸ trivial
  rw [Algebra.mem_bot] at hi
  obtain ⟨n, hn⟩ := hi
  simpa using congrArg Zsqrtd.im hn

theorem not_isTrData_gaussianInt_one {n : ℕ} (a b : Fin n → GaussianInt) :
    ¬ IsTrData (⊥ : Subalgebra ℤ GaussianInt) ⊤ (fun x => x + star x) a b 1 := by
  intro h
  have h1 := h.left 1 trivial
  have h2 : (2 : GaussianInt) ∣ 1 * 1 := by
    rw [← h1]
    refine Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (Dvd.intro (((b i * 1).re : ℤ) : GaussianInt) ?_) _
    ext <;> simp <;> ring
  obtain ⟨c, hc⟩ := h2
  have := congrArg Zsqrtd.re hc
  simp at this
  omega

end Examples

section Tower

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem coe_zS (T : Tower p Ω) (n : ℕ) : (zS T n : Ω) = T.ζ n := rfl

theorem coe_qS (T : Tower p Ω) (n : ℕ) : (qS T n : Ω) = T.qq n := rfl

theorem zS_succ_pow (T : Tower p Ω) (n : ℕ) : zS T (n + 1) ^ p = zS T n :=
  Subtype.ext (T.ζpow n)

theorem qS_succ_pow (T : Tower p Ω) (n : ℕ) : qS T (n + 1) ^ p = qS T n :=
  Subtype.ext (T.qpow n)

theorem zS_mem (T : Tower p Ω) (n : ℕ) : zS T n ∈ levelAlg T n :=
  Algebra.subset_adjoin (by simp)

theorem qS_mem (T : Tower p Ω) (n : ℕ) : qS T n ∈ levelAlg T n :=
  Algebra.subset_adjoin (by simp)

theorem levelAlg_mono (T : Tower p Ω) : Monotone (levelAlg T) := by
  refine monotone_nat_of_le_succ fun n => Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · rw [← zS_succ_pow]; exact Subalgebra.pow_mem _ (zS_mem T _) _
  · rw [← qS_succ_pow]; exact Subalgebra.pow_mem _ (qS_mem T _) _

theorem towerAlg_eq_iSup (T : Tower p Ω) : towerAlg T = ⨆ n, levelAlg T n := by
  refine le_antisymm (Algebra.adjoin_le ?_) (iSup_le fun n => Algebra.adjoin_mono ?_)
  · rintro x (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · exact le_iSup (levelAlg T) n (zS_mem T n)
    · exact le_iSup (levelAlg T) n (qS_mem T n)
  · rintro x (rfl | rfl)
    · exact Or.inl ⟨n, rfl⟩
    · exact Or.inr ⟨n, rfl⟩

theorem frac_mk_eq_zero_iff (x : Ω) :
    (Submodule.Quotient.mk x : Frac p Ω) = 0 ↔ IsInt p x := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem frac_mk_inv_p_ne_zero (h : IsClo p Ω) :
    (Submodule.Quotient.mk ((p : Ω)⁻¹) : Frac p Ω) ≠ 0 := by
  haveI := GlobalTheory.K5.Basic.charZero_of_isClo h
  rw [Ne, frac_mk_eq_zero_iff]
  intro hi
  refine GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero ⟨_, hi, ?_⟩
  rw [pow_one, mul_inv_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero), sub_zero]

end Tower

end GlobalTheory.AlmostEt.Inhab
