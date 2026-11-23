import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne

noncomputable section

namespace GlobalTheory.AlmostEt

variable {A S M : Type} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

def trTwist (tr : S → S) {n : ℕ} (a b : Fin n → S) (D : S → M) (x : S) : M :=
  ∑ i, a i • D (tr (b i * x))

def trTwistDefect (tr : S → S) {n : ℕ} (a b : Fin n → S) (D : S → M) (x u : S) : M :=
  trTwist tr a b D (x * u) - x • trTwist tr a b D u

def trExtDer (tr : S → S) {n : ℕ} (a b : Fin n → S) (e : S) (D : S → M) (y : S) : M :=
  e • ∑ j, b j • trTwistDefect tr a b D y (a j)

variable {B C : Subalgebra A S} {tr : S → S} {n : ℕ} {a b : Fin n → S} {e : S} {D : S → M}

theorem trTwist_add (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x y : S} (hx : x ∈ C)
    (hy : y ∈ C) : trTwist tr a b D (x + y) = trTwist tr a b D x + trTwist tr a b D y := by
  unfold trTwist
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := C.mul_mem (h.b_mem i) hx
  have h2 := C.mul_mem (h.b_mem i) hy
  rw [mul_add, h.tr_add _ h1 _ h2, hD.add _ (h.tr_mem _ h1) _ (h.tr_mem _ h2), smul_add]

theorem trTwist_smul (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {β x : S} (hβ : β ∈ B)
    (hx : x ∈ C) : trTwist tr a b D (β * x) = β • trTwist tr a b D x + (e * x) • D β := by
  unfold trTwist
  have key : ∀ i, a i • D (tr (b i * (β * x))) =
      β • (a i • D (tr (b i * x))) + (a i * tr (b i * x)) • D β := by
    intro i
    have h1 := C.mul_mem (h.b_mem i) hx
    have hm : b i * (β * x) = β * (b i * x) := by ring
    rw [hm, h.tr_mul _ hβ _ h1, hD.mul _ hβ _ (h.tr_mem _ h1), smul_add, mul_smul, smul_comm (a i) β]
  simp_rw [key, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul, h.left x hx]

theorem trTwist_zero (h : IsTrData B C tr a b e) (hD : IsDerOn B D) :
    trTwist tr a b D (0 : S) = 0 := by
  have := trTwist_add h hD C.zero_mem C.zero_mem
  rw [add_zero] at this
  simpa using this

theorem defect_add (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x u v : S} (hx : x ∈ C)
    (hu : u ∈ C) (hv : v ∈ C) :
    trTwistDefect tr a b D x (u + v) = trTwistDefect tr a b D x u + trTwistDefect tr a b D x v := by
  unfold trTwistDefect
  rw [mul_add, trTwist_add h hD (C.mul_mem hx hu) (C.mul_mem hx hv), trTwist_add h hD hu hv, smul_add]
  abel

theorem defect_zero (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x : S} (hx : x ∈ C) :
    trTwistDefect tr a b D x 0 = 0 := by
  unfold trTwistDefect
  rw [mul_zero, trTwist_zero h hD, smul_zero, sub_zero]

theorem defect_smul (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x β u : S} (hx : x ∈ C)
    (hβ : β ∈ B) (hu : u ∈ C) :
    trTwistDefect tr a b D x (β * u) = β • trTwistDefect tr a b D x u := by
  unfold trTwistDefect
  have hm : x * (β * u) = β * (x * u) := by ring
  rw [hm, trTwist_smul h hD hβ (C.mul_mem hx hu), trTwist_smul h hD hβ hu, smul_add, smul_sub,
    smul_smul x (e * u), smul_comm x β]
  have : x * (e * u) = e * (x * u) := by ring
  rw [this]
  abel

theorem defect_sum (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x : S} (hx : x ∈ C)
    (c : Fin n → S) (hc : ∀ i, c i ∈ B) :
    trTwistDefect tr a b D x (∑ i, c i * a i) = ∑ i, c i • trTwistDefect tr a b D x (a i) := by
  have : ∀ s : Finset (Fin n), trTwistDefect tr a b D x (∑ i ∈ s, c i * a i) =
      ∑ i ∈ s, c i • trTwistDefect tr a b D x (a i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using defect_zero h hD hx
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        defect_add h hD hx (C.mul_mem (h.le (hc j)) (h.a_mem j))
          (C.sum_mem fun i _ => C.mul_mem (h.le (hc i)) (h.a_mem i)),
        defect_smul h hD hx (hc j) (h.a_mem j), ih]
  exact this Finset.univ

theorem defect_mul (x y u : S) :
    trTwistDefect tr a b D (x * y) u =
      trTwistDefect tr a b D x (y * u) + x • trTwistDefect tr a b D y u := by
  unfold trTwistDefect
  rw [smul_sub, mul_assoc, mul_smul]
  abel

theorem trExtDer_swap (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x y : S} (hx : x ∈ C)
    (hy : y ∈ C) : y • trExtDer tr a b e D x =
      e • ∑ j, b j • trTwistDefect tr a b D x (y * a j) := by

  have step1 : ∀ j, e • (b j • trTwistDefect tr a b D x (y * a j)) =
      ∑ i, (tr (b i * (y * a j)) * b j) • trTwistDefect tr a b D x (a i) := by
    intro j
    have hya := C.mul_mem hy (h.a_mem j)
    have hl : e * (y * a j) = ∑ i, tr (b i * (y * a j)) * a i := by
      rw [← h.left _ hya]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [smul_comm, ← defect_smul h hD hx h.e_mem hya, hl,
      defect_sum h hD hx _ fun i => h.tr_mem _ (C.mul_mem (h.b_mem i) hya), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm (b j)]
  rw [Finset.smul_sum]
  simp_rw [step1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hr : ∀ i, ∑ j, tr (b i * (y * a j)) * b j = y • (e • b i) := by
    intro i
    have := h.right _ (C.mul_mem (h.b_mem i) hy)
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm y e, mul_assoc, mul_comm y (b i), ← this]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]; congr 2; ring
  simp_rw [hr]
  unfold trExtDer
  rw [Finset.smul_sum, Finset.smul_sum]
  simp_rw [smul_smul, smul_eq_mul, mul_assoc]

theorem trExtDer_isDerOn (h : IsTrData B C tr a b e) (hD : IsDerOn B D) :
    IsDerOn C (trExtDer tr a b e D) where
  add x hx y hy := by
    unfold trExtDer
    rw [← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold trTwistDefect
    rw [← smul_add, add_mul, trTwist_add h hD (C.mul_mem hx (h.a_mem j)) (C.mul_mem hy (h.a_mem j)),
      add_smul]
    congr 1
    abel
  mul x hx y hy := by
    have e1 : trExtDer tr a b e D (x * y) =
        e • ∑ j, b j • trTwistDefect tr a b D x (y * a j) + x • trExtDer tr a b e D y := by
      unfold trExtDer
      simp_rw [defect_mul, smul_add, Finset.sum_add_distrib, smul_add]
      congr 1
      rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_comm (b j) x, smul_comm e x]
    rw [e1, ← trExtDer_swap h hD hx hy, add_comm]
  alg c := by
    unfold trExtDer
    have hc : algebraMap A S c ∈ B := B.algebraMap_mem c
    have : ∀ j, b j • trTwistDefect tr a b D (algebraMap A S c) (a j) =
        (b j * (e * a j)) • D (algebraMap A S c) := by
      intro j
      unfold trTwistDefect
      rw [trTwist_smul h hD hc (h.a_mem j), add_sub_cancel_left, smul_smul]
    simp [this, hD.alg c]

theorem trExtDer_apply_of_mem (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {β : S} (hβ : β ∈ B) :
    trExtDer tr a b e D β = (e ^ 3) • D β := by
  unfold trExtDer
  have : ∀ j, b j • trTwistDefect tr a b D β (a j) = (b j * (e * a j)) • D β := by
    intro j
    unfold trTwistDefect
    rw [trTwist_smul h hD hβ (h.a_mem j), add_sub_cancel_left, smul_smul]
  simp_rw [this, ← Finset.sum_smul, smul_smul]
  have hs : ∑ j, b j * (e * a j) = e * e := by
    rw [← h.sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]; congr 1; ring

theorem exists_derOn_ext : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn B D →
      ∃ D' : S → M, IsDerOn C D' ∧ ∀ β ∈ B, D' β = (e ^ 3) • D β := by
  intro A S M _ _ _ _ _ B C tr n a b e h D hD
  exact ⟨trExtDer tr a b e D, trExtDer_isDerOn h hD, fun β hβ => trExtDer_apply_of_mem h hD hβ⟩

end GlobalTheory.AlmostEt
