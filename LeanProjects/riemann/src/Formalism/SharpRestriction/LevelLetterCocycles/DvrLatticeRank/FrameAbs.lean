import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaO
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaJ
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaI
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaB

namespace DualFramesAlt.FrameAbs

open Matrix

variable {A : Type*} [CommRing A] {d : ℕ}

def MatIn (I : Ideal A) (H : Matrix (Fin d) (Fin d) A) : Prop := by
  first | exact @Bl.FirstLemmaO.goal1 A ‹_› d I H | exact @Bl.FirstLemmaO.goal1 A ‹_› d I | exact @Bl.FirstLemmaO.goal1 A ‹_› d | exact @Bl.FirstLemmaO.goal1 A ‹_› | exact @Bl.FirstLemmaO.goal1 A | exact @Bl.FirstLemmaO.goal1

def IsFrame (σ : A →+* A) (Γ : Matrix (Fin d) (Fin d) A) (π c : A) (M : ℕ)
    (H : Matrix (Fin d) (Fin d) A) : Prop :=
  MatIn (Ideal.span {π}) (H - c • (1 : Matrix (Fin d) (Fin d) A)) ∧
    MatIn (Ideal.span {π ^ M}) (Γ * H.map σ - H)

def IsDualFrame (σ : A →+* A) (Γ : Matrix (Fin d) (Fin d) A) (π c : A) (M : ℕ)
    (F : Matrix (Fin d) (Fin d) A) : Prop :=
  MatIn (Ideal.span {π}) (F - c • (1 : Matrix (Fin d) (Fin d) A)) ∧
    MatIn (Ideal.span {π ^ M}) (F * Γ - F.map σ)

structure Hyp (O : Type*) [CommRing O] [Algebra O A] (σ : A →+* A) (Γ : Matrix (Fin d) (Fin d) A)
    (π : A) (ev : ℕ → A) : Prop where
  hσ : ∀ a : A, σ a - a ∈ (Ideal.span {π} : Ideal A)
  hΓ : MatIn (Ideal.span {π}) (Γ - 1)
  hΓunit : IsUnit Γ.det
  hπ : π ∈ nonZeroDivisors A
  hσπ : ∀ y : ℕ, σ (π ^ y) - (ev y + 1) * π ^ y ∈ (Ideal.span {π ^ (y + 1)} : Ideal A)
  hσev : ∀ y : ℕ, σ (ev y) = ev y
  hnzd : ∀ (y : ℕ) (a : A), 1 ≤ y → ev y * a ∈ (Ideal.span {π} : Ideal A) → a ∈ (Ideal.span {π} : Ideal A)
  hO : ∀ o : O, σ (algebraMap O A o) = algebraMap O A o
  hdec : ∀ a : A, ∃ o : O, a - algebraMap O A o ∈ (Ideal.span {π} : Ideal A)
  hinj : ∀ o : O, algebraMap O A o ∈ (Ideal.span {π} : Ideal A) → o = 0
  hev : ∀ y : ℕ, ∃ o : O, ev y = algebraMap O A o

section SlopeTestRemainingChoices

variable {I J : Ideal A} {X Y : Matrix (Fin d) (Fin d) A}

theorem MatIn.zero : MatIn I (0 : Matrix (Fin d) (Fin d) A) := fun _ _ => I.zero_mem

theorem MatIn.add (hX : MatIn I X) (hY : MatIn I Y) : MatIn I (X + Y) :=
  fun i j => I.add_mem (hX i j) (hY i j)

theorem MatIn.neg (hX : MatIn I X) : MatIn I (-X) := fun i j => I.neg_mem (hX i j)

theorem MatIn.sub (hX : MatIn I X) (hY : MatIn I Y) : MatIn I (X - Y) :=
  fun i j => I.sub_mem (hX i j) (hY i j)

theorem MatIn.mul_left (hY : MatIn I Y) : MatIn I (X * Y) := fun i j => by
  rw [Matrix.mul_apply]; exact I.sum_mem fun k _ => I.mul_mem_left _ (hY k j)

theorem MatIn.mul_right (hX : MatIn I X) : MatIn I (X * Y) := fun i j => by
  rw [Matrix.mul_apply]; exact I.sum_mem fun k _ => I.mul_mem_right _ (hX i k)

theorem MatIn.smul (hX : MatIn I X) (a : A) : MatIn I (a • X) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact I.mul_mem_left a (hX i j)

theorem MatIn.mono (hIJ : I ≤ J) (hX : MatIn I X) : MatIn J X := fun i j => hIJ (hX i j)

theorem MatIn.transpose (hX : MatIn I X) : MatIn I Xᵀ := fun i j => hX j i

theorem MatIn.exists_smul {p : A} (h : MatIn (Ideal.span {p}) X) :
    ∃ K : Matrix (Fin d) (Fin d) A, X = p • K := by
  choose K hK using fun i j => Ideal.mem_span_singleton'.mp (h i j)
  refine ⟨Matrix.of K, ?_⟩
  ext i j
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact (hK i j).symm.trans (mul_comm _ _)

theorem MatIn.smul_self (p : A) (K : Matrix (Fin d) (Fin d) A) : MatIn (Ideal.span {p}) (p • K) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self p)

theorem matIn_sub_iff : MatIn I (X - Y) ↔ X.map (Ideal.Quotient.mk I) = Y.map (Ideal.Quotient.mk I) := by
  constructor
  · intro h
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq]
    exact h i j
  · intro h i j
    have := congr_fun (congr_fun h i) j
    rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq] at this
    exact this

theorem span_pow_mono (π : A) {m n : ℕ} (h : m ≤ n) :
    Ideal.span {π ^ n} ≤ Ideal.span ({π ^ m} : Set A) :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π h)

theorem span_pow_le (π : A) {n : ℕ} (h : 1 ≤ n) : Ideal.span {π ^ n} ≤ Ideal.span ({π} : Set A) :=
  Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self π (by omega))

theorem map_smul_ring (σ : A →+* A) (a : A) (X : Matrix (Fin d) (Fin d) A) :
    (a • X).map σ = σ a • X.map σ := by
  first | exact Bl.MatrixMapSmul.goal1 .. | (apply Bl.MatrixMapSmul.goal1 <;> assumption) | (intros; apply Bl.MatrixMapSmul.goal1 <;> assumption) | (apply @Bl.MatrixMapSmul.goal1 <;> assumption) | (intros; apply @Bl.MatrixMapSmul.goal1 <;> assumption) | (apply @Bl.MatrixMapSmul.goal1 <;> first | assumption | infer_instance) | exact @Bl.MatrixMapSmul.goal1 A ‹_› d σ a X | exact @Bl.MatrixMapSmul.goal1 A ‹_› d σ a | exact @Bl.MatrixMapSmul.goal1 A ‹_› d σ | exact @Bl.MatrixMapSmul.goal1 A ‹_› d | exact @Bl.MatrixMapSmul.goal1 A ‹_› | exact @Bl.MatrixMapSmul.goal1 A

theorem map_sub_ring (σ : A →+* A) (X Y : Matrix (Fin d) (Fin d) A) :
    (X - Y).map σ = X.map σ - Y.map σ := by
  first | exact Bl.MatrixMapSub.goal1 .. | (apply Bl.MatrixMapSub.goal1 <;> assumption) | (intros; apply Bl.MatrixMapSub.goal1 <;> assumption) | (apply @Bl.MatrixMapSub.goal1 <;> assumption) | (intros; apply @Bl.MatrixMapSub.goal1 <;> assumption) | (apply @Bl.MatrixMapSub.goal1 <;> first | assumption | infer_instance) | exact @Bl.MatrixMapSub.goal1 A ‹_› d σ X Y | exact @Bl.MatrixMapSub.goal1 A ‹_› d σ X | exact @Bl.MatrixMapSub.goal1 A ‹_› d σ | exact @Bl.MatrixMapSub.goal1 A ‹_› d | exact @Bl.MatrixMapSub.goal1 A ‹_› | exact @Bl.MatrixMapSub.goal1 A

theorem cancel_pow {π x : A} (hπ : π ∈ nonZeroDivisors A) {y : ℕ}
    (hx : π ^ y * x ∈ Ideal.span ({π ^ (y + 1)} : Set A)) : x ∈ Ideal.span ({π} : Set A) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hx
  have h0 : (x - t * π) * π ^ y = 0 := by linear_combination (-1 : A) * ht
  have h1 := (mem_nonZeroDivisors_iff.mp (pow_mem hπ y)).2 _ h0
  exact Ideal.mem_span_singleton'.mpr ⟨t, (sub_eq_zero.mp h1).symm⟩

end SlopeTestRemainingChoices

section Core

variable {σ : A →+* A} {π : A} {ev : ℕ → A}

theorem scalar_core (hσ : ∀ a : A, σ a - a ∈ (Ideal.span {π} : Ideal A))
    (hσπ : ∀ y : ℕ, σ (π ^ y) - (ev y + 1) * π ^ y ∈ (Ideal.span {π ^ (y + 1)} : Ideal A))
    (y : ℕ) (b : A) : ∃ r : A, σ (π ^ y * b) - π ^ y * b = π ^ y * (ev y * b + π * r) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hσπ y)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (hσ b)
  refine ⟨(ev y + 1) * s + t * b + t * s * π, ?_⟩
  have e1 : σ (π ^ y) = (ev y + 1) * π ^ y + t * π ^ (y + 1) := by rw [ht]; ring
  have e2 : σ b = b + s * π := by rw [hs]; ring
  rw [map_mul, e1, e2]; ring

theorem mat_core {Γ : Matrix (Fin d) (Fin d) A} (hσ : ∀ a : A, σ a - a ∈ (Ideal.span {π} : Ideal A))
    (hΓ : MatIn (Ideal.span {π}) (Γ - 1))
    (hσπ : ∀ y : ℕ, σ (π ^ y) - (ev y + 1) * π ^ y ∈ (Ideal.span {π ^ (y + 1)} : Ideal A))
    (y : ℕ) (U : Matrix (Fin d) (Fin d) A) : ∃ R : Matrix (Fin d) (Fin d) A,
      Γ * (π ^ y • U).map σ - π ^ y • U = π ^ y • (ev y • U + π • R) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hσπ y)
  have hK : MatIn (Ideal.span {π}) (Γ * U.map σ - U) := by
    have e : Γ * U.map σ - U = (Γ - 1) * U.map σ + (U.map σ - U) := by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e]
    refine (MatIn.mul_right hΓ).add (fun i j => ?_)
    rw [Matrix.sub_apply, Matrix.map_apply]
    exact hσ (U i j)
  obtain ⟨K, hK'⟩ := hK.exists_smul
  refine ⟨(ev y + 1) • K + t • U + (π * t) • K, ?_⟩
  have e1 : σ (π ^ y) = (ev y + 1) * π ^ y + t * π ^ (y + 1) := by rw [ht]; ring
  have e2 : Γ * U.map σ = U + π • K := by rw [← hK']; abel
  rw [map_smul_ring, Matrix.mul_smul, e2, e1]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem frame_exists_of_eigenvalues {Γ : Matrix (Fin d) (Fin d) A}
    (hσ : ∀ a : A, σ a - a ∈ (Ideal.span {π} : Ideal A))
    (hΓ : MatIn (Ideal.span {π}) (Γ - 1))
    (hσπ : ∀ y : ℕ, σ (π ^ y) - (ev y + 1) * π ^ y ∈ (Ideal.span {π ^ (y + 1)} : Ideal A))
    (hσev : ∀ y : ℕ, σ (ev y) = ev y) (n : ℕ) (hn : 1 ≤ n) :
    ∃ H : Matrix (Fin d) (Fin d) A,
      MatIn (Ideal.span {π}) (H - (∏ y ∈ Finset.Ico 1 n, ev y) • (1 : Matrix (Fin d) (Fin d) A)) ∧
      MatIn (Ideal.span {π ^ n}) (Γ * H.map σ - H) := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨1, ?_, ?_⟩
    · rw [Finset.Ico_self, Finset.prod_empty, one_smul, sub_self]
      exact MatIn.zero
    · rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.mul_one, pow_one]
      exact hΓ
  | succ n hn ih =>
    obtain ⟨H, h1, h2⟩ := ih
    obtain ⟨W, hW⟩ := h2.exists_smul
    obtain ⟨R, hR⟩ := mat_core hσ hΓ hσπ n W
    refine ⟨ev n • H - π ^ n • W, ?_, ?_⟩
    · rw [Finset.prod_Ico_succ_top hn]
      have e : ev n • H - π ^ n • W - ((∏ y ∈ Finset.Ico 1 n, ev y) * ev n) •
          (1 : Matrix (Fin d) (Fin d) A) =
          ev n • (H - (∏ y ∈ Finset.Ico 1 n, ev y) • (1 : Matrix (Fin d) (Fin d) A)) - π ^ n • W := by
        ext i j
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact (h1.smul _).sub ((MatIn.smul_self _ W).mono (span_pow_le π hn))
    · have hX : Γ * H.map σ = H + π ^ n • W := by rw [← hW]; abel
      have hY : Γ * (π ^ n • W).map σ = π ^ n • W + π ^ n • (ev n • W + π • R) := by
        rw [← hR]; abel
      have e : Γ * (ev n • H - π ^ n • W).map σ - (ev n • H - π ^ n • W) = π ^ (n + 1) • (-R) := by
        rw [map_sub_ring, map_smul_ring, hσev, Matrix.mul_sub, Matrix.mul_smul, hX, hY]
        ext i j
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
        ring
      rw [e]
      exact MatIn.smul_self _ _

theorem frame_unique_of_eigenvalues {Γ : Matrix (Fin d) (Fin d) A}
    (hσ : ∀ a : A, σ a - a ∈ (Ideal.span {π} : Ideal A))
    (hΓ : MatIn (Ideal.span {π}) (Γ - 1)) (hπ : π ∈ nonZeroDivisors A)
    (hσπ : ∀ y : ℕ, σ (π ^ y) - (ev y + 1) * π ^ y ∈ (Ideal.span {π ^ (y + 1)} : Ideal A))
    (hnzd : ∀ (y : ℕ) (a : A), 1 ≤ y → ev y * a ∈ (Ideal.span {π} : Ideal A) →
      a ∈ (Ideal.span {π} : Ideal A))
    (M : ℕ) (hM : 1 ≤ M) (D : Matrix (Fin d) (Fin d) A) (h1 : MatIn (Ideal.span {π}) D)
    (h2 : MatIn (Ideal.span {π ^ M}) (Γ * D.map σ - D)) : MatIn (Ideal.span {π ^ M}) D := by
  suffices key : ∀ n, 1 ≤ n → n ≤ M → MatIn (Ideal.span {π ^ n}) D from key M hM le_rfl
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro _; rw [pow_one]; exact h1
  | succ n hn ih =>
    intro hle
    obtain ⟨U, hU⟩ := (ih (by omega)).exists_smul
    obtain ⟨R, hR⟩ := mat_core hσ hΓ hσπ n U
    have h2' : MatIn (Ideal.span {π ^ (n + 1)}) (π ^ n • (ev n • U + π • R)) := by
      rw [← hR, ← hU]; exact h2.mono (span_pow_mono π hle)
    intro i j
    have e1 := h2' i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at e1
    have e2 := cancel_pow hπ e1
    have e3 : ev n * U i j ∈ (Ideal.span {π} : Ideal A) := by
      have := Ideal.sub_mem _ e2 (Ideal.mul_mem_right (R i j) _ (Ideal.mem_span_singleton_self π))
      rwa [add_sub_cancel_right] at this
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (hnzd n (U i j) hn e3)
    rw [hU, Matrix.smul_apply, smul_eq_mul, ← hs]
    exact Ideal.mem_span_singleton'.mpr ⟨s, by ring⟩

end Core

section Const

variable {O : Type*} [CommRing O] [Algebra O A] {σ : A →+* A} {Γ : Matrix (Fin d) (Fin d) A}
  {π : A} {ev : ℕ → A}

theorem invariants_const (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M) (a : A)
    (ha : σ a - a ∈ (Ideal.span {π ^ M} : Ideal A)) :
    ∃ o : O, a - algebraMap O A o ∈ (Ideal.span {π ^ M} : Ideal A) := by
  obtain ⟨o, ho⟩ := h.hdec a
  refine ⟨o, ?_⟩
  suffices key : ∀ n, 1 ≤ n → n ≤ M → a - algebraMap O A o ∈ (Ideal.span {π ^ n} : Ideal A) from
    key M hM le_rfl
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro _; rw [pow_one]; exact ho
  | succ n hn ih =>
    intro hle
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (ih (by omega))
    obtain ⟨r, hr⟩ := scalar_core h.hσ h.hσπ n b
    have ea : a = algebraMap O A o + π ^ n * b := by linear_combination -hb
    have e : σ a - a = π ^ n * (ev n * b + π * r) := by
      rw [← hr, ea, map_add, h.hO]; ring
    have hin : π ^ n * (ev n * b + π * r) ∈ (Ideal.span {π ^ (n + 1)} : Ideal A) := by
      rw [← e]; exact span_pow_mono π hle ha
    have e2 := cancel_pow h.hπ hin
    have e3 : ev n * b ∈ (Ideal.span {π} : Ideal A) := by
      have := Ideal.sub_mem _ e2 (Ideal.mul_mem_right r _ (Ideal.mem_span_singleton_self π))
      rwa [add_sub_cancel_right] at this
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (h.hnzd n b hn e3)
    exact Ideal.mem_span_singleton'.mpr ⟨s, by rw [← hb, ← hs]; ring⟩

theorem rigid (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M) (a : A) (o' : O)
    (ha : σ a - a ∈ (Ideal.span {π ^ M} : Ideal A))
    (hb : a - algebraMap O A o' ∈ (Ideal.span {π} : Ideal A)) :
    a - algebraMap O A o' ∈ (Ideal.span {π ^ M} : Ideal A) := by
  obtain ⟨o, ho⟩ := invariants_const h M hM a ha
  have hoo : o = o' := by
    apply sub_eq_zero.mp
    apply h.hinj
    have := Ideal.sub_mem _ hb (span_pow_le π hM ho)
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  rw [← hoo]; exact ho

end Const

theorem mul_comm_of_mul_eq_smul {R : Type*} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R)
    (c : R) (hc : c ∈ nonZeroDivisors R) (h : Q * P = c • (1 : Matrix (Fin n) (Fin n) R)) :
    P * Q = c • (1 : Matrix (Fin n) (Fin n) R) := by
  first | exact Bl.FirstLemmaB.goal1 .. | (apply Bl.FirstLemmaB.goal1 <;> assumption) | (intros; apply Bl.FirstLemmaB.goal1 <;> assumption) | (apply @Bl.FirstLemmaB.goal1 <;> assumption) | (intros; apply @Bl.FirstLemmaB.goal1 <;> assumption) | (apply @Bl.FirstLemmaB.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstLemmaB.goal1 R ‹_› n P Q c hc h | exact @Bl.FirstLemmaB.goal1 R ‹_› n P Q c hc | exact @Bl.FirstLemmaB.goal1 R ‹_› n P Q c | exact @Bl.FirstLemmaB.goal1 R ‹_› n P Q | exact @Bl.FirstLemmaB.goal1 R ‹_› n P | exact @Bl.FirstLemmaB.goal1 R ‹_› n | exact @Bl.FirstLemmaB.goal1 R ‹_› | exact @Bl.FirstLemmaB.goal1 R

theorem quot_sq_nzd {I : Ideal A} {c : A} (hc : ∀ a : A, c * a ∈ I → a ∈ I) :
    Ideal.Quotient.mk I (c ^ 2) ∈ nonZeroDivisors (A ⧸ I) := by
  have aux : ∀ x : A ⧸ I, x * Ideal.Quotient.mk I (c ^ 2) = 0 → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem]
    apply hc; apply hc
    convert hx using 1; ring
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => aux x (by rwa [mul_comm]), aux⟩

section Main

variable {O : Type*} [CommRing O] [Algebra O A] {σ : A →+* A} {Γ : Matrix (Fin d) (Fin d) A}
  {π : A} {ev : ℕ → A}

theorem prod_ev_mem (h : Hyp O σ Γ π ev) (M : ℕ) :
    ∃ o : O, (∏ y ∈ Finset.Ico 1 M, ev y) = algebraMap O A o := by
  choose f hf using h.hev
  exact ⟨∏ y ∈ Finset.Ico 1 M, f y, by
    rw [map_prod]; exact Finset.prod_congr rfl fun y _ => hf y⟩

theorem dual_frame_products (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M) (c : A)
    (hcO : ∃ o : O, c = algebraMap O A o) (H F : Matrix (Fin d) (Fin d) A)
    (hH : IsFrame σ Γ π c M H) (hF : IsDualFrame σ Γ π c M F)
    (hc : ∀ a : A, c * a ∈ (Ideal.span {π ^ M} : Ideal A) → a ∈ (Ideal.span {π ^ M} : Ideal A)) :
    MatIn (Ideal.span {π ^ M}) (F * H - c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) ∧
    MatIn (Ideal.span {π ^ M}) (H * F - c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) := by
  have hG1 : MatIn (Ideal.span {π ^ M}) ((F * H).map σ - F * H) := by
    have e : (F * H).map σ - F * H = -(F * Γ - F.map σ) * H.map σ + F * (Γ * H.map σ - H) := by
      rw [Matrix.map_mul, neg_sub]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [e]
    exact (MatIn.mul_right hF.2.neg).add (MatIn.mul_left hH.2)
  have hG2 : MatIn (Ideal.span {π}) (F * H - c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) := by
    have e : F * H - c ^ 2 • (1 : Matrix (Fin d) (Fin d) A) =
        (F - c • (1 : Matrix (Fin d) (Fin d) A)) * H + c • (H - c • (1 : Matrix (Fin d) (Fin d) A)) := by
      simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul, pow_two]
      abel
    rw [e]
    exact (MatIn.mul_right hF.1).add (hH.1.smul c)
  obtain ⟨oc, hoc⟩ := hcO
  have hFH : MatIn (Ideal.span {π ^ M}) (F * H - c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) := by
    intro i j
    obtain ⟨o', ho'⟩ : ∃ o' : O, (c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) i j = algebraMap O A o' := by
      by_cases hij : i = j
      · refine ⟨oc ^ 2, ?_⟩
        subst hij
        rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hoc, map_pow]
      · refine ⟨0, ?_⟩
        rw [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, map_zero]
    rw [Matrix.sub_apply, ho']
    apply rigid h M hM
    · have := hG1 i j
      rwa [Matrix.sub_apply, Matrix.map_apply] at this
    · rw [← ho', ← Matrix.sub_apply]
      exact hG2 i j
  refine ⟨hFH, ?_⟩
  have h1 := matIn_sub_iff.mp hFH
  apply matIn_sub_iff.mpr
  have hsm : (c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)).map (Ideal.Quotient.mk (Ideal.span {π ^ M})) =
      Ideal.Quotient.mk (Ideal.span {π ^ M}) (c ^ 2) • (1 : Matrix (Fin d) (Fin d) _) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [Matrix.map_mul, hsm] at h1 ⊢
  exact mul_comm_of_mul_eq_smul _ _ _ (quot_sq_nzd hc) h1

theorem frame_products {O : Type*} [CommRing O] [Algebra O A] {σ : A →+* A}
    {Γ : Matrix (Fin d) (Fin d) A} {π : A} {ev : ℕ → A} (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M)
    (H F : Matrix (Fin d) (Fin d) A)
    (hH : IsFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M H)
    (hF : IsDualFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M F)
    (hc : ∀ a : A, (∏ y ∈ Finset.Ico 1 M, ev y) * a ∈ (Ideal.span {π ^ M} : Ideal A) →
      a ∈ (Ideal.span {π ^ M} : Ideal A)) :
    MatIn (Ideal.span {π ^ M}) (F * H - (∏ y ∈ Finset.Ico 1 M, ev y) ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) ∧
    MatIn (Ideal.span {π ^ M}) (H * F - (∏ y ∈ Finset.Ico 1 M, ev y) ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) :=
  dual_frame_products h M hM _ (prod_ev_mem h M) H F hH hF hc

theorem exists_frame {O : Type*} [CommRing O] [Algebra O A] {σ : A →+* A}
    {Γ : Matrix (Fin d) (Fin d) A} {π : A} {ev : ℕ → A} (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M) :
    (∃ H, IsFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M H) ∧
    (∀ H H', IsFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M H →
      IsFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M H' → MatIn (Ideal.span {π ^ M}) (H - H')) := by
  refine ⟨frame_exists_of_eigenvalues h.hσ h.hΓ h.hσπ h.hσev M hM, fun H H' hH hH' => ?_⟩
  apply frame_unique_of_eigenvalues h.hσ h.hΓ h.hπ h.hσπ h.hnzd M hM
  · have := hH.1.sub hH'.1
    rwa [sub_sub_sub_cancel_right] at this
  · have e : Γ * (H - H').map σ - (H - H') = (Γ * H.map σ - H) - (Γ * H'.map σ - H') := by
      rw [map_sub_ring, Matrix.mul_sub]; abel
    rw [e]
    exact hH.2.sub hH'.2

theorem exists_dualFrame {O : Type*} [CommRing O] [Algebra O A] {σ : A →+* A}
    {Γ : Matrix (Fin d) (Fin d) A} {π : A} {ev : ℕ → A} (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M) :
    ∃ F, IsDualFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M F := by
  have hinv : Γ⁻¹ * Γ = 1 := Matrix.nonsing_inv_mul Γ h.hΓunit
  have hΓ' : MatIn (Ideal.span {π}) ((Γ⁻¹)ᵀ - 1) := by
    have e : (Γ⁻¹)ᵀ - 1 = (Γ⁻¹ * (-(Γ - 1)))ᵀ := by
      rw [Matrix.mul_neg, Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub, Matrix.transpose_sub,
        Matrix.transpose_one]
    rw [e]
    exact (MatIn.mul_left h.hΓ.neg).transpose
  obtain ⟨H', h1, h2⟩ := frame_exists_of_eigenvalues h.hσ hΓ' h.hσπ h.hσev M hM
  refine ⟨H'ᵀ, ?_, ?_⟩
  · have := h1.transpose
    rwa [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one] at this
  · have hΓΓ : Γᵀ * (Γ⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
    have key : (H'ᵀ * Γ - H'ᵀ.map σ)ᵀ = -(Γᵀ * ((Γ⁻¹)ᵀ * H'.map σ - H')) := by
      rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_map, Matrix.transpose_transpose, Matrix.mul_sub, ← Matrix.mul_assoc, hΓΓ,
        Matrix.one_mul, neg_sub]
    have := ((MatIn.mul_left (X := Γᵀ) h2).neg).transpose
    rwa [← key, Matrix.transpose_transpose] at this

end Main

end DualFramesAlt.FrameAbs
