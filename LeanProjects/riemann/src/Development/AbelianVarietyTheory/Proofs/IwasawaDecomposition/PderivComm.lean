import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators

noncomputable section

namespace GlobalTheory.WeilReal.QuadAlg

open Matrix MvPolynomial
open scoped ComplexConjugate

section Abstract

theorem pderiv_comm' {σ : Type} (i j : σ) (p : MvPolynomial σ ℂ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp =>
    simp only [Derivation.leibniz, pderiv_X, map_add, smul_eq_mul, hp]
    simp only [Pi.single_apply]
    split_ifs <;> simp [Derivation.leibniz] <;> ring

variable {κ σ : Type} [Fintype κ] [DecidableEq κ] [DecidableEq σ]

def wOp (e : κ → σ) (p : κ → Prop) [DecidablePred p] (k : κ) (Q : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  if p k then X (e k) * Q else -pderiv (e k) Q

def vOp (e : κ → σ) (p : κ → Prop) [DecidablePred p] (k : κ) (Q : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  if p k then pderiv (e k) Q else X (e k) * Q

def fc (p : κ → Prop) [DecidablePred p] (k : κ) (c : ℂ) : ℂ := if p k then c else conj c

def mA (p : κ → Prop) [DecidablePred p] (A : Matrix κ κ ℂ) (k l : κ) : ℂ :=
  if (p k ↔ p l) then fc p k (A k l) else 0

def nA (p : κ → Prop) [DecidablePred p] (A : Matrix κ κ ℂ) (k l : κ) : ℂ :=
  if (p k ↔ p l) then 0 else fc p k (A k l)

def gT (e : κ → σ) (p : κ → Prop) [DecidablePred p] (A : Matrix κ κ ℂ) (P : MvPolynomial σ ℂ) (k l : κ) :
    MvPolynomial σ ℂ :=
  C (mA p A k l) * X (e k) * pderiv (e l) P + C (nA p A k l / 2) * X (e k) * X (e l) * P -
    C (conj (nA p A k l) / 2) * pderiv (e k) (pderiv (e l) P)

theorem pair_eq (e : κ → σ) (he : Function.Injective e) (p : κ → Prop) [DecidablePred p] (A : Matrix κ κ ℂ)
    (hA : ∀ k l, conj (A k l) = (if (p k ↔ p l) then -A l k else A l k)) (P : MvPolynomial σ ℂ) (k l : κ) :
    C (A k l) * wOp e p k (vOp e p l P) + C (A l k) * wOp e p l (vOp e p k P) =
      gT e p A P k l + gT e p A P l k -
        (if k = l ∧ ¬ p k then C (2 * A k k) * P else 0) := by
  have hd : ∀ (a b : κ) (Q : MvPolynomial σ ℂ), pderiv (e a) (pderiv (e b) Q) = pderiv (e b) (pderiv (e a) Q) :=
    fun a b Q => pderiv_comm' _ _ _
  have hx : ∀ (a b : κ) (Q : MvPolynomial σ ℂ), pderiv (e a) (X (e b) * Q) =
      X (e b) * pderiv (e a) Q + (if a = b then Q else 0) := fun a b Q => by
    rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
    simp only [Pi.single_apply, he.eq_iff]
    by_cases h : a = b
    · simp [h, mul_comm]
    · simp [h, Ne.symm h]
  have hkl := hA k l
  have hlk := hA l k
  have h2 : ∀ c : ℂ, C c = C (c / 2) + (C (c / 2) : MvPolynomial σ ℂ) := fun c => by
    rw [← C_add, add_halves]
  have h2' : ∀ c : ℂ, C (2 * c) = C c + (C c : MvPolynomial σ ℂ) := fun c => by
    rw [← C_add, two_mul]
  have wp : ∀ a, p a → ∀ Q, wOp e p a Q = X (e a) * Q := fun a h Q => if_pos h
  have wn : ∀ a, ¬ p a → ∀ Q, wOp e p a Q = -pderiv (e a) Q := fun a h Q => if_neg h
  have vp : ∀ a, p a → ∀ Q, vOp e p a Q = pderiv (e a) Q := fun a h Q => if_pos h
  have vn : ∀ a, ¬ p a → ∀ Q, vOp e p a Q = X (e a) * Q := fun a h Q => if_neg h
  have fp : ∀ a, p a → ∀ c, fc p a c = c := fun a h c => if_pos h
  have fn : ∀ a, ¬ p a → ∀ c, fc p a c = conj c := fun a h c => if_neg h
  have ms : ∀ a b, (p a ↔ p b) → mA p A a b = fc p a (A a b) := fun a b h => if_pos h
  have md : ∀ a b, ¬ (p a ↔ p b) → mA p A a b = 0 := fun a b h => if_neg h
  have ns : ∀ a b, (p a ↔ p b) → nA p A a b = 0 := fun a b h => if_pos h
  have nd : ∀ a b, ¬ (p a ↔ p b) → nA p A a b = fc p a (A a b) := fun a b h => if_neg h
  by_cases hk : p k <;> by_cases hl : p l
  · have hn : ¬ (k = l ∧ ¬ p k) := fun h => h.2 hk
    have e1 : (p k ↔ p l) := by simp [hk, hl]
    rw [if_neg hn, wp k hk, wp l hl, vp k hk, vp l hl]
    simp only [gT, ms k l e1, ms l k e1.symm, ns k l e1, ns l k e1.symm, fp k hk, fp l hl, zero_div, map_zero, C_0]
    ring
  · have hne : k ≠ l := fun h => hl (h ▸ hk)
    have hn : ¬ (k = l ∧ ¬ p k) := fun h => hne h.1
    have e1 : ¬ (p k ↔ p l) := by simp [hk, hl]
    have e2 : ¬ (p l ↔ p k) := by simp [hk, hl]
    rw [if_neg e1] at hkl
    rw [if_neg e2] at hlk
    rw [if_neg hn, wp k hk, wn l hl, vp k hk, vn l hl]
    simp only [gT, md k l e1, md l k e2, nd k l e1, nd l k e2, fp k hk, fn l hl, hlk, hkl, map_zero, C_0, zero_div]
    rw [h2 (A k l), h2 (A l k), hd l k]
    ring
  · have hne : k ≠ l := fun h => hk (h ▸ hl)
    have hn : ¬ (k = l ∧ ¬ p k) := fun h => hne h.1
    have e1 : ¬ (p k ↔ p l) := by simp [hk, hl]
    have e2 : ¬ (p l ↔ p k) := by simp [hk, hl]
    rw [if_neg e1] at hkl
    rw [if_neg e2] at hlk
    rw [if_neg hn, wn k hk, wp l hl, vn k hk, vp l hl]
    simp only [gT, md k l e1, md l k e2, nd k l e1, nd l k e2, fn k hk, fp l hl, hlk, hkl, map_zero, C_0, zero_div]
    rw [h2 (A k l), h2 (A l k), hd l k]
    ring
  · have e1 : (p k ↔ p l) := by simp [hk, hl]
    have e2 : (p l ↔ p k) := by simp [hk, hl]
    rw [if_pos e1] at hkl
    rw [if_pos e2] at hlk
    rw [wn k hk, wn l hl, vn k hk, vn l hl, hx, hx]
    simp only [gT, ms k l e1, ms l k e2, ns k l e1, ns l k e2, fn k hk, fn l hl, hlk, hkl, map_zero, C_0, zero_div,
      map_neg]
    by_cases h : k = l
    · subst h
      simp only [if_true, true_and, if_pos hk, not_false_eq_true, if_pos (show ¬ p k from hk)]
      rw [h2' (A k k)]
      ring
    · have h' : l ≠ k := Ne.symm h
      rw [if_neg (fun hh : k = l ∧ ¬ p k => h hh.1), if_neg h, if_neg h']
      ring

theorem sum_eq (e : κ → σ) (he : Function.Injective e) (p : κ → Prop) [DecidablePred p] (A : Matrix κ κ ℂ)
    (hA : ∀ k l, conj (A k l) = (if (p k ↔ p l) then -A l k else A l k)) (P : MvPolynomial σ ℂ) :
    ∑ k, ∑ l, C (A k l) * wOp e p k (vOp e p l P) =
      ∑ k, ∑ l, gT e p A P k l - ∑ k, (if p k then 0 else C (A k k) * P) := by
  set S := ∑ k, ∑ l, C (A k l) * wOp e p k (vOp e p l P) with hS
  set G := ∑ k, ∑ l, gT e p A P k l with hG
  set R := ∑ k, (if p k then 0 else C (A k k) * P) with hR
  have h1 : S + S = (G + G) - (R + R) := by
    have e1 : S + S = ∑ k, ∑ l, (C (A k l) * wOp e p k (vOp e p l P) + C (A l k) * wOp e p l (vOp e p k P)) := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun k l => C (A l k) * wOp e p l (vOp e p k P))]
    have e2 : G + G = ∑ k, ∑ l, (gT e p A P k l + gT e p A P l k) := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun k l => gT e p A P l k)]
    have e3 : R + R = ∑ k, ∑ l, (if k = l ∧ ¬ p k then C (2 * A k k) * P else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : p k
      · simp [hk]
      · simp only [hk, if_false, not_false_eq_true, and_true, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [two_mul, C_add, add_mul]
    rw [e1, e2, e3, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => pair_eq e he p A hA P k l
  have h2 : (2 : ℂ) • S = (2 : ℂ) • (G - R) := by
    rw [two_smul, two_smul, h1]
    abel
  exact smul_right_injective _ (two_ne_zero (α := ℂ)) h2

end Abstract

section Concrete

open Formalism.BasicNotions Formalism.IndefR.Datum Formalism.IndefR.Fock.Sk GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

def sgB {k : ℕ} (p : ℕ) (a : Fin k) : Bool := decide ((a : ℕ) < p)

theorem Jm_eq' {k : ℕ} (ε : Fin k → Bool) : Formalism.REAL.Jm ε = diagonal fun a => sgn (ε a) := rfl

theorem sgn_sq (e : Bool) : sgn e * sgn e = 1 := by cases e <;> simp [sgn]

theorem onb_facts {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    IsUnit B.det ∧ Bᴴ * G * B = Formalism.REAL.Jm (sgB p) ∧ s * B = B * Formalism.REAL.Jm (sgB p) := by
  obtain ⟨ε, h1, h2, h3⟩ := h
  have e : (diagonal fun a => (ε a : ℂ)) = Formalism.REAL.Jm (sgB p) := by
    rw [Jm_eq']
    congr 1
    funext a
    rcases h1 a with ⟨h, h'⟩ | ⟨h, h'⟩
    · simp [h, h', sgB, sgn]
    · simp [h, sgB, sgn, not_lt.2 h']
  rw [e] at h2 h3
  refine ⟨?_, h2, h3⟩
  have hJ : Formalism.REAL.Jm (sgB (k := k) p) * Formalism.REAL.Jm (sgB p) = 1 := by
    simp only [Jm_eq', diagonal_mul_diagonal, sgn_sq, diagonal_one]
  refine Matrix.isUnit_det_of_left_inverse (B := Formalism.REAL.Jm (sgB p) * (Bᴴ * G)) ?_
  rw [Matrix.mul_assoc, h2, hJ]

theorem lie_entry' {k : ℕ} {G B X : Matrix (Fin k) (Fin k) ℂ} {ε : Fin k → Bool} (hB : IsUnit B.det)
    (hG : Bᴴ * G * B = Formalism.REAL.Jm ε) (hX : Xᴴ * G + G * X = 0) (a b : Fin k) :
    conj ((B⁻¹ * X * B) a b) = -(sgn (ε a) * sgn (ε b)) * (B⁻¹ * X * B) b a := by
  have h1 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, nonsing_inv_mul _ hB, conjTranspose_one]
  have e : (B⁻¹ * X * B)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (B⁻¹ * X * B) = 0 := by
    rw [← hG]
    calc _ = Bᴴ * (Xᴴ * G + G * X) * B := by
          simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
          rw [← Matrix.mul_assoc (B⁻¹)ᴴ Bᴴ, show (B⁻¹)ᴴ * Bᴴ = 1 by
            rw [← conjTranspose_mul, mul_nonsing_inv _ hB, conjTranspose_one], Matrix.one_mul,
            mul_nonsing_inv_cancel_left _ _ hB]
      _ = 0 := by rw [hX, Matrix.mul_zero, Matrix.zero_mul]
  have e' := congrFun (congrFun e b) a
  rw [Matrix.add_apply, Jm_eq', mul_diagonal, diagonal_mul, conjTranspose_apply, Matrix.zero_apply,
    Complex.star_def] at e'
  linear_combination sgn (ε a) * e' - conj ((B⁻¹ * X * B) a b) * sgn_sq (ε a)

variable {m n : ℕ}

def aK (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  fun k l => (Y * Matrix.single l.1 l.2 (1 : ℂ) - Matrix.single l.1 l.2 (1 : ℂ) * X) k.1 k.2

theorem aK_apply (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) (k l : Fin m × Fin n) :
    aK X Y k l = (if k.2 = l.2 then Y k.1 l.1 else 0) - (if k.1 = l.1 then X l.2 k.2 else 0) := by
  by_cases h1 : k.2 = l.2 <;> by_cases h2 : k.1 = l.1 <;>
    simp [aK, Matrix.mul_apply, Matrix.single_apply, eq_comm, h1, h2]

def pp (pS pT : ℕ) (k : Fin m × Fin n) : Prop := PosF (m := m) (n := n) pS pT k.1 k.2

instance (pS pT : ℕ) : DecidablePred (pp (m := m) (n := n) pS pT) :=
  fun k => inferInstanceAs (Decidable (PosF pS pT k.1 k.2))

def sL (pS pT : ℕ) (k : Fin m × Fin n) : ℂ := sgn (sgB pT k.1) * sgn (sgB pS k.2)

theorem sL_eq (pS pT : ℕ) (k : Fin m × Fin n) : sL pS pT k = if pp pS pT k then 1 else -1 := by
  simp only [sL, sgB, pp, PosF, sgn]
  by_cases h1 : (k.1 : ℕ) < pT <;> by_cases h2 : (k.2 : ℕ) < pS <;> simp [h1, h2]

theorem sL_mul (pS pT : ℕ) (k l : Fin m × Fin n) :
    sL pS pT k * sL pS pT l = if (pp pS pT k ↔ pp pS pT l) then 1 else -1 := by
  rw [sL_eq, sL_eq]
  by_cases h1 : pp pS pT k <;> by_cases h2 : pp pS pT l <;> simp [h1, h2]

theorem aK_conj {X : Matrix (Fin n) (Fin n) ℂ} {Y : Matrix (Fin m) (Fin m) ℂ} {pS pT : ℕ}
    (hX : ∀ a b, conj (X a b) = -(sgn (sgB pS a) * sgn (sgB pS b)) * X b a)
    (hY : ∀ a b, conj (Y a b) = -(sgn (sgB pT a) * sgn (sgB pT b)) * Y b a) (k l : Fin m × Fin n) :
    conj (aK X Y k l) = if (pp pS pT k ↔ pp pS pT l) then -aK X Y l k else aK X Y l k := by
  have e : conj (aK X Y k l) = -(sL pS pT k * sL pS pT l) * aK X Y l k := by
    rw [aK_apply, aK_apply, map_sub]
    obtain ⟨i, j⟩ := k
    obtain ⟨i', j'⟩ := l
    simp only [sL]
    have ha := fun i => sgn_sq (sgB pT (i : Fin m))
    have hb := fun j => sgn_sq (sgB pS (j : Fin n))
    by_cases h1 : j = j' <;> by_cases h2 : i = i'
    · subst h1 h2
      simp only [if_true, hX, hY]
      linear_combination (-(X j j) * sgn (sgB pS j) * sgn (sgB pS j)) * ha i +
        (sgn (sgB pT i) * sgn (sgB pT i) * Y i i) * hb j
    · subst h1
      have h2' : i' ≠ i := Ne.symm h2
      simp only [if_true, if_neg h2, if_neg h2', map_zero, sub_zero, hY]
      linear_combination (sgn (sgB pT i) * sgn (sgB pT i') * Y i' i) * hb j
    · subst h2
      have h1' : j' ≠ j := Ne.symm h1
      simp only [if_true, if_neg h1, if_neg h1', map_zero, zero_sub, hX, map_neg]
      linear_combination (-(sgn (sgB pS j) * sgn (sgB pS j') * X j j')) * ha i
    · have h1' : j' ≠ j := Ne.symm h1
      have h2' : i' ≠ i := Ne.symm h2
      simp [h1, h2, h1', h2']
  rw [e, sL_mul]
  split_ifs <;> simp

section Coef

variable {sS BS XS : Matrix (Fin n) (Fin n) ℂ} {sT BT XT : Matrix (Fin m) (Fin m) ℂ} {pS pT : ℕ}

theorem cplxO_conj (hS : IsUnit BS.det) (hsS : sS * BS = BS * Formalism.REAL.Jm (sgB pS))
    (hsT : sT * BT = BT * Formalism.REAL.Jm (sgB pT)) (W : Matrix (Fin m) (Fin n) ℂ) :
    cplxO sS sT (BT * W * BS⁻¹) = BT * (Complex.I • ((Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) * W *
      (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ))) * BS⁻¹ := by
  have h : BS⁻¹ * sS = Formalism.REAL.Jm (sgB pS) * BS⁻¹ := by
    have e : sS = BS * Formalism.REAL.Jm (sgB pS) * BS⁻¹ := by rw [← hsS, mul_nonsing_inv_cancel_right _ _ hS]
    rw [e, Matrix.mul_assoc BS, nonsing_inv_mul_cancel_left _ _ hS]
  have e : sT * (BT * W * BS⁻¹) * sS = BT * (Formalism.REAL.Jm (sgB (k := m) pT) * W * Formalism.REAL.Jm (sgB (k := n) pS)) * BS⁻¹ := by
    calc _ = (sT * BT) * W * (BS⁻¹ * sS) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hsT, h]; simp only [Matrix.mul_assoc]
  rw [cplxO, e, Matrix.mul_smul, Matrix.smul_mul]

theorem adX_conj (hS : IsUnit BS.det) (hT : IsUnit BT.det) (W : Matrix (Fin m) (Fin n) ℂ) :
    adX XS XT (BT * W * BS⁻¹) = BT * ((BT⁻¹ * XT * BT) * W - W * (BS⁻¹ * XS * BS)) * BS⁻¹ := by
  have h1 : BT * ((BT⁻¹ * XT * BT) * W) * BS⁻¹ = XT * (BT * W * BS⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hT]
  have h2 : BT * (W * (BS⁻¹ * XS * BS)) * BS⁻¹ = BT * W * BS⁻¹ * XS := by
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv _ hS, Matrix.mul_one]
  rw [adX, Matrix.mul_sub, Matrix.sub_mul, h1, h2]

theorem fCoord_conj (hS : IsUnit BS.det) (hT : IsUnit BT.det) (W : Matrix (Fin m) (Fin n) ℂ) (k : Fin m × Fin n) :
    fCoord BS BT pS pT (BT * W * BS⁻¹) k = fc (pp pS pT) k (W k.1 k.2) := by
  have e : BT⁻¹ * (BT * W * BS⁻¹) * BS = W := by
    rw [Matrix.mul_assoc BT, nonsing_inv_mul_cancel_left _ _ hT, nonsing_inv_mul_cancel_right _ _ hS]
  simp only [fCoord, fc, pp, e]
  rfl

theorem Jm_entry {a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool) (W : Matrix (Fin a) (Fin b) ℂ) (i : Fin a) (j : Fin b) :
    (Formalism.REAL.Jm ε * W * Formalism.REAL.Jm ε') i j = sgn (ε i) * W i j * sgn (ε' j) := by
  rw [Jm_eq', Jm_eq', mul_diagonal, diagonal_mul]

theorem part_entry (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (k l : Fin m × Fin n) :
    ((1 / 2 : ℂ) • ((Y * Matrix.single l.1 l.2 (1 : ℂ) - Matrix.single l.1 l.2 (1 : ℂ) * X) + c •
      (Complex.I • ((Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) *
        (Y * (Complex.I • ((Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) * Matrix.single l.1 l.2 (1 : ℂ) *
          (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ))) -
        (Complex.I • ((Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) * Matrix.single l.1 l.2 (1 : ℂ) *
          (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ))) * X) *
        (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ))))) k.1 k.2 =
      (1 / 2 : ℂ) * (1 - c * (sL pS pT k * sL pS pT l)) * aK X Y k l := by
  have e1 : (Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) * Matrix.single l.1 l.2 (1 : ℂ) *
      (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ) = sL pS pT l • Matrix.single l.1 l.2 (1 : ℂ) := by
    ext a b
    rw [Jm_entry, Matrix.smul_apply, Matrix.single_apply, sL, smul_eq_mul]
    by_cases h : l.1 = a ∧ l.2 = b
    · obtain ⟨h1, h2⟩ := h
      subst h1 h2
      simp
    · simp [h]
  rw [e1]
  have e2 : Y * (Complex.I • sL pS pT l • Matrix.single l.1 l.2 (1 : ℂ)) -
      (Complex.I • sL pS pT l • Matrix.single l.1 l.2 (1 : ℂ)) * X =
      (Complex.I * sL pS pT l) • (Y * Matrix.single l.1 l.2 (1 : ℂ) - Matrix.single l.1 l.2 (1 : ℂ) * X) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul]
  have e3 : ∀ (w : ℂ) (F : Matrix (Fin m) (Fin n) ℂ), ((Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) * (w • F) *
      (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ)) k.1 k.2 =
      w * (sgn (sgB pT k.1) * F k.1 k.2 * sgn (sgB pS k.2)) := fun w F => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Jm_entry, smul_eq_mul]
  rw [e2, Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, e3]
  change (1 / 2 : ℂ) • (aK X Y k l + c • Complex.I • (Complex.I * sL pS pT l *
    (sgn (sgB pT k.1) * aK X Y k l * sgn (sgB pS k.2)))) = _
  simp only [smul_eq_mul, sL]
  linear_combination ((1 / 2 : ℂ) * c * (sgn (sgB pT l.1) * sgn (sgB pS l.2)) * sgn (sgB pT k.1) * sgn (sgB pS k.2) *
    aK X Y k l) * Complex.I_sq

theorem fc_zero (p : Fin m × Fin n → Prop) [DecidablePred p] (k : Fin m × Fin n) : fc p k 0 = 0 := by
  simp [fc]

theorem mCoef_eq (hS : IsUnit BS.det) (hT : IsUnit BT.det) (hsS : sS * BS = BS * Formalism.REAL.Jm (sgB pS))
    (hsT : sT * BT = BT * Formalism.REAL.Jm (sgB pT)) (k l : Fin m × Fin n) :
    mCoef sS BS XS sT BT XT pS pT k l = mA (pp pS pT) (aK (BS⁻¹ * XS * BS) (BT⁻¹ * XT * BT)) k l := by
  have h := part_entry (pS := pS) (pT := pT) (BS⁻¹ * XS * BS) (BT⁻¹ * XT * BT) (-1) k l
  rw [sL_mul] at h
  have e : ∀ F J : Matrix (Fin m) (Fin n) ℂ, (1 / 2 : ℂ) • (BT * F * BS⁻¹ - BT * J * BS⁻¹) =
      BT * ((1 / 2 : ℂ) • (F + (-1 : ℂ) • J)) * BS⁻¹ := fun F J => by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, neg_smul, one_smul, Matrix.mul_neg,
      Matrix.neg_mul, sub_eq_add_neg]
  simp only [mCoef, unitMap, cplxO_conj hS hsS hsT, adX_conj hS hT]
  rw [e, fCoord_conj hS hT, h]
  by_cases hp : pp pS pT k ↔ pp pS pT l
  · rw [if_pos hp, mA, if_pos hp]
    congr 1
    ring
  · rw [if_neg hp, mA, if_neg hp, show (1 / 2 : ℂ) * (1 - -1 * -1) = 0 by ring, zero_mul, fc_zero]

theorem nCoef_eq (hS : IsUnit BS.det) (hT : IsUnit BT.det) (hsS : sS * BS = BS * Formalism.REAL.Jm (sgB pS))
    (hsT : sT * BT = BT * Formalism.REAL.Jm (sgB pT)) (k l : Fin m × Fin n) :
    nCoef sS BS XS sT BT XT pS pT k l = nA (pp pS pT) (aK (BS⁻¹ * XS * BS) (BT⁻¹ * XT * BT)) k l := by
  have h := part_entry (pS := pS) (pT := pT) (BS⁻¹ * XS * BS) (BT⁻¹ * XT * BT) 1 k l
  rw [sL_mul] at h
  have e : ∀ F J : Matrix (Fin m) (Fin n) ℂ, (1 / 2 : ℂ) • (BT * F * BS⁻¹ + BT * J * BS⁻¹) =
      BT * ((1 / 2 : ℂ) • (F + (1 : ℂ) • J)) * BS⁻¹ := fun F J => by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, one_smul]
  simp only [nCoef, unitMap, cplxO_conj hS hsS hsT, adX_conj hS hT]
  rw [e, fCoord_conj hS hT, h]
  by_cases hp : pp pS pT k ↔ pp pS pT l
  · rw [if_pos hp, nA, if_pos hp, show (1 / 2 : ℂ) * (1 - 1 * 1) = 0 by ring, zero_mul, fc_zero]
  · rw [if_neg hp, nA, if_neg hp]
    congr 1
    ring

end Coef

section Final

variable {D : D7} (τ : D.what₂.Tau) {sS BS XS GS : Matrix (Fin n) (Fin n) ℂ} {sT BT XT GT : Matrix (Fin m) (Fin m) ℂ}
  (pS pT : ℕ)

def eV (k : Fin m × Fin n) : FVar D m n := (τ, k.1, k.2)

theorem eV_inj : Function.Injective (eV (D := D) (m := m) (n := n) τ) := fun k l h => by
  simp only [eV, Prod.mk.injEq, true_and] at h
  exact Prod.ext h.1 h.2

def tT (P : MvPolynomial (FVar D m n) ℂ) (k l : Fin m × Fin n) : MvPolynomial (FVar D m n) ℂ :=
  wOp (eV τ) (pp pS pT) k (vOp (eV τ) (pp pS pT) l P)

theorem sg_iff (i : Fin m) (j : Fin n) : (sgB pT i = sgB pS j) ↔ pp pS pT (i, j) := by
  simp only [sgB, pp, PosF, decide_eq_decide]

theorem rai_eq (i : Fin m) (j : Fin n) (Q : MvPolynomial (FVar D m n) ℂ) :
    raiO τ (sgB pS) (sgB pT) i j Q = sgn (sgB pS j) • wOp (eV τ) (pp pS pT) (i, j) Q := by
  unfold raiO wOp
  by_cases h : pp pS pT (i, j)
  · rw [if_pos ((sg_iff pS pT i j).2 h), if_pos h]
    rfl
  · rw [if_neg (fun e => h ((sg_iff pS pT i j).1 e)), if_neg h]
    rfl

theorem low_eq (i : Fin m) (j : Fin n) (Q : MvPolynomial (FVar D m n) ℂ) :
    lowO τ (sgB pS) (sgB pT) i j Q = sgn (sgB pS j) • vOp (eV τ) (pp pS pT) (i, j) Q := by
  unfold lowO vOp
  by_cases h : pp pS pT (i, j)
  · rw [if_pos ((sg_iff pS pT i j).2 h), if_pos h]
    rfl
  · rw [if_neg (fun e => h ((sg_iff pS pT i j).1 e)), if_neg h]
    rfl

theorem fockT_apply (Y : Matrix (Fin m) (Fin m) ℂ) (P : MvPolynomial (FVar D m n) ℂ) :
    fockT τ (sgB pS) (sgB pT) Y P = ∑ i, ∑ l, ∑ j, C (Y i l) * tT τ pS pT P (i, j) (l, j) +
      (((n : ℂ) / 2) * Y.trace) • P := by
  have term : ∀ i l j, (raiO τ (sgB pS) (sgB pT) i j * lowO τ (sgB pS) (sgB pT) l j +
      if i = l then (1 / 2 : ℂ) • (1 : Module.End ℂ (Formalism.IndefR.Links.PolF D m n)) else 0) P =
      tT τ pS pT P (i, j) (l, j) + (if i = l then (1 / 2 : ℂ) else 0) • P := fun i l j => by
    rw [LinearMap.add_apply, Module.End.mul_apply, low_eq, map_smul, rai_eq, smul_smul, sgn_sq, one_smul]
    congr 1
    split_ifs <;> simp
  simp only [fockT, LinearMap.sum_apply, LinearMap.smul_apply, term]
  simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib, C_mul']
  congr 1
  simp only [smul_smul, ← Finset.sum_smul]
  congr 1
  simp [Matrix.trace, mul_ite, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem fockS_apply (Z : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (FVar D m n) ℂ) :
    fockS τ (sgB pS) (sgB pT) Z P = ∑ j, ∑ k, ∑ i, C (Z j k * (sgn (sgB pS j) * sgn (sgB pS k))) * tT τ pS pT P (i, j) (i, k) +
      (((m : ℂ) / 2) * Z.trace) • P := by
  have term : ∀ i j k, (raiO τ (sgB pS) (sgB pT) i j * lowO τ (sgB pS) (sgB pT) i k +
      if j = k then (1 / 2 : ℂ) • (1 : Module.End ℂ (Formalism.IndefR.Links.PolF D m n)) else 0) P =
      (sgn (sgB pS j) * sgn (sgB pS k)) • tT τ pS pT P (i, j) (i, k) + (if j = k then (1 / 2 : ℂ) else 0) • P := fun i j k => by
    rw [LinearMap.add_apply, Module.End.mul_apply, low_eq, map_smul, rai_eq, smul_smul, mul_comm (sgn (sgB pS k))]
    congr 1
    split_ifs <;> simp
  simp only [fockS, LinearMap.sum_apply, LinearMap.smul_apply, term]
  simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib, C_mul', smul_smul]
  congr 1
  simp only [← Finset.sum_smul]
  congr 1
  simp [Matrix.trace, mul_ite, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem sum_aK {R : Type} [CommRing R] (c : ℂ →+* R) (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ)
    (T : Fin m × Fin n → Fin m × Fin n → R) :
    ∑ k, ∑ l, c (aK X Y k l) * T k l =
      ∑ i, ∑ l, ∑ j, c (Y i l) * T (i, j) (l, j) - ∑ j, ∑ k, ∑ i, c (X k j) * T (i, j) (i, k) := by
  simp only [Fintype.sum_prod_type, aK_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [apply_ite c, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · have e : ∀ i j, ∑ i', ∑ j', c (if (i, j).1 = (i', j').1 then X (i', j').2 (i, j).2 else 0) * T (i, j) (i', j') =
        ∑ k, c (X k j) * T (i, j) (i, k) := fun i j => by
      rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun j' _ => by simp [Ne.symm hb]) (by simp)]
      simp
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]

theorem fock_eq_quad (hS : IsONBasis GS sS BS pS) (hT : IsONBasis GT sT BT pT) (hX : XSᴴ * GS + GS * XS = 0)
    (hY : XTᴴ * GT + GT * XT = 0) (P : MvPolynomial (FVar D m n) ℂ) :
    fockS τ (sgB pS) (sgB pT) ((BS⁻¹ * XS * BS).map (starRingEnd ℂ)) P + fockT τ (sgB pS) (sgB pT) (BT⁻¹ * XT * BT) P =
      quadOp τ sS BS XS sT BT XT pS pT P + halfTrJ sS BS XS sT BT XT pS pT • P := by
  classical
  obtain ⟨uS, nS, cS⟩ := onb_facts hS
  obtain ⟨uT, nT, cT⟩ := onb_facts hT
  set Xf := BS⁻¹ * XS * BS with hXf
  set Yf := BT⁻¹ * XT * BT with hYf
  have lX : ∀ a b, conj (Xf a b) = -(sgn (sgB pS a) * sgn (sgB pS b)) * Xf b a := lie_entry' uS nS hX
  have lY : ∀ a b, conj (Yf a b) = -(sgn (sgB pT a) * sgn (sgB pT b)) * Yf b a := lie_entry' uT nT hY
  have hA := aK_conj lX lY
  have q1 : quadOp τ sS BS XS sT BT XT pS pT P = ∑ k, ∑ l, gT (eV τ) (pp pS pT) (aK Xf Yf) P k l := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mCoef_eq uS uT cS cT, nCoef_eq uS uT cS cT]
    rfl
  have q2 := sum_eq (eV τ) (eV_inj τ) (pp pS pT) (aK Xf Yf) hA P
  have q3 := sum_aK (C : ℂ →+* MvPolynomial (FVar D m n) ℂ) Xf Yf (tT τ pS pT P)
  have q4 : ∑ j, ∑ k, ∑ i, C (Xf.map (starRingEnd ℂ) j k * (sgn (sgB pS j) * sgn (sgB pS k))) * tT τ pS pT P (i, j) (i, k) =
      -∑ j, ∑ k, ∑ i, (C (Xf k j) : MvPolynomial (FVar D m n) ℂ) * tT τ pS pT P (i, j) (i, k) := by
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    have e : Xf.map (starRingEnd ℂ) j k * (sgn (sgB pS j) * sgn (sgB pS k)) = -Xf k j := by
      rw [Matrix.map_apply, lX j k]
      linear_combination (-(Xf k j) * sgn (sgB pS k) * sgn (sgB pS k)) * sgn_sq (sgB pS j) - Xf k j * sgn_sq (sgB pS k)
    rw [e, C_neg, neg_mul]
  have tr1 : (Xf.map (starRingEnd ℂ)).trace = -Xf.trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, lX, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sgn_sq]
    ring
  have tr2 : ∑ k : Fin m × Fin n, aK Xf Yf k k = (n : ℂ) * Yf.trace - (m : ℂ) * Xf.trace := by
    simp only [Fintype.sum_prod_type, aK_apply, if_true, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Matrix.trace, Matrix.diag, Finset.mul_sum]
  have sc : halfTrJ sS BS XS sT BT XT pS pT = (1 / 2 : ℂ) * ∑ k, aK Xf Yf k k - ∑ k, (if pp pS pT k then 0 else aK Xf Yf k k) := by
    rw [halfTrJ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mCoef_eq uS uT cS cT, mA, if_pos Iff.rfl, fc]
    by_cases h : pp pS pT k
    · simp only [if_pos h]
      ring
    · have e := hA k k
      rw [if_pos Iff.rfl] at e
      rw [if_neg h, if_neg h, e]
      ring
  have hR : ∑ k, (if pp pS pT k then 0 else C (aK Xf Yf k k) * P) =
      (∑ k, (if pp pS pT k then 0 else aK Xf Yf k k)) • P := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · simp
    · rw [C_mul']
  have hq : ∑ i, ∑ l, ∑ j, C (Yf i l) * tT τ pS pT P (i, j) (l, j) =
      quadOp τ sS BS XS sT BT XT pS pT P - (∑ k, (if pp pS pT k then 0 else aK Xf Yf k k)) • P +
        ∑ j, ∑ k, ∑ i, C (Xf k j) * tT τ pS pT P (i, j) (i, k) := by
    refine eq_add_of_sub_eq ?_
    rw [q1, ← hR, ← q2, ← q3]
    rfl
  rw [fockS_apply, fockT_apply, q4, sc, tr1, tr2, hq]
  module

end Final

end Concrete

end GlobalTheory.WeilReal.QuadAlg
