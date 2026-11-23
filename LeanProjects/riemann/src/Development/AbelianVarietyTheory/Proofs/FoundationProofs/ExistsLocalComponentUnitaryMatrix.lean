import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIdeleGenerator

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.LocalComponent

theorem exists_idem_away (D : D7) {q : ℕ} (hq : q.Prime) :
    ∃ f ∈ OhE D, f * f = f ∧ sgA D f = f ∧ (∀ k : ℕ, ∃ w ∈ OhE D, f = (q : AE D) ^ k * w) ∧
      ∀ n : ℕ, n.Coprime q → ∃ w ∈ OhE D, 1 - f = (n : AE D) * w := by
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := GlobalTheory.IdealIdele.exists_idem (OhE D) hsep hcpl q hq.pos
  have h2 : ∀ k : ℕ, ∃ w ∈ OhE D, f = (q : AE D) ^ k * w := by
    intro k
    induction k with
    | zero => exact ⟨f, hf, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, h⟩ := ih
      refine ⟨v * w, mul_mem hv hw, ?_⟩
      calc f = f * f := hff.symm
        _ = ((q : AE D) ^ k * v) * ((q : AE D) * w) := by rw [← h, ← hfw]
        _ = _ := by ring
  have h4 : ∀ n : ℕ, n.Coprime q → ∃ w ∈ OhE D, 1 - f = (n : AE D) * w := fun n hn =>
    h3 n (Nat.pos_of_ne_zero (by rintro rfl; exact hq.ne_one (by simpa using hn))) hn.symm
  refine ⟨f, hf, hff, ?_, h2, h4⟩
  have key : f * (1 - sgA D f) = 0 := by
    refine hsep _ fun N hN => ?_
    obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.ne_one
    obtain ⟨u, hu, e1⟩ := h2 a
    obtain ⟨v, hv, e2⟩ := h4 n' ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm
    have e3 := congrArg (sgA D) e2
    rw [map_sub, map_one, map_mul, map_natCast] at e3
    refine ⟨u * sgA D v, mul_mem hu (VacMove.sgA_mem D hv), ?_⟩
    rw [e3]
    push_cast
    linear_combination ((n' : AE D) * sgA D v) * e1
  have key' := congrArg (sgA D) key
  rw [map_mul, map_sub, map_one, VacMove.sgA_sgA, map_zero] at key'
  linear_combination key' - key

theorem exists_common_denom (D : D7) {q : ℕ} (hq : q.Prime) {n : ℕ} (y : Fin n → AE D) :
    ∃ a m : ℕ, m.Coprime q ∧ ∀ i, (q : AE D) ^ a * (m : AE D) * y i ∈ OhE D := by
  choose N hN hy using fun i => VacMove.exists_nat_denom D (y i)
  have hP : (∏ i, N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hN i).ne'
  obtain ⟨a, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hP q hq.ne_one
  refine ⟨a, m, ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm, fun i => ?_⟩
  obtain ⟨c, hc⟩ : N i ∣ ∏ i, N i := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have e' : (q : AE D) ^ a * (m : AE D) = (c : AE D) * (N i : AE D) := by
    have := congrArg (Nat.cast : ℕ → AE D) (e.symm.trans hc)
    push_cast at this
    rw [this, mul_comm]
  rw [e', mul_assoc]
  exact mul_mem (natCast_mem _ c) (hy i)

theorem glue_mul {A : Type} [CommRing A] {n : ℕ} {f : A} (hf : f * f = f) {σ τ : Matrix (Fin n) (Fin n) A}
    (h : σ * τ = 1) : ((1 - f) • σ + f • (1 : Matrix (Fin n) (Fin n) A)) * ((1 - f) • τ + f • 1) = 1 := by
  have h1 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  have h2 : (1 - f) * f = 0 := by linear_combination -hf
  have h3 : f * (1 - f) = 0 := by linear_combination -hf
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h, h1, h2, h3, hf, zero_smul,
    Matrix.mul_one, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem mulVec_inc_smul (D : D7) {n : ℕ} (H : Matrix (Fin n) (Fin n) (AE D)) (c : ℕ) (x : Fin n → D.host.E)
    (i : Fin n) : H.mulVec (fun j => inc D (((c : D.host.E) • x) j)) i =
      (c : AE D) * H.mulVec (fun j => inc D (x j)) i := by
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 1000000 in

theorem exists_local_component : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 → ∃ g : GA D n, (∀ p : ℕ, p.Prime → p ≠ q → TrivAt D p (g : GL (Fin n) (AE D))) ∧ ∀ (h : GA D n) (B C : Lat D n), Moves D (h : GL (Fin n) (AE D)) B → EqAway D q B C → SAt D q s B C → Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) C := by
  intro D n q hq s hs
  obtain ⟨f, hf, hff, hsg, h2, h3⟩ := exists_idem_away D hq
  have hs' : cT D s * s = 1 := mul_eq_one_comm.1 hs
  have a : s.map (inc D) * (cT D s).map (inc D) = 1 := by
    rw [← Matrix.map_mul, hs, Matrix.map_one _ (map_zero _) (map_one _)]
  have b : (cT D s).map (inc D) * s.map (inc D) = 1 := by
    rw [← Matrix.map_mul, hs', Matrix.map_one _ (map_zero _) (map_one _)]
  let g : GL (Fin n) (AE D) := ⟨_, _, glue_mul hff a, glue_mul hff b⟩
  have hg : g ∈ GA D n := by
    rw [PtsMem.mem_GA]
    have e : ((g : Matrix (Fin n) (Fin n) (AE D)).map (sgA D)).transpose =
        (1 - f) • (cT D s).map (inc D) + f • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
      ext i j
      change sgA D ((1 - f) * inc D (s j i) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) j i) =
        (1 - f) * inc D (D.host.conj (s j i)) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) i j
      rw [map_add, map_mul, map_mul, map_sub, map_one, hsg, PtsMem.sgA_inc]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
    rw [e]
    exact glue_mul hff b
  refine ⟨⟨g, hg⟩, fun p hp hpq i j => ?_, ?_⟩
  · have hz : ZeroAt D p (1 - f) := fun k => by
      obtain ⟨w, hw, e⟩ := h3 (p ^ k) (Nat.Coprime.pow_left k ((Nat.coprime_primes hp hq).2 hpq))
      exact ⟨1, one_pos, by simp, w, hw, by rw [e]; push_cast; ring⟩
    have := VacMove.zeroAt_mul D hp hz (inc D (s i j) - (1 : Matrix (Fin n) (Fin n) (AE D)) i j)
    convert this using 1
    change (1 - f) * inc D (s i j) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) i j - _ = _
    ring
  · rintro h B C hB ⟨k, hBC, hCB⟩ ⟨m, hm, hsB, hsC⟩ x
    set H : Matrix (Fin n) (Fin n) (AE D) :=
      (((h : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) with hH
    have hB' : ∀ (c : ℕ) (y : Fin n → D.host.E), (c : D.host.E) • y ∈ B ↔
        ∀ i, (c : AE D) * H.mulVec (fun j => inc D (y j)) i ∈ OhE D := fun c y => by
      rw [hB]
      exact forall_congr' fun i => by rw [mulVec_inc_smul]
    have e : ∀ i, ((((((⟨g, hg⟩ : GA D n) * h : GA D n) : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) :
        Matrix (Fin n) (Fin n) (AE D)).mulVec (fun j => inc D (x j))) i =
        (1 - f) * H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i + f * H.mulVec (fun j => inc D (x j)) i := by
      intro i
      rw [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      change H.mulVec (((1 - f) • (cT D s).map (inc D) + f • (1 : Matrix (Fin n) (Fin n) (AE D))).mulVec _) i = _
      have e1 : ((cT D s).map (inc D)).mulVec (fun j => inc D (x j)) = fun j => inc D ((cT D s).mulVec x j) :=
        funext fun j => (RingHom.map_mulVec (inc D) (cT D s) x j).symm
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, e1, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul]
      rfl
    simp only [e]
    constructor
    · intro hx i
      obtain ⟨w, hw, e1⟩ := h3 m hm
      obtain ⟨v, hv, e2⟩ := h2 k
      have m1 := (hB' m _).1 (hsC x hx) i
      have m2 := (hB' (q ^ k) x).1 (by simpa using hCB x hx) i
      have := add_mem (mul_mem hw m1) (mul_mem hv m2)
      convert this using 1
      push_cast
      rw [e1]
      linear_combination H.mulVec (fun j => inc D (x j)) i * e2
    · intro hx
      obtain ⟨a1, n1, hn1, d1⟩ := exists_common_denom D hq (H.mulVec (fun j => inc D ((cT D s).mulVec x j)))
      obtain ⟨a2, n2, hn2, d2⟩ := exists_common_denom D hq (H.mulVec (fun j => inc D (x j)))
      have m1 : (n1 : D.host.E) • (cT D s).mulVec x ∈ B := (hB' n1 _).2 fun i => by
        obtain ⟨v, hv, e2⟩ := h2 a1
        have := add_mem (mul_mem (mul_mem (natCast_mem _ n1) (sub_mem (one_mem _) hf)) (hx i)) (mul_mem hv (d1 i))
        convert this using 1
        linear_combination ((n1 : AE D) * H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i) * e2 -
          (n1 : AE D) * (H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i - H.mulVec (fun j => inc D (x j)) i) * hff
      have m2 : ((q ^ a2 : ℕ) : D.host.E) • x ∈ B := (hB' (q ^ a2) _).2 fun i => by
        obtain ⟨w, hw, e1⟩ := h3 n2 hn2
        have := add_mem (mul_mem (mul_mem (pow_mem (natCast_mem _ q) a2) hf) (hx i)) (mul_mem hw (d2 i))
        convert this using 1
        push_cast
        linear_combination ((q : AE D) ^ a2 * H.mulVec (fun j => inc D (x j)) i) * e1 +
          (q : AE D) ^ a2 * (H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i - H.mulVec (fun j => inc D (x j)) i) * hff
      have c1 := hsB _ m1
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hs, Matrix.one_mulVec, smul_smul] at c1
      have c2 := hBC _ m2
      rw [smul_smul] at c2
      have hcop : IsCoprime ((m * n1 : ℕ) : ℤ) ((q ^ (k + a2) : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ (Nat.Coprime.mul_left hm hn1))
      obtain ⟨u, v, huv⟩ := hcop
      have huv' := congrArg (Int.cast : ℤ → D.host.E) huv
      push_cast at huv' c2
      have := add_mem (zsmul_mem c1 u) (zsmul_mem c2 v)
      convert this using 1
      funext j
      simp only [Pi.add_apply, Pi.smul_apply]
      simp only [zsmul_eq_mul, smul_eq_mul]
      linear_combination (-x j) * huv'

end GlobalTheory.LocalComponent
