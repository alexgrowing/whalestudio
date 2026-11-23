import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

def vermaIdeal (lam : Fin n → ℂ) : Submodule ℂ (U n) :=
  nPlusU n ⊔ Submodule.span ℂ
    {x | ∃ (u : U n) (k : Fin n), u * (e (k, k) - algebraMap ℂ (U n) (lam k)) = x}

theorem nPlusU_le_vermaIdeal (lam : Fin n → ℂ) : nPlusU n ≤ vermaIdeal lam := le_sup_left

theorem mul_e_sub_mem_vermaIdeal (lam : Fin n → ℂ) (u : U n) (k : Fin n) :
    u * (e (k, k) - algebraMap ℂ (U n) (lam k)) ∈ vermaIdeal lam :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨u, k, rfl⟩)

theorem mul_mem_vermaIdeal (lam : Fin n → ℂ) (v : U n) {x : U n} (hx : x ∈ vermaIdeal lam) :
    v * x ∈ vermaIdeal lam := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  clear hx
  rw [mul_add]
  refine Submodule.add_mem _ (nPlusU_le_vermaIdeal lam (mul_mem_nPlusU v hy)) ?_
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, k, rfl⟩ := hx
    rw [← mul_assoc]
    exact mul_e_sub_mem_vermaIdeal lam _ k
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem hcEmb_sub_eval_mem_vermaIdeal (lam : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    hcEmb p - algebraMap ℂ (U n) (eval lam p) ∈ vermaIdeal lam := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, eval_add, map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hp hq
  | mul_X p k hp =>
    have : hcEmb (p * X k) - algebraMap ℂ (U n) (eval lam (p * X k)) =
        hcEmb p * (e (k, k) - algebraMap ℂ (U n) (lam k)) +
          lam k • (hcEmb p - algebraMap ℂ (U n) (eval lam p)) := by
      rw [map_mul, hcEmb_X, eval_mul, eval_X]
      simp only [mul_sub, Algebra.smul_def]
      rw [Algebra.commutes (lam k) (hcEmb p), ← map_mul, mul_comm (lam k)]
      abel
    rw [this]
    exact Submodule.add_mem _ (mul_e_sub_mem_vermaIdeal lam _ k) (Submodule.smul_mem _ _ hp)

noncomputable def lowPart (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.filter IsLower

open Classical in

noncomputable def vermaCoord (lam : Fin n → ℂ) : U n →ₗ[ℂ] ((Fin n × Fin n →₀ ℕ) →₀ ℂ) :=
  pbw.constr ℂ fun m =>
    if HasUpper m then 0 else Finsupp.single (lowPart m) (eval lam (monomial (diagExp m) 1))

theorem vermaCoord_canon_of_hasUpper (lam : Fin n → ℂ) {m : Fin n × Fin n →₀ ℕ} (h : HasUpper m) :
    vermaCoord lam (canon m) = 0 := by
  rw [vermaCoord, ← pbw_apply, Module.Basis.constr_basis, if_pos h]

theorem vermaCoord_canon_of_not (lam : Fin n → ℂ) {m : Fin n × Fin n →₀ ℕ} (h : ¬ HasUpper m) :
    vermaCoord lam (canon m) = Finsupp.single (lowPart m) (eval lam (monomial (diagExp m) 1)) := by
  rw [vermaCoord, ← pbw_apply, Module.Basis.constr_basis, if_neg h]

theorem vermaCoord_eq_zero_of_mem_nPlusU (lam : Fin n → ℂ) {x : U n} (hx : x ∈ nPlusU n) :
    vermaCoord lam x = 0 := by
  have hx' : x ∈ Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, HasUpper m ∧ canon m = x} :=
    nPlusU_le_spanUpper hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact vermaCoord_canon_of_hasUpper lam hm
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

theorem canon_mul_e_diag_of_not_hasUpper {m : Fin n × Fin n →₀ ℕ} (h : ¬ HasUpper m) (k : Fin n) :
    canon m * e (k, k) = canon (m + Finsupp.single (k, k) 1) := by
  have hup : ∀ a ∈ upL n, m a = 0 := fun a ha => by
    by_contra hne; exact h ⟨a, mem_upL.1 ha, hne⟩
  have hk : ¬ IsUpper (k, k) := not_upper_of_diag (a := (k, k)) rfl
  have hup' : ∀ a ∈ upL n, (m + Finsupp.single (k, k) 1 : Fin n × Fin n →₀ ℕ) a = 0 := fun a ha => by
    have hne : a ≠ (k, k) := fun hak => hk (hak ▸ mem_upL.1 ha)
    simp [hup a ha, Ne.symm hne]
  have hlow : blockW (lowL n) (m + Finsupp.single (k, k) 1) = blockW (lowL n) m := by
    refine blockW_congr fun a ha => ?_
    have hne : a ≠ (k, k) := fun hak => not_lower_of_diag (a := (k, k)) rfl (hak ▸ mem_lowL.1 ha)
    simp [Finsupp.single_apply, Ne.symm hne]
  have hdiag : diagExp (m + Finsupp.single (k, k) 1) = diagExp m + Finsupp.single k 1 := by
    ext i
    simp only [diagExp_apply, Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq, and_self]
  rw [canon_eq_triangular, canon_eq_triangular, blockW_eq_nil hup, blockW_eq_nil hup', hlow, hdiag,
    show monomial (diagExp m + Finsupp.single k 1) (1 : ℂ) = monomial (diagExp m) 1 * X k by
      rw [X, monomial_mul, mul_one], map_mul, hcEmb_X]
  simp only [word_nil, mul_one, mul_assoc]

theorem vermaCoord_canon_mul_e_sub (lam : Fin n → ℂ) (m : Fin n × Fin n →₀ ℕ) (k : Fin n) :
    vermaCoord lam (canon m * (e (k, k) - algebraMap ℂ (U n) (lam k))) = 0 := by
  by_cases h : HasUpper m
  · refine vermaCoord_eq_zero_of_mem_nPlusU lam ?_
    rw [mul_sub, ← Algebra.commutes, ← Algebra.smul_def]
    exact Submodule.sub_mem _ (mul_e_diag_mem_nPlusU (canon_mem_nPlusU h) k)
      (Submodule.smul_mem _ _ (canon_mem_nPlusU h))
  · have hnu : ¬ HasUpper (m + Finsupp.single (k, k) 1) := by
      rintro ⟨a, ha, hne⟩
      apply h
      refine ⟨a, ha, ?_⟩
      have hak : a ≠ (k, k) := fun hak => not_upper_of_diag (a := (k, k)) rfl (hak ▸ ha)
      simpa [Finsupp.single_apply, Ne.symm hak] using hne
    have hlow : lowPart (m + Finsupp.single (k, k) 1) = lowPart m := by
      ext a
      simp only [lowPart, Finsupp.filter_apply, Finsupp.add_apply]
      split_ifs with ha
      · have hak : a ≠ (k, k) := fun hak => not_lower_of_diag (a := (k, k)) rfl (hak ▸ ha)
        simp [Finsupp.single_apply, Ne.symm hak]
      · rfl
    have hdiag : diagExp (m + Finsupp.single (k, k) 1) = diagExp m + Finsupp.single k 1 := by
      ext i
      simp only [diagExp_apply, Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq, and_self]
    rw [mul_sub, ← Algebra.commutes, ← Algebra.smul_def, map_sub, map_smul,
      canon_mul_e_diag_of_not_hasUpper h, vermaCoord_canon_of_not lam hnu,
      vermaCoord_canon_of_not lam h, hlow, hdiag, Finsupp.smul_single,
      show monomial (diagExp m + Finsupp.single k 1) (1 : ℂ) = monomial (diagExp m) 1 * X k by
        rw [X, monomial_mul, mul_one],
      eval_mul, eval_X, smul_eq_mul, mul_comm (lam k), sub_self]

theorem vermaCoord_mul_e_sub (lam : Fin n → ℂ) (u : U n) (k : Fin n) :
    vermaCoord lam (u * (e (k, k) - algebraMap ℂ (U n) (lam k))) = 0 := by
  have hu : u ∈ Submodule.span ℂ (Set.range (canon (n := n))) := by
    rw [span_canon_eq_top]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact vermaCoord_canon_mul_e_sub lam m k
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_mul_assoc, map_smul, hx, smul_zero]

theorem vermaCoord_vermaIdeal (lam : Fin n → ℂ) {x : U n} (hx : x ∈ vermaIdeal lam) :
    vermaCoord lam x = 0 := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  clear hx
  rw [map_add, vermaCoord_eq_zero_of_mem_nPlusU lam hy, zero_add]
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨u, k, rfl⟩ := hx; exact vermaCoord_mul_e_sub lam u k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

theorem canon_single (a : Fin n × Fin n) (m : ℕ) : canon (Finsupp.single a m) = e a ^ m := by
  rw [canon_eq_prod]
  have key : ∀ l : List (Fin n × Fin n), l.Nodup →
      (l.map fun b => e b ^ (Finsupp.single a m) b).prod = if a ∈ l then e a ^ m else 1 := by
    intro l hl
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.map_cons, List.prod_cons, ih (List.nodup_cons.1 hl).2]
      by_cases hb : b = a
      · subst hb
        simp [(List.nodup_cons.1 hl).1]
      · simp [Finsupp.single_apply, Ne.symm hb, hb]
  rw [key _ nodup_letters, if_pos (mem_letters a)]

theorem vermaCoord_e_pow (lam : Fin n → ℂ) {a : Fin n × Fin n} (ha : IsLower a) (m : ℕ) :
    vermaCoord lam (e a ^ m) = Finsupp.single (Finsupp.single a m) 1 := by
  have hnu : ¬ HasUpper (Finsupp.single a m) := by
    rintro ⟨b, hb, hne⟩
    have hba : b = a := by by_contra h; exact hne (by simp [Finsupp.single_apply, Ne.symm h])
    exact not_lower_of_upper hb (hba ▸ ha)
  have hlow : lowPart (Finsupp.single a m) = Finsupp.single a m := by
    ext b
    simp only [lowPart, Finsupp.filter_apply]
    split_ifs with hb
    · rfl
    · have : b ≠ a := fun h => hb (h ▸ ha)
      simp [Finsupp.single_apply, Ne.symm this]
  have hdiag : diagExp (Finsupp.single a m) = 0 := by
    ext i
    have : (i, i) ≠ a := fun h => not_lower_of_diag (a := (i, i)) rfl (h ▸ ha)
    simp [Finsupp.single_apply, Ne.symm this]
  rw [← canon_single, vermaCoord_canon_of_not lam hnu, hlow, hdiag]
  simp

theorem e_diag_mul_e_pow (k : Fin n) (a : Fin n × Fin n) (p : ℕ) :
    e (k, k) * e a ^ p = e a ^ p * e (k, k) + ((p : ℂ) * rootAt a k) • e a ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h : e (k, k) * e a = e a * e (k, k) + (rootAt a k : ℂ) • e a := by
      rw [← e_diag_mul_sub k a]; abel
    calc e (k, k) * e a ^ (p + 1) = (e (k, k) * e a ^ p) * e a := by rw [pow_succ, mul_assoc]
      _ = e a ^ p * (e (k, k) * e a) + ((p : ℂ) * rootAt a k) • (e a ^ p * e a) := by
          rw [ih, add_mul, mul_assoc, smul_mul_assoc]
      _ = e a ^ (p + 1) * e (k, k) + (((p + 1 : ℕ) : ℂ) * rootAt a k) • e a ^ (p + 1) := by
          rw [h, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ]
          push_cast
          rw [add_mul, one_mul, add_smul]
          abel

theorem hcEmb_mul_e_pow (a : Fin n × Fin n) (p : ℕ) (q : MvPolynomial (Fin n) ℂ) :
    hcEmb q * e a ^ p = e a ^ p * hcEmb (translate (fun k => (p : ℂ) * rootAt a k) q) := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [show translate (fun k => (p : ℂ) * rootAt a k) (C c) = C c by simp [translate],
      ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.commutes]
  | add q r hq hr => rw [map_add, add_mul, hq, hr, map_add, map_add, mul_add]
  | mul_X q k hq =>
    set T := translate (fun k => (p : ℂ) * rootAt a k)
    have hTX : hcEmb (T (X k)) = e (k, k) + ((p : ℂ) * rootAt a k) • 1 := by
      simp only [T, translate, aeval_X, map_add, hcEmb_X, ← MvPolynomial.algebraMap_eq,
        Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    calc hcEmb (q * X k) * e a ^ p = hcEmb q * (e (k, k) * e a ^ p) := by
          rw [map_mul, hcEmb_X, mul_assoc]
      _ = (hcEmb q * e a ^ p) * e (k, k) + ((p : ℂ) * rootAt a k) • (hcEmb q * e a ^ p) := by
          rw [e_diag_mul_e_pow, mul_add, mul_smul_comm, mul_assoc]
      _ = e a ^ p * (hcEmb (T q) * e (k, k) + ((p : ℂ) * rootAt a k) • hcEmb (T q)) := by
          rw [hq, mul_add, mul_smul_comm, mul_assoc]
      _ = e a ^ p * hcEmb (T (q * X k)) := by
          rw [map_mul T, map_mul hcEmb, hTX]
          simp only [mul_add, mul_smul_comm, mul_one]

section SimpleRoot

variable {i j : Fin n}

theorem rootAt_lower_self (hij : i ≠ j) : rootAt (j, i) i = -1 := by
  simp [rootAt, hij]

theorem rootAt_lower_other (hij : i ≠ j) : rootAt (j, i) j = 1 := by
  simp [rootAt, Ne.symm hij]

theorem rootAt_lower_of_ne {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) : rootAt (j, i) k = 0 := by
  simp [rootAt, hki, hkj]

theorem e_upper_mul_pow_mem (hij : (j : ℕ) = i + 1) (m : ℕ) :
    ∀ b : Fin n × Fin n, IsUpper b → b ≠ (i, j) → e b * e (j, i) ^ m ∈ nPlusU n := by
  induction m with
  | zero =>
    intro b hb _
    rw [pow_zero, mul_one]
    exact Submodule.subset_span ⟨1, b, hb, one_mul _⟩
  | succ m ih =>
    intro b hb hne
    have hc := e_mul_sub_mul b (j, i)
    have : e b * e (j, i) ^ (m + 1) = e (j, i) * (e b * e (j, i) ^ m) +
        ((if b.2 = j then e (b.1, i) else 0) - (if i = b.1 then e (j, b.2) else 0)) *
          e (j, i) ^ m := by
      rw [← hc, pow_succ']; noncomm_ring
    rw [this]
    refine Submodule.add_mem _ (mul_mem_nPlusU _ (ih b hb hne)) ?_
    rw [sub_mul]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs with h2
      · refine ih (b.1, i) ?_ ?_
        · simp only [IsUpper] at hb ⊢
          have h1 : b.1 ≠ i := fun h1 => hne (Prod.ext h1 h2)
          rw [Fin.lt_def] at hb ⊢
          rw [h2, hij] at hb
          have : (b.1 : ℕ) ≠ i := fun h => h1 (Fin.ext h)
          omega
        · intro h; simp only [Prod.mk.injEq] at h
          rw [h.2] at hij; omega
      · rw [zero_mul]; exact Submodule.zero_mem _
    · split_ifs with h1
      · refine ih (j, b.2) ?_ ?_
        · simp only [IsUpper] at hb ⊢
          have h2 : b.2 ≠ j := fun h2 => hne (Prod.ext h1.symm h2)
          rw [Fin.lt_def] at hb ⊢
          rw [← h1] at hb
          have : (b.2 : ℕ) ≠ j := fun h => h2 (Fin.ext h)
          omega
        · intro h; simp only [Prod.mk.injEq] at h
          have := congrArg Fin.val h.1; omega
      · rw [zero_mul]; exact Submodule.zero_mem _

theorem e_upper_simple_mul_pow_sub_mem (hij : (j : ℕ) = i + 1) (m : ℕ) :
    e (i, j) * e (j, i) ^ (m + 1) -
      (((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) - (((m : ℂ) + 1) * m) • e (j, i) ^ m)
      ∈ nPlusU n := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hxy : e (i, j) * e (j, i) = e (j, i) * e (i, j) + (e (i, i) - e (j, j)) := by
    have := e_mul_sub_mul (i, j) (j, i)
    simp only [if_true] at this
    rw [← this]; abel
  have hh : ∀ p : ℕ, (e (i, i) - e (j, j)) * e (j, i) ^ p =
      e (j, i) ^ p * (e (i, i) - e (j, j)) - (2 * (p : ℂ)) • e (j, i) ^ p := by
    intro p
    rw [sub_mul, e_diag_mul_e_pow, e_diag_mul_e_pow, rootAt_lower_self hne, rootAt_lower_other hne,
      mul_sub]
    module
  induction m with
  | zero =>
    simp only [pow_zero, pow_one, one_mul, Nat.cast_zero, zero_add, one_smul, mul_zero, zero_smul,
      sub_zero]
    rw [hxy, add_sub_cancel_right]
    exact Submodule.subset_span ⟨_, _, by simp only [IsUpper]; rw [Fin.lt_def, hij]; omega, rfl⟩
  | succ m ih =>
    have key : e (i, j) * e (j, i) ^ (m + 1 + 1) -
        ((((m + 1 : ℕ) : ℂ) + 1) • (e (j, i) ^ (m + 1) * (e (i, i) - e (j, j))) -
          ((((m + 1 : ℕ) : ℂ) + 1) * ((m + 1 : ℕ) : ℂ)) • e (j, i) ^ (m + 1)) =
        e (j, i) * (e (i, j) * e (j, i) ^ (m + 1) -
          (((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) -
            (((m : ℂ) + 1) * m) • e (j, i) ^ m)) := by
      have e1 : e (i, j) * e (j, i) ^ (m + 1 + 1) =
          e (j, i) * (e (i, j) * e (j, i) ^ (m + 1)) + (e (i, i) - e (j, j)) * e (j, i) ^ (m + 1) := by
        rw [pow_succ' _ (m + 1), ← mul_assoc, hxy, add_mul, mul_assoc]
      rw [e1, hh]
      simp only [mul_sub, sub_mul, mul_smul_comm, ← mul_assoc, ← pow_succ']
      push_cast
      module
    rw [key]
    exact mul_mem_nPlusU _ ih

end SimpleRoot

section Reflection

variable {i j : Fin n}

theorem pow_mul_h_sub_mem_vermaIdeal (lam : Fin n → ℂ) (m : ℕ) (hm : lam i - lam j = m) :
    e (j, i) ^ m * (e (i, i) - e (j, j)) - (m : ℂ) • e (j, i) ^ m ∈ vermaIdeal lam := by
  have : e (j, i) ^ m * (e (i, i) - e (j, j)) - (m : ℂ) • e (j, i) ^ m =
      e (j, i) ^ m * (e (i, i) - algebraMap ℂ (U n) (lam i)) -
        e (j, i) ^ m * (e (j, j) - algebraMap ℂ (U n) (lam j)) := by
    rw [← hm]
    simp only [mul_sub, sub_smul, ← Algebra.commutes, ← Algebra.smul_def]
    abel
  rw [this]
  exact Submodule.sub_mem _ (mul_e_sub_mem_vermaIdeal lam _ i) (mul_e_sub_mem_vermaIdeal lam _ j)

theorem mul_pow_mem_vermaIdeal (hij : (j : ℕ) = i + 1) (lam : Fin n → ℂ) (m : ℕ)
    (hm : lam i - lam j = m) {x : U n} (hx : x ∈ nPlusU n) :
    x * e (j, i) ^ (m + 1) ∈ vermaIdeal lam := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, b, hb, rfl⟩ := hx
    rw [mul_assoc]
    refine mul_mem_vermaIdeal lam u ?_
    by_cases hbij : b = (i, j)
    · subst hbij
      have h1 := e_upper_simple_mul_pow_sub_mem hij m
      have h2 := pow_mul_h_sub_mem_vermaIdeal lam m hm
      have : e (i, j) * e (j, i) ^ (m + 1) =
          (e (i, j) * e (j, i) ^ (m + 1) -
            (((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) -
              (((m : ℂ) + 1) * m) • e (j, i) ^ m)) +
          ((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j)) - (m : ℂ) • e (j, i) ^ m) := by
        rw [smul_sub, smul_smul]; abel
      rw [this]
      exact Submodule.add_mem _ (nPlusU_le_vermaIdeal lam h1) (Submodule.smul_mem _ _ h2)
    · exact nPlusU_le_vermaIdeal lam (e_upper_mul_pow_mem hij (m + 1) b hb hbij)
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem eval_eq_eval_reflect_of_nat (hij : (j : ℕ) = i + 1) {z : U n}
    (hz : z ∈ Subalgebra.center ℂ (U n)) (lam : Fin n → ℂ) (m : ℕ) (hm : lam i - lam j = m) :
    eval lam (hcProjLin z) =
      eval (lam + fun k => ((m : ℂ) + 1) * rootAt (j, i) k) (hcProjLin z) := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  set p := hcProjLin z
  set Y := e (n := n) (j, i) ^ (m + 1)
  have hN : z - hcEmb p ∈ nPlusU n :=
    sub_hcEmb_mem_nPlusU (commute_e_diag_of_mem (mem_centralizerT_of_mem_center hz))
  set c : Fin n → ℂ := fun k => ((m + 1 : ℕ) : ℂ) * rootAt (j, i) k with hc_def
  have hc : c = fun k => ((m : ℂ) + 1) * rootAt (j, i) k := by
    ext k; simp [c]
  have hA : Y * z - eval lam p • Y ∈ vermaIdeal lam := by
    have : Y * z - eval lam p • Y =
        Y * (z - hcEmb p) + Y * (hcEmb p - algebraMap ℂ (U n) (eval lam p)) := by
      rw [mul_sub, mul_sub, ← Algebra.commutes, ← Algebra.smul_def]; abel
    rw [this]
    exact Submodule.add_mem _ (nPlusU_le_vermaIdeal lam (mul_mem_nPlusU _ hN))
      (mul_mem_vermaIdeal lam _ (hcEmb_sub_eval_mem_vermaIdeal lam p))
  have hB : z * Y - eval (lam + c) p • Y ∈ vermaIdeal lam := by
    have h1 : hcEmb p * Y = Y * hcEmb (translate c p) := hcEmb_mul_e_pow (j, i) (m + 1) p
    have : z * Y - eval (lam + c) p • Y = (z - hcEmb p) * Y +
        Y * (hcEmb (translate c p) - algebraMap ℂ (U n) (eval lam (translate c p))) := by
      rw [eval_translate, mul_sub, ← Algebra.commutes, ← Algebra.smul_def, ← h1, sub_mul]; abel
    rw [this]
    exact Submodule.add_mem _ (mul_pow_mem_vermaIdeal hij lam m hm hN)
      (mul_mem_vermaIdeal lam _ (hcEmb_sub_eval_mem_vermaIdeal lam _))
  have hcomm : Y * z = z * Y := (Subalgebra.mem_center_iff.1 hz Y)
  have hdiff : (eval (lam + c) p - eval lam p) • Y ∈ vermaIdeal lam := by
    have := Submodule.sub_mem _ hA hB
    rw [hcomm, sub_sub_sub_cancel_left, ← sub_smul] at this
    exact this
  have hlow : IsLower (j, i) := by
    simp only [IsLower]; rw [Fin.lt_def, hij]; omega
  have h0 := vermaCoord_vermaIdeal lam hdiff
  rw [map_smul, vermaCoord_e_pow lam hlow, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_eq_zero, sub_eq_zero] at h0
  rw [← hc]
  exact h0.symm

theorem eval_aeval_reflect (r : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) (mu : Fin n → ℂ) :
    eval mu (aeval (fun k => X k + (X i - X j + 1) * C (r k)) q) =
      eval (mu + fun k => (mu i - mu j + 1) * r k) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, eval_add, eval_add, hp, hq]
  | mul_X p k hp =>
    rw [map_mul, eval_mul, eval_mul, hp]
    simp

theorem eq_of_eval_eq_of_sub_nat (hij : i ≠ j) {P Q : MvPolynomial (Fin n) ℂ}
    (h : ∀ lam : Fin n → ℂ, ∀ m : ℕ, lam i - lam j = m → eval lam P = eval lam Q) : P = Q := by
  let f : Fin n → MvPolynomial (Fin n) ℂ := fun k => if k = i then X i + X j else X k
  let g : Fin n → MvPolynomial (Fin n) ℂ := fun k => if k = i then X i - X j else X k
  have hgf : (aeval g).comp (aeval f) = AlgHom.id ℂ _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    by_cases hk : k = i
    · subst hk; simp [f, g, Ne.symm hij]
    · simp [f, g, hk]
  have heval : ∀ (x : Fin n → ℂ) (R : MvPolynomial (Fin n) ℂ),
      eval x (aeval f R) = eval (fun k => if k = i then x i + x j else x k) R := by
    intro x R
    induction R using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, eval_add, eval_add, hp, hq]
    | mul_X p k hp =>
      rw [map_mul, eval_mul, eval_mul, hp, aeval_X, eval_X]
      by_cases hk : k = i
      · subst hk; simp [f]
      · simp [f, hk]
  have hfPQ : aeval f P = aeval f Q := by
    refine MvPolynomial.funext_set
      (fun k => if k = i then Set.range (Nat.cast : ℕ → ℂ) else Set.univ) (fun k => ?_) fun x hx => ?_
    · split_ifs
      · exact Set.infinite_range_of_injective Nat.cast_injective
      · exact Set.infinite_univ
    · have hxi : x i ∈ Set.range (Nat.cast : ℕ → ℂ) := by
        simpa using hx i (Set.mem_univ i)
      obtain ⟨m, hm⟩ := hxi
      rw [heval, heval]
      refine h _ m ?_
      simp [Ne.symm hij, hm]
  have := congrArg (aeval g) hfPQ
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hgf, AlgHom.id_apply, AlgHom.id_apply] at this

theorem eval_eq_eval_reflect (hij : (j : ℕ) = i + 1) {z : U n}
    (hz : z ∈ Subalgebra.center ℂ (U n)) (lam : Fin n → ℂ) :
    eval lam (hcProjLin z) =
      eval (lam + fun k => (lam i - lam j + 1) * rootAt (j, i) k) (hcProjLin z) := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hpR : hcProjLin z =
      aeval (fun k => X k + (X i - X j + 1) * C ((rootAt (j, i) k : ℤ) : ℂ)) (hcProjLin z) := by
    refine eq_of_eval_eq_of_sub_nat hne fun mu m hm => ?_
    rw [eval_aeval_reflect, hm]
    exact eval_eq_eval_reflect_of_nat hij hz mu m hm
  conv_lhs => rw [hpR]
  rw [eval_aeval_reflect]

end Reflection

theorem rename_swap_harishChandraHom {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (z : Subalgebra.center ℂ (U n)) :
    rename (Equiv.swap i j) (harishChandraHom z) = harishChandraHom z := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hrho : rhoVec n i - rhoVec n j = 1 := by
    have : (j : ℂ) = (i : ℂ) + 1 := by exact_mod_cast hij
    simp only [rhoVec, this]; ring
  refine MvPolynomial.funext fun mu => ?_
  rw [eval_rename, eval_harishChandraHom, eval_harishChandraHom,
    eval_eq_eval_reflect hij z.2 (mu - rhoVec n)]
  have hv : mu ∘ ⇑(Equiv.swap i j) - rhoVec n = (mu - rhoVec n) + fun k =>
      ((mu - rhoVec n) i - (mu - rhoVec n) j + 1) * ((rootAt (j, i) k : ℤ) : ℂ) := by
    funext k
    simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply]
    by_cases hki : k = i
    · subst hki
      rw [Equiv.swap_apply_left, rootAt_lower_self hne]
      push_cast
      linear_combination (-1 : ℂ) * hrho
    · by_cases hkj : k = j
      · subst hkj
        rw [Equiv.swap_apply_right, rootAt_lower_other hne]
        push_cast
        linear_combination hrho
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, rootAt_lower_of_ne hki hkj]
        push_cast; ring
  rw [hv]

theorem harishChandraHom_isSymmetric (z : Subalgebra.center ℂ (U n)) :
    (harishChandraHom z).IsSymmetric := by
  intro σ
  rcases n with _ | n
  · have : σ = 1 := Equiv.ext fun x => x.elim0
    subst this
    simp
  · let S : Submonoid (Equiv.Perm (Fin (n + 1))) :=
      { carrier := {τ | rename τ (harishChandraHom z) = harishChandraHom z}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, Equiv.Perm.coe_mul] at *
          rw [← rename_rename, hb, ha] }
    have hle : Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) ≤ S := by
      rw [Submonoid.closure_le]
      rintro _ ⟨i, rfl⟩
      exact rename_swap_harishChandraHom (by simp) z
    rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hle
    exact hle (Submonoid.mem_top σ)

end GroundTheory.Automorphic.HarishChandra
