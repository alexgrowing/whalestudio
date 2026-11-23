import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Formalism.DegreeFormula.PointDegree.PowSum

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.CovTestDR

noncomputable section

namespace GlobalTheory.VdmFibre

def blockEquiv {N j : ℕ} (h : j ≤ N) : Fin j ⊕ Fin (N - j) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))

def blockPerm {N j : ℕ} (h : j ≤ N) (p : Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j))) : Equiv.Perm (Fin N) :=
  (blockEquiv h).permCongr (Equiv.sumCongr p.1 p.2)

theorem blockEquiv_inl {N j : ℕ} (h : j ≤ N) (a : Fin j) : ((blockEquiv h (Sum.inl a) : Fin N) : ℕ) = a := by
  simp [blockEquiv]

theorem blockEquiv_inr {N j : ℕ} (h : j ≤ N) (b : Fin (N - j)) :
    ((blockEquiv h (Sum.inr b) : Fin N) : ℕ) = j + b := by
  simp [blockEquiv]

theorem blockPerm_inl {N j : ℕ} (h : j ≤ N) (p : Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j))) (a : Fin j) :
    blockPerm h p (blockEquiv h (Sum.inl a)) = blockEquiv h (Sum.inl (p.1 a)) := by
  simp [blockPerm, Equiv.permCongr_apply]

theorem blockPerm_inr {N j : ℕ} (h : j ≤ N) (p : Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j))) (b : Fin (N - j)) :
    blockPerm h p (blockEquiv h (Sum.inr b)) = blockEquiv h (Sum.inr (p.2 b)) := by
  simp [blockPerm, Equiv.permCongr_apply]

theorem blockPerm_lt {N j : ℕ} (h : j ≤ N) (p : Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j))) (i : Fin N) :
    ((blockPerm h p i : Fin N) : ℕ) < j ↔ (i : ℕ) < j := by
  obtain ⟨s, rfl⟩ := (blockEquiv h).surjective i
  rcases s with a | b
  · rw [blockPerm_inl, blockEquiv_inl, blockEquiv_inl]; simp [a.2, (p.1 a).2]
  · rw [blockPerm_inr, blockEquiv_inr, blockEquiv_inr]; omega

theorem sign_blockPerm {N j : ℕ} (h : j ≤ N) (p : Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j))) :
    Equiv.Perm.sign (blockPerm h p) = Equiv.Perm.sign p.1 * Equiv.Perm.sign p.2 := by
  simp [blockPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

theorem degFl_rename_fibre {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (ρ : ι → Equiv.Perm (Fin N))
    (P : MvPolynomial (ι × Fin N) ℝ) :
    degFl ι N (rename (fun x : ι × Fin N => (x.1, ρ x.1 x.2)) P) =
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) * degFl ι N P := by
  set f : ι × Fin N → ι × Fin N := fun x => (x.1, ρ x.1 x.2) with hfdef
  have hinj : Function.Injective f := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    simp only [hfdef, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp [(ρ a).injective h2]
  have hsurj : Function.Surjective f := by
    rintro ⟨a, j⟩
    exact ⟨(a, (ρ a).symm j), by simp [hfdef]⟩
  have hexp : ∀ σ : ι → Equiv.Perm (Fin N), permExp (σ * ρ⁻¹) = (permExp σ).mapDomain f := by
    intro σ
    ext y
    obtain ⟨⟨a, i⟩, rfl⟩ := hsurj y
    rw [Finsupp.mapDomain_apply hinj]
    simp [permExp, hfdef, Pi.mul_apply, Pi.inv_apply]
  have hsgn : ∀ σ : ι → Equiv.Perm (Fin N),
      (∏ τ, ((Equiv.Perm.sign ((σ * ρ⁻¹) τ) : ℤ) : ℝ)) =
        (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * ∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ) := by
    intro σ
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [Pi.mul_apply, Pi.inv_apply, Equiv.Perm.sign_inv]
  have key : ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
        (rename f P).coeff (permExp σ) =
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) * ∑ σ : ι → Equiv.Perm (Fin N),
        (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * P.coeff (permExp σ) := by
    rw [← Equiv.sum_comp (Equiv.mulRight (ρ⁻¹ : ι → Equiv.Perm (Fin N))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Equiv.coe_mulRight, hsgn, hexp, coeff_rename_mapDomain _ hinj]
    ring
  unfold degFl
  rw [key]
  ring

theorem rename_pLow {ι : Type} [Fintype ι] [DecidableEq ι] {N j : ℕ} (h : j ≤ N)
    (w : ι → Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j))) (τ : ι) :
    rename (fun x : ι × Fin N => (x.1, blockPerm h (w x.1) x.2)) (pLow j τ 1 : Pol ι N) = pLow j τ 1 := by
  simp only [pLow, map_sum, map_pow, rename_X, Finset.sum_filter]
  rw [← Equiv.sum_comp (blockPerm h (w τ)) (fun i : Fin N => if (i : ℕ) < j then (X (τ, i) : Pol ι N) ^ 1 else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [blockPerm_lt]
  split_ifs <;> simp

theorem rename_pHigh {ι : Type} [Fintype ι] [DecidableEq ι] {N j : ℕ} (h : j ≤ N)
    (w : ι → Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j))) (τ : ι) :
    rename (fun x : ι × Fin N => (x.1, blockPerm h (w x.1) x.2)) (pHigh j τ 1 : Pol ι N) = pHigh j τ 1 := by
  simp only [pHigh, map_sum, map_pow, rename_X, Finset.sum_filter]
  rw [← Equiv.sum_comp (blockPerm h (w τ)) (fun i : Fin N => if j ≤ (i : ℕ) then (X (τ, i) : Pol ι N) ^ 1 else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := blockPerm_lt h (w τ) i
  simp only [← not_lt, this]
  split_ifs <;> simp

theorem rename_lamA {ι : Type} [Fintype ι] [DecidableEq ι] {N j : ℕ} (h : j ≤ N)
    (w : ι → Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j))) :
    rename (fun x : ι × Fin N => (x.1, blockPerm h (w x.1) x.2)) (lamA ι N j) = lamA ι N j := by
  simp only [lamA, map_sum, map_sub, rename_pLow, rename_pHigh]

theorem sign_revPerm_cast {R : Type} [CommRing R] (n : ℕ) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) = (-1) ^ (∑ i : Fin n, (i : ℕ)) := by
  induction n with
  | zero =>
    rw [Subsingleton.elim (Fin.revPerm : Equiv.Perm (Fin 0)) 1]; simp
  | succ n ih =>
    have key : finRotate (n + 1) * (Fin.revPerm : Equiv.Perm (Fin (n + 1))) =
        Equiv.Perm.decomposeFin.symm (0, (Fin.revPerm : Equiv.Perm (Fin n))) := by
      ext i
      cases i using Fin.cases with
      | zero => simp
      | succ j =>
        simp [Equiv.Perm.decomposeFin_symm_apply_succ, Fin.rev_succ]
    have hs := congrArg Equiv.Perm.sign key
    rw [Equiv.Perm.sign_mul, sign_finRotate, Equiv.Perm.decomposeFin.symm_sign] at hs
    simp only [if_true, one_mul, Nat.add_sub_cancel] at hs
    rw [Fin.sum_univ_castSucc, pow_add]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [← ih]
    have : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (n + 1))) =
        (-1) ^ n * Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) := by
      rw [← hs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
    rw [this]; push_cast; ring

theorem sum_rev_val (n : ℕ) : ∑ i : Fin n, (n - 1 - (i : ℕ)) = ∑ i : Fin n, (i : ℕ) := by
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Fin.val_rev]
  omega

theorem vdm_alt {R : Type} [CommRing R] (n : ℕ) (v : Fin n → R) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ a : Fin n, (-v (σ a)) ^ (n - 1 - (a : ℕ)) =
      ∏ a : Fin n, ∏ b : Fin n, if a < b then v b - v a else 1 := by
  have hM : (Matrix.of fun i k : Fin n => (-v i) ^ (n - 1 - (k : ℕ))) =
      (Matrix.vandermonde (fun i => -v i)).submatrix id Fin.revPerm := by
    ext i k
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply, Fin.revPerm_apply,
      Fin.val_rev]
    congr 1; omega
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_apply', Matrix.det_permute', Matrix.det_vandermonde] at hdet
  simp only [Matrix.of_apply] at hdet
  rw [hdet]
  have hterm : ∀ i : Fin n, ∏ k ∈ Finset.Ioi i, (-v k - -v i) =
      (-1) ^ (n - 1 - (i : ℕ)) * ∏ b : Fin n, if i < b then v b - v i else 1 := by
    intro i
    rw [show (∏ k ∈ Finset.Ioi i, (-v k - -v i)) = ∏ k ∈ Finset.Ioi i, -(v k - v i) from
      Finset.prod_congr rfl fun _ _ => by ring, Finset.prod_neg, Fin.card_Ioi, ← Finset.prod_filter]
    congr 2
    ext b; simp
  simp only [hterm, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_rev_val, sign_revPerm_cast]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

theorem vdmLow_reindex {ι : Type} {N j : ℕ} (h : j ≤ N) (τ : ι) :
    (∏ a : Fin N, ∏ b : Fin N, if a < b ∧ (b : ℕ) < j then (X (τ, b) - X (τ, a) : MvPolynomial (ι × Fin N) ℝ) else 1) =
      ∏ a : Fin j, ∏ b : Fin j, if a < b then
        (X (τ, blockEquiv h (Sum.inl b)) - X (τ, blockEquiv h (Sum.inl a)) : MvPolynomial (ι × Fin N) ℝ) else 1 := by
  rw [← (blockEquiv h).prod_comp, Fintype.prod_sum_type]
  rw [Finset.prod_eq_one (s := Finset.univ) (f := fun b' : Fin (N - j) => ∏ b : Fin N,
      if blockEquiv h (Sum.inr b') < b ∧ (b : ℕ) < j then
        (X (τ, b) - X (τ, blockEquiv h (Sum.inr b')) : MvPolynomial (ι × Fin N) ℝ) else 1)
    (fun b' _ => Finset.prod_eq_one fun b _ => if_neg fun hh => by
      have := Fin.lt_def.1 hh.1; rw [blockEquiv_inr] at this; omega), mul_one]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← (blockEquiv h).prod_comp, Fintype.prod_sum_type]
  rw [Finset.prod_eq_one (s := Finset.univ) (f := fun b' : Fin (N - j) =>
      if blockEquiv h (Sum.inl a) < blockEquiv h (Sum.inr b') ∧ ((blockEquiv h (Sum.inr b') : Fin N) : ℕ) < j then
        (X (τ, blockEquiv h (Sum.inr b')) - X (τ, blockEquiv h (Sum.inl a)) : MvPolynomial (ι × Fin N) ℝ) else 1)
    (fun b' _ => if_neg fun hh => by have := hh.2; rw [blockEquiv_inr] at this; omega), mul_one]
  refine Finset.prod_congr rfl fun b _ => ?_
  have hb := b.2
  simp only [Fin.lt_def, blockEquiv_inl, hb, and_true]

theorem vdmHigh_reindex {ι : Type} {N j : ℕ} (h : j ≤ N) (τ : ι) :
    (∏ a : Fin N, ∏ b : Fin N, if a < b ∧ j ≤ (a : ℕ) then (X (τ, b) - X (τ, a) : MvPolynomial (ι × Fin N) ℝ) else 1) =
      ∏ a : Fin (N - j), ∏ b : Fin (N - j), if a < b then
        (X (τ, blockEquiv h (Sum.inr b)) - X (τ, blockEquiv h (Sum.inr a)) : MvPolynomial (ι × Fin N) ℝ) else 1 := by
  rw [← (blockEquiv h).prod_comp, Fintype.prod_sum_type]
  rw [Finset.prod_eq_one (s := Finset.univ) (f := fun a' : Fin j => ∏ b : Fin N,
      if blockEquiv h (Sum.inl a') < b ∧ j ≤ ((blockEquiv h (Sum.inl a') : Fin N) : ℕ) then
        (X (τ, b) - X (τ, blockEquiv h (Sum.inl a')) : MvPolynomial (ι × Fin N) ℝ) else 1)
    (fun a' _ => Finset.prod_eq_one fun b _ => if_neg fun hh => by
      have := hh.2; rw [blockEquiv_inl] at this; have := a'.2; omega), one_mul]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← (blockEquiv h).prod_comp, Fintype.prod_sum_type]
  rw [Finset.prod_eq_one (s := Finset.univ) (f := fun b' : Fin j =>
      if blockEquiv h (Sum.inr a) < blockEquiv h (Sum.inl b') ∧ j ≤ ((blockEquiv h (Sum.inr a) : Fin N) : ℕ) then
        (X (τ, blockEquiv h (Sum.inl b')) - X (τ, blockEquiv h (Sum.inr a)) : MvPolynomial (ι × Fin N) ℝ) else 1)
    (fun b' _ => if_neg fun hh => by
      have := Fin.lt_def.1 hh.1; rw [blockEquiv_inr, blockEquiv_inl] at this; have := b'.2; omega), one_mul]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [Fin.lt_def, blockEquiv_inr, Nat.le_add_right, and_true, Nat.add_lt_add_iff_left]

theorem fibPt_blocks {ι : Type} [Fintype ι] {N j : ℕ} (h : j ≤ N) :
    fibPt ι N j = ∏ τ : ι, ((∏ a : Fin j, (-X (τ, blockEquiv h (Sum.inl a))) ^ (j - 1 - (a : ℕ))) *
      ∏ b : Fin (N - j), (-X (τ, blockEquiv h (Sum.inr b))) ^ (N - j - 1 - (b : ℕ))) := by
  unfold fibPt
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← (blockEquiv h).prod_comp, Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [blockEquiv_inl, if_pos a.2]
  · refine Finset.prod_congr rfl fun b _ => ?_
    rw [blockEquiv_inr, if_neg (by omega)]
    congr 1; omega

theorem antisym_fibPt {ι : Type} [Fintype ι] [DecidableEq ι] {N j : ℕ} (h : j ≤ N) :
    ∑ w : ι → Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j)),
      C (∏ τ, ((Equiv.Perm.sign (w τ).1 : ℤ) : ℝ) * ((Equiv.Perm.sign (w τ).2 : ℤ) : ℝ)) *
        rename (fun x : ι × Fin N => (x.1, blockPerm h (w x.1) x.2)) (fibPt ι N j) =
    ∏ τ : ι, ((∏ a : Fin N, ∏ b : Fin N, if a < b ∧ (b : ℕ) < j then X (τ, b) - X (τ, a) else 1) *
      (∏ a : Fin N, ∏ b : Fin N, if a < b ∧ j ≤ (a : ℕ) then X (τ, b) - X (τ, a) else 1)) := by
  simp only [vdmLow_reindex h, vdmHigh_reindex h]
  simp only [← vdm_alt]
  rw [fibPt_blocks h]
  simp only [map_prod, map_mul, map_pow, map_neg, rename_X, blockPerm_inl, blockPerm_inr]
  simp only [map_intCast, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  rw [Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun w => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => by ring

theorem degFl_lamA_pow_vdmCl : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j k : ℕ), j ≤ N →
    degFl ι N (lamA ι N j ^ k * vdmCl ι N j) = degFl ι N (lamA ι N j ^ k * fibPt ι N j) := by
  intro ι _ _ N j k h
  set G := lamA ι N j ^ k
  set sg : (ι → Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j))) → ℝ :=
    fun w => ∏ τ, ((Equiv.Perm.sign (w τ).1 : ℤ) : ℝ) * ((Equiv.Perm.sign (w τ).2 : ℤ) : ℝ) with hsg
  set c : ℝ := ((Nat.factorial j : ℝ)⁻¹ * (Nat.factorial (N - j) : ℝ)⁻¹) ^ Fintype.card ι with hc
  have hv : vdmCl ι N j = C c * ∑ w : ι → Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j)),
      C (sg w) * rename (fun x : ι × Fin N => (x.1, blockPerm h (w x.1) x.2)) (fibPt ι N j) := by
    rw [antisym_fibPt h, vdmCl, hc, ← Finset.card_univ, ← Finset.prod_const, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [map_mul]; ring
  have hterm : ∀ w : ι → Equiv.Perm (Fin j) × Equiv.Perm (Fin (N - j)),
      degFl ι N (G * (C (sg w) * rename (fun x : ι × Fin N => (x.1, blockPerm h (w x.1) x.2)) (fibPt ι N j))) =
        degFl ι N (G * fibPt ι N j) := by
    intro w
    have hG : rename (fun x : ι × Fin N => (x.1, blockPerm h (w x.1) x.2)) G = G := by
      simp only [G, map_pow, rename_lamA h w]
    rw [mul_left_comm, PPowSum.degFl_C_mul, ← hG, ← map_mul, hG]
    rw [degFl_rename_fibre (fun τ => blockPerm h (w τ)), ← mul_assoc]
    have : sg w * ∏ τ, ((Equiv.Perm.sign (blockPerm h (w τ)) : ℤ) : ℝ) = 1 := by
      rw [hsg, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [sign_blockPerm]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (w τ).1) with h1 | h1 <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign (w τ).2) with h2 | h2 <;> simp [h1, h2]
    rw [this, one_mul]
  rw [hv, mul_left_comm, PPowSum.degFl_C_mul, Finset.mul_sum, PPowSum.degFl_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc]
  convert one_mul _
  rw [hc, Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
  have h1 : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have h2 : (Nat.factorial (N - j) : ℝ) ≠ 0 := by positivity
  push_cast
  rw [← mul_pow]
  field_simp
  exact one_pow _

end GlobalTheory.VdmFibre
