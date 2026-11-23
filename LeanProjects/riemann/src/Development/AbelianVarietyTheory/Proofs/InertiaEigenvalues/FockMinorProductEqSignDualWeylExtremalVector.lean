import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenMDetNeZeroOfNontrivial

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries.DeltaExtremal

noncomputable def lead {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℂ :=
  if h : k ≤ n then (y.submatrix (Fin.castLE h) (Fin.castLE h)).det else 1

theorem lead_zero {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : lead y 0 = 1 := by
  simp [lead]

theorem lead_self {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : lead y n = y.det := by
  simp [lead]

theorem det_inv_rev {n k : ℕ} (hk : k ≤ n) (y : GL (Fin n) ℂ) :
    (Matrix.of fun a b : Fin k => (y⁻¹).val (Fin.rev (Fin.castLE hk a)) (Fin.rev (Fin.castLE hk b))).det =
      lead y.val (n - k) * (y.val.det)⁻¹ := by
  obtain ⟨e, hl, hr⟩ := GlobalTheory.ValCmp.exists_equiv_castLE_rev hk
  have hj := GlobalTheory.ValCmp.jacobi_blocks_of_mul (y.val.submatrix e e) ((y⁻¹).val.submatrix e e) 1 (by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, one_smul, Matrix.submatrix_one_equiv])
  have e1 : (y.val.submatrix e e).toBlocks₁₁ =
      y.val.submatrix (Fin.castLE (Nat.sub_le n k)) (Fin.castLE (Nat.sub_le n k)) := by
    ext a b
    simp [Matrix.toBlocks₁₁, hl]
  have e2 : ((y⁻¹).val.submatrix e e).toBlocks₂₂ =
      Matrix.of fun a b : Fin k => (y⁻¹).val (Fin.rev (Fin.castLE hk a)) (Fin.rev (Fin.castLE hk b)) := by
    ext a b
    simp only [Matrix.toBlocks₂₂, hr, Matrix.of_apply, Matrix.submatrix_apply]
  rw [e1, e2, one_pow, one_mul, Matrix.det_submatrix_equiv_self] at hj
  rw [← hj, lead, dif_pos (Nat.sub_le n k), Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

variable {D : D7} {m n : ℕ}

theorem aeval_minorPlus (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) {k : ℕ} (hk : k ≤ p τ) (hm : k ≤ m) (hn : k ≤ n) :
    MvPolynomial.aeval (fockPt p y) (minorPlus τ k : PolF D m n) = lead (y τ).val k := by
  rw [minorPlus, AlgHom.map_det, lead, dif_pos hn]
  congr 1
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  have h1 : b.val < m ∧ a.val < n := ⟨by omega, by omega⟩
  have h2 : b.val < p τ := by omega
  have h3 : b.val < n := by omega
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos h1, MvPolynomial.aeval_X, fockPt,
    if_pos h2, dif_pos h3, Matrix.submatrix_apply]
  rfl

theorem aeval_minorMinus (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) {k : ℕ} (hm : p τ + k ≤ m) (hn : k ≤ n) :
    MvPolynomial.aeval (fockPt p y) (minorMinus τ (p τ) k : PolF D m n) =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) : ℂ) * (lead (y τ).val (n - k) * ((y τ).val.det)⁻¹) := by
  rw [minorMinus, AlgHom.map_det, ← det_inv_rev hn, ← Matrix.det_permute', ← Matrix.det_transpose]
  congr 1
  ext b a
  have ha := a.isLt
  have hb := b.isLt
  have h1 : p τ + b.val < m ∧ n - k + a.val < n := ⟨by omega, by omega⟩
  have h2 : ¬ p τ + b.val < p τ := by omega
  have h3 : p τ + b.val - p τ < n := by omega
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos h1, MvPolynomial.aeval_X, fockPt,
    if_neg h2, dif_pos h3, Matrix.submatrix_apply, Matrix.transpose_apply, id]
  refine congrArg₂ _ (congrArg Fin.rev (Fin.ext ?_)) (Fin.ext ?_)
  · simp
  · simp only [Fin.revPerm_apply, Fin.val_rev, Fin.val_castLE]
    omega

theorem sum_drops (q : ℕ) (a : ℕ → ℕ) (h : ∀ i, i + 1 < q → a (i + 1) ≤ a i) :
    ∑ i ∈ Finset.range q, (a i - if i + 1 < q then a (i + 1) else 0) = if 0 < q then a 0 else 0 := by
  have := Finset.sum_range_sub' (fun i => if i < q then (a i : ℤ) else 0) q
  simp only [lt_irrefl, if_false, sub_zero] at this
  refine Nat.cast_injective (R := ℤ) ?_
  rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, ← this]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  have := h i
  split_ifs <;> omega

theorem prod_exponents {n p q : ℕ} (ap am : ℕ → ℕ) (c : ℤ) (lam : DomWeight n) (hle : p + q ≤ n)
    (hl : ∀ i : Fin n, lam.w i = (if i.val < p then (ap i : ℤ) else if n - q ≤ i.val then -(am (n - 1 - i) : ℤ) else 0) + c)
    (L : ℕ → ℂ) (h0 : L 0 = 1) (hd : L n ≠ 0) :
    L n ^ c * ((∏ i ∈ Finset.range p, L (i + 1) ^ (ap i - if i + 1 < p then ap (i + 1) else 0)) *
      ∏ i ∈ Finset.range q, (L (n - (i + 1)) * (L n)⁻¹) ^ (am i - if i + 1 < q then am (i + 1) else 0)) =
    L n ^ lam.detShift * ∏ s : Fin n, L (s + 1) ^ (lam.natW s - Formalism.GradedWeylDivisibility.nuNext lam.natW s) := by
  rcases n with _ | k
  · obtain rfl : p = 0 := by omega
    obtain rfl : q = 0 := by omega
    simp [h0]
  have hanti : ∀ i j (hi : i < k + 1) (hj : j < k + 1), i ≤ j → lam.w ⟨j, hj⟩ ≤ lam.w ⟨i, hi⟩ :=
    fun i j hi hj h => lam.anti (show (⟨i, hi⟩ : Fin (k + 1)) ≤ ⟨j, hj⟩ from h)
  have ham : ∀ i, i + 1 < q → am (i + 1) ≤ am i := by
    intro i hi
    have := hanti (k - (i + 1)) (k - i) (by omega) (by omega) (by omega)
    rw [hl, hl] at this
    dsimp only at this
    rw [show k + 1 - 1 - (k - i) = i by omega, show k + 1 - 1 - (k - (i + 1)) = i + 1 by omega] at this
    split_ifs at this <;> omega
  have hshift : lam.detShift = lam.w ⟨k, Nat.lt_succ_self k⟩ := by
    simp [DomWeight.detShift]
  set A : ℕ → ℕ := fun i => if i < p then ap i - if i + 1 < p then ap (i + 1) else 0 else 0 with hA
  set B : ℕ → ℕ := fun i => if i < q then am i - if i + 1 < q then am (i + 1) else 0 else 0 with hB
  have eA : (∏ i ∈ Finset.range p, L (i + 1) ^ (ap i - if i + 1 < p then ap (i + 1) else 0)) =
      (∏ i ∈ Finset.range k, L (i + 1) ^ A i) * L (k + 1) ^ A k := by
    rw [← Finset.prod_range_succ (fun i => L (i + 1) ^ A i),
      ← Finset.prod_subset (Finset.range_subset_range.2 (show p ≤ k + 1 by omega))
        (fun i _ hi => by rw [hA]; dsimp only; rw [if_neg (fun h => hi (Finset.mem_range.2 h)), pow_zero])]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hA]; dsimp only; rw [if_pos (Finset.mem_range.1 hi)]
  have eB : (∏ i ∈ Finset.range q, L (k + 1 - (i + 1)) ^ (am i - if i + 1 < q then am (i + 1) else 0)) =
      ∏ i ∈ Finset.range k, L (i + 1) ^ B (k - 1 - i) := by
    have : ∏ i ∈ Finset.range (k + 1), L (k + 1 - (i + 1)) ^ B i = ∏ i ∈ Finset.range k, L (i + 1) ^ B (k - 1 - i) := by
      rw [Finset.prod_range_succ, Nat.sub_self, h0, one_pow, mul_one, ← Finset.prod_range_reflect]
      refine Finset.prod_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show k + 1 - (k - 1 - i + 1) = i + 1 by omega]
    rw [← this, ← Finset.prod_subset (Finset.range_subset_range.2 (show q ≤ k + 1 by omega))
        (fun i _ hi => by rw [hB]; dsimp only; rw [if_neg (fun h => hi (Finset.mem_range.2 h)), pow_zero])]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hB]; dsimp only; rw [if_pos (Finset.mem_range.1 hi)]
  have eR : ∏ s : Fin (k + 1), L (s + 1) ^ (lam.natW s - Formalism.GradedWeylDivisibility.nuNext lam.natW s) =
      ∏ i ∈ Finset.range k, L (i + 1) ^ (A i + B (k - 1 - i)) := by
    rw [Fin.prod_univ_castSucc, show lam.natW (Fin.last k) = 0 by
      rw [DomWeight.natW, hshift]; simp [Fin.last], Nat.zero_sub, pow_zero, mul_one,
      ← Fin.prod_univ_eq_prod_range (fun i => L (i + 1) ^ (A i + B (k - 1 - i)))]
    refine Finset.prod_congr rfl fun s _ => ?_
    obtain ⟨s, hs⟩ := s
    have hs' : s + 1 < k + 1 := by omega
    simp only [Fin.castSucc_mk, Formalism.GradedWeylDivisibility.nuNext, dif_pos hs', DomWeight.natW, hshift]
    congr 1
    have a1 := hanti s (s + 1) (by omega) hs' (by omega)
    have a2 := hanti (s + 1) k hs' (by omega) (by omega)
    have b1 := hl ⟨s, by omega⟩
    have b2 := hl ⟨s + 1, hs'⟩
    dsimp only at b1 b2
    rw [show k + 1 - 1 - s = k - 1 - s + 1 by omega] at b1
    rw [show k + 1 - 1 - (s + 1) = k - 1 - s by omega] at b2
    rw [hA, hB]
    dsimp only
    split_ifs at b1 b2 ⊢ <;> omega
  have eS : lam.detShift = c + (A k : ℤ) - ((if 0 < q then am 0 else 0 : ℕ) : ℤ) := by
    rw [hshift, hl, hA]
    dsimp only
    rw [show k + 1 - 1 - k = 0 by omega]
    split_ifs <;> omega
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [eA, eB, eR, eS, sum_drops q am ham, zpow_sub₀ hd, zpow_add₀ hd, zpow_natCast, zpow_natCast]
  simp only [pow_add, Finset.prod_mul_distrib, inv_pow]
  ring

theorem eval_extremal (lam : D.what₂.Tau → DomWeight n) (y : GLR D n) (τ : D.what₂.Tau) :
    MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (y v.1).val v.2.1 v.2.2)
      (Formalism.GradedWeylDivisibility.blockEmb ℂ τ (extremal ℂ n (lam τ))) =
    ∏ s : Fin n, lead (y τ).val (s + 1) ^ ((lam τ).natW s - Formalism.GradedWeylDivisibility.nuNext (lam τ).natW s) := by
  rw [extremal, Formalism.GradedWeylDivisibility.hw, map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, map_pow, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det, RingHom.map_det, lead, dif_pos (Nat.succ_le_of_lt s.isLt)]
  congr 2
  ext a b
  simp [Formalism.GradedWeylDivisibility.blockEmb]

theorem harmFn_delta : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∃ s : ℤˣ, ∀ x, harmFn m w B (w.delta m) x = ((s : ℤ) : ℂ) * coefFn (RingHom.id ℂ) w.lam (ten fun τ => extremal ℂ n (w.lam τ)) (B⁻¹ * x) := by
  intro D m n w B hw hm
  refine ⟨∏ τ, ∏ i ∈ Finset.range (w.q τ), Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i + 1))) ^
    (w.am τ i - if i + 1 < w.q τ then w.am τ (i + 1) else 0), fun x => ?_⟩
  rw [harmFn_apply, coefFn, ten]
  generalize B⁻¹ * x = y
  rw [Weight.delta, Datum.delta, map_prod, map_prod]
  simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply, Int.cast_prod, Units.val_pow_eq_pow_val, Int.cast_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := hw.le τ
  have h2 := hm τ
  have hd : lead (y τ).val n ≠ 0 := by
    rw [lead_self]; exact (GeneralLinearGroup.det (y τ)).ne_zero
  rw [eval_extremal, ← lead_self, ← prod_exponents (w.ap τ) (w.am τ) (w.c τ) (w.lam τ) h1 (hw.lam_eq τ) _ (lead_zero _) hd,
    deltaAt, map_mul, map_prod, map_prod,
    Finset.prod_congr rfl fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_pow, aeval_minorPlus w.p y τ (by omega) (by omega) (by omega)],
    Finset.prod_congr (s₁ := Finset.range (w.q τ)) rfl fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_pow, aeval_minorMinus w.p y τ (by omega) (by omega), mul_pow, ← lead_self],
    Finset.prod_mul_distrib]
  ring

end GlobalTheory.ExportSeries.DeltaExtremal
