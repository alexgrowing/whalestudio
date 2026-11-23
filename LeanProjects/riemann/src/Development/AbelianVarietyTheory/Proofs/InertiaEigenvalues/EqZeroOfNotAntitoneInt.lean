import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HasGammaX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetProdMapProductEqProdProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaCellDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCellOfUnipotentIwahoriProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WhitTorus

theorem eq_zero_of_not_antitone_int (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (ψ : AddChar (w.adicCompletion E) ℂ)
    (hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w)
    (W : GL (Fin n) (w.adicCompletion E) → ℂ)
    (hWN : ∀ u ∈ unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (superDiag u) * W g)
    (hWK : ∀ g, ∀ k ∈ KGL w n, W (g * k) = W g)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (l : Fin n → ℤ) (hl : ¬ Antitone l)
    (D : GL (Fin n) (w.adicCompletion E))
    (hDv : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ ^ l a : (w.adicCompletion E)ˣ) : w.adicCompletion E)) :
    W D = 0 := by
  obtain ⟨i, j, hij, hlt⟩ : ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ l i < l j := by
    by_contra h
    push_neg at h
    apply hl
    cases n with
    | zero => exact fun a => a.elim0
    | succ m =>
      rw [Fin.antitone_iff_succ_le]
      intro k
      exact h k.castSucc k.succ (by simp)
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hlt' : i < j := Fin.lt_def.2 (by omega)
  have hnot : ((ϖ : w.adicCompletion E))⁻¹ ∉ Ov E w := by
    intro h
    change Valued.v (((ϖ : w.adicCompletion E))⁻¹) ≤ 1 at h
    rw [map_inv₀, hϖ, ← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe] at h
    exact absurd (Multiplicative.ofAdd_le.1 (h.trans_eq (ofAdd_zero).symm)) (by norm_num)
  obtain ⟨y, hy, hψy⟩ : ∃ y ∈ Ov E w, ψ (((ϖ : w.adicCompletion E))⁻¹ * y) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hnot ((hψ _).1 h)
  set x : w.adicCompletion E := ((ϖ : w.adicCompletion E))⁻¹ * y with hx
  have hϖ0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  set m : ℕ := (l j - l i).toNat with hm
  have hlj : l j = l i + (m : ℤ) := by omega
  have hm1 : 1 ≤ m := by omega
  have hdj : ((ϖ ^ l j : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      ((ϖ ^ l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * (ϖ : w.adicCompletion E) ^ m := by
    rw [hlj, _root_.zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  set c : w.adicCompletion E := (ϖ : w.adicCompletion E) ^ m * x with hc
  have hcO : c ∈ Ov E w := by
    have hϖO : (ϖ : w.adicCompletion E) ∈ Ov E w := mem_Ov_of_isUnifV hϖ
    have : c = (ϖ : w.adicCompletion E) ^ (m - 1) * y := by
      rw [hc, hx, ← mul_assoc, show m = (m - 1) + 1 by omega, pow_succ, mul_assoc _ (ϖ : w.adicCompletion E),
        mul_inv_cancel₀ hϖ0, mul_one, Nat.add_sub_cancel]
    rw [this]
    exact Subring.mul_mem _ (Subring.pow_mem _ hϖO _) hy
  let T : w.adicCompletion E → GL (Fin n) (w.adicCompletion E) := fun a =>
    ⟨Matrix.transvection i j a, Matrix.transvection i j (-a),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩
  have hT : ∀ a, ((T a : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.transvection i j a := fun a => rfl
  have hentry : ∀ {R : Type} [CommRing R] (a : R) (p q : Fin n), Matrix.transvection i j a p q =
      (if p = q then 1 else 0) + (if i = p ∧ j = q then a else 0) := by
    intro R _ a p q
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
  have hu : T x ∈ unipB (w.adicCompletion E) (Fin n) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hT, hentry, if_neg (fun h => by rw [h] at hqp; exact lt_irrefl _ hqp), if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hqp hlt'
    · rw [hT, hentry, if_pos rfl, if_neg, add_zero]
      rintro ⟨rfl, h⟩
      exact hne h.symm
  have hsd : superDiag (T x) = x := by
    unfold GlobalTheory.Whittaker.superDiag
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [hT, hentry, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]
      · intro b hb hbj
        have hb' := (Finset.mem_filter.1 hb).2
        rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hbj h.2.symm), add_zero]
      · intro hj
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, hij⟩) hj
    · intro a _ hai
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' := (Finset.mem_filter.1 hb).2
      rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hai h.1.symm), add_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hk : T c ∈ KGL w n := by
    refine ⟨⟨Matrix.transvection i j ⟨c, hcO⟩, Matrix.transvection i j (-⟨c, hcO⟩),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩, ?_⟩
    apply Units.ext
    ext p q
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hT]
    rw [hentry, hentry]
    split_ifs <;> simp
  have hkey : D * T c = T x * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hDv, hT, hT]
    ext p q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hentry, hentry]
    by_cases hpq : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [if_neg hne, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, zero_add, zero_add, hc, hdj]
      ring_nf
    · simp only [if_neg hpq, add_zero]
      split_ifs with h
      · subst h
        simp
      · simp
  have h1 := hWK D (T c) hk
  rw [hkey, hWN (T x) hu D, hsd] at h1
  have h2 : (ψ x - 1) * W D = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hψy)

theorem val_emb₂_tD_one (K : Type) [Field K] {m j n : ℕ} (hn : m + (j + 1) = n) (ϖ : Kˣ) (a : Fin m → ℤ) :
    ((emb₂ K (stdSum hn) (GlobalTheory.IwaCell.tD ϖ a, 1) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal fun k : Fin n => ((ϖ ^ (if h : (k : ℕ) < m then a ⟨k, h⟩ else 0) : Kˣ) : K) := by
  rw [val_emb₂]
  ext p q
  obtain ⟨p, rfl⟩ := (stdSum hn).surjective p
  obtain ⟨q, rfl⟩ := (stdSum hn).surjective q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [GlobalTheory.IwaCell.val_tD, Matrix.diagonal_apply, Matrix.one_apply]
  rw [show ((GlobalTheory.IwaCell.tD ϖ a : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = _ from GlobalTheory.SmGL.val_diagT K _]
  simp [Matrix.diagonal_apply]

theorem whittaker_value_emb₂_tD : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (m j n : ℕ)
    (hn : m + (j + 1) = n) (ψ : AddChar (w.adicCompletion E) ℂ),
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) →
    ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ),
    (∀ u ∈ unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (superDiag u) * W g) →
    (∀ g, ∀ k ∈ KGL w n, W (g * k) = W g) →
    (∀ ϖ, IsUnifV E w ϖ → ∀ i ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w n)
      (Tj ℂ n (Ov E w) ϖ i) W = satEig (qV E w) n (Finset.univ.val.map α) i • W) →
    ∀ ϖ : (w.adicCompletion E)ˣ, IsUnifV E w (ϖ : w.adicCompletion E) → ∀ a : Fin m → ℤ,
      W (emb₂ (w.adicCompletion E) (stdSum hn) (GlobalTheory.IwaCell.tD ϖ a, 1)) =
        if Antitone a ∧ ∀ i, 0 ≤ a i then
          GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) (GlobalTheory.JSW.padTo (Nat.le.intro hn) fun i => (a i).toNat) * W 1
        else 0 := by
  intro E _ _ w m j n hn ψ hψ W α hN hK hH ϖ hϖ a
  have hv := val_emb₂_tD_one (w.adicCompletion E) hn ϖ a
  split_ifs with ha
  · have hpow : ∀ i, ((ϖ ^ a i : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (ϖ : w.adicCompletion E) ^ (a i).toNat := by
      intro i
      conv_lhs => rw [← Int.toNat_of_nonneg (ha.2 i)]
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    have heq : emb₂ (w.adicCompletion E) (stdSum hn) (GlobalTheory.IwaCell.tD ϖ a, 1) =
        Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
          (MulEquiv.piUnits.symm fun i => ϖ ^ (GlobalTheory.JSW.padTo (Nat.le.intro hn) fun i => (a i).toNat) i) := by
      apply Units.ext
      rw [hv]
      ext p q
      by_cases hpq : p = q
      · subst hpq
        by_cases hp : (p : ℕ) < m
        · simp [Matrix.diagonal_apply, GlobalTheory.JSW.padTo, hp, hpow]
        · simp [Matrix.diagonal_apply, GlobalTheory.JSW.padTo, hp]
      · simp [Matrix.diagonal_apply, hpq]
    rw [heq]
    exact GlobalTheory.JSW.shintani_formula E w n ψ hψ W α hN hK hH ϖ hϖ _
  · refine eq_zero_of_not_antitone_int E w n ψ hψ W hN hK ϖ hϖ _ ?_ _ hv
    intro hanti
    apply ha
    refine ⟨fun p q hpq => ?_, fun i => ?_⟩
    · have := hanti (show (⟨p, by omega⟩ : Fin n) ≤ ⟨q, by omega⟩ from Fin.le_def.2 (Fin.le_def.1 hpq))
      simpa [p.2, q.2] using this
    · have := hanti (show (⟨i, by omega⟩ : Fin n) ≤ ⟨m, by omega⟩ from Fin.le_def.2 (show (i : ℕ) ≤ m by omega))
      simpa [i.2] using this

end GlobalTheory.WhitTorus
