import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NewtonPowerSeriesSurjectiveLinearizationSolution
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesTaylorSubstFirstOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffHasse

open Polynomial

namespace GlobalTheory.PicDiv.DeformZerosHasse

variable {k J I : Type} [Field k] [Fintype J] [Fintype I]

noncomputable def sys (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k)
    (x : J ⊕ I → PowerSeries k) : Option (I × Fin N) → PowerSeries k
  | none => ∑ j, x (Sum.inl j) * ξ j
  | some (i, l) => ∑ j, x (Sum.inl j) *
      ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (x (Sum.inr i)) : PowerSeries k)

noncomputable def linFun (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k)
    (v : J ⊕ I → k) : Option (I × Fin N) → k
  | none => ∑ j, v (Sum.inl j) * PowerSeries.constantCoeff (ξ j)
  | some (i, l) => ∑ j, v (Sum.inl j) *
        PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
      + v (Sum.inr i) * ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j))

noncomputable def lin (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k) :
    (J ⊕ I → k) →ₗ[k] (Option (I × Fin N) → k) where
  toFun := linFun N ξ s y₀
  map_add' v w := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, add_mul, Finset.sum_add_distrib] <;> ring
  map_smul' c v := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, Finset.mul_sum, mul_assoc, mul_add]

lemma cc_subst (φ a : PowerSeries k) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ :=
  (GlobalTheory.taylor_subst_first_order k φ a 0 1 le_rfl ha).1

end GlobalTheory.PicDiv.DeformZerosHasse

namespace GlobalTheory.PicDiv.DeformZerosHasse

variable {k : Type} [Field k]

lemma dvd_step {m : ℕ} (hm : 1 ≤ m) (y g S S' : PowerSeries k) (y0 c A : k)
    (hy : PowerSeries.constantCoeff y = y0) (hS : PowerSeries.constantCoeff S = A)
    (hT : (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      S' - S - PowerSeries.X ^ m * PowerSeries.C c) :
    (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      (y + PowerSeries.X ^ m * g) * S' - y * S
        - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c) := by
  obtain ⟨r, hr⟩ := hT
  have hS' : S' = S + PowerSeries.X ^ m * PowerSeries.C c + PowerSeries.X ^ (m + 1) * r := by
    linear_combination hr
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have heq : (y + PowerSeries.X ^ (n + 1) * g) * S' - y * S
      - PowerSeries.X ^ (n + 1) * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c)
      = PowerSeries.X ^ (n + 1) * (y * PowerSeries.C c - PowerSeries.C (y0 * c)
          + (g * S - PowerSeries.C (PowerSeries.constantCoeff g * A)))
        + PowerSeries.X ^ (n + 1 + 1) * (y * r + PowerSeries.X ^ n *
          (g * PowerSeries.C c + PowerSeries.X * g * r)) := by
    rw [hS', map_add]; ring
  rw [heq]
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [pow_succ]
  refine mul_dvd_mul_left _ ?_
  rw [PowerSeries.X_dvd_iff]
  simp [hy, hS]

end GlobalTheory.PicDiv.DeformZerosHasse

namespace GlobalTheory.PicDiv.DeformZerosHasse

theorem deform : ∀ (k J I : Type) [Field k] [Fintype J] [Fintype I] (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k), 1 ≤ N → (N : k) ≠ 0 →
 ∑ j, y₀ j * PowerSeries.constantCoeff (ξ j) = 0 →
 (∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (s i j) = 0) → (∀ i, ∑ j, y₀ j * PowerSeries.coeff N (s i j) ≠ 0) →
 (∀ (e₀ : k) (e : I → ℕ → k), ∃ h : J → k, ∑ j, h j * PowerSeries.constantCoeff (ξ j) = e₀ ∧ ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (s i j) = e i l) →
 ∃ (y : J → PowerSeries k) (a : I → PowerSeries k), (∀ j, PowerSeries.constantCoeff (y j) = y₀ j) ∧ (∀ i, PowerSeries.constantCoeff (a i) = 0) ∧
   ∑ j, y j * ξ j = 0 ∧ ∀ i, ∀ l < N, ∑ j, y j * ((GlobalTheory.PicDiv.hasse l (s i j)).subst (a i) : PowerSeries k) = 0 := by
  intro k J I _ _ _ N ξ s y₀ hN hNk h0 hlow hN' hsurj
  have hA : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l f)
      = PowerSeries.coeff l f := fun f l => GlobalTheory.PicDiv.constantCoeff_hasse l f
  have hB : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l f)
      = ((l + 1 : ℕ) : k) * PowerSeries.coeff (l + 1) f := fun f l => GlobalTheory.PicDiv.coeff_one_hasse l f
  have hsur : Function.Surjective (lin N ξ s y₀) := by
    intro w
    obtain ⟨hv, hv0, hvl⟩ := hsurj (w none)
      (fun i l => if hl : l < N then w (some (i, ⟨l, hl⟩)) else 0)
    have hN1 : N - 1 < N := by omega
    have hS : ∀ i, ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse (N - 1) (s i j)) ≠ 0 := by
      intro i
      simp only [hB]
      have e1 : N - 1 + 1 = N := by omega
      rw [e1]
      calc ∑ j, y₀ j * (((N : ℕ) : k) * PowerSeries.coeff N (s i j))
          = ((N : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff N (s i j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≠ 0 := mul_ne_zero hNk (hN' i)
    refine ⟨Sum.elim hv (fun i => (w (some (i, ⟨N - 1, hN1⟩)) - ∑ j, hv j *
        PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse (N - 1) (s i j))) /
        ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse (N - 1) (s i j))), ?_⟩
    funext e
    rcases e with _ | ⟨i, l⟩
    · simpa [lin, linFun] using hv0
    · simp only [lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
      rcases Nat.lt_or_ge (l.1 + 1) N with hl | hl
      · have h1 : ∑ j, hv j * PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
            = w (some (i, l)) := by
          simp only [hA]
          have := hvl i l.1 hl
          rw [dif_pos l.2] at this
          exact this
        have h2 : ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)) = 0 := by
          simp only [hB]
          calc ∑ j, y₀ j * (((l.1 + 1 : ℕ) : k) * PowerSeries.coeff (l.1 + 1) (s i j))
              = ((l.1 + 1 : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff (l.1 + 1) (s i j) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [hlow i (l.1 + 1) (by omega), mul_zero]
        rw [h1, h2, mul_zero, add_zero]
      · have hl' : l = ⟨N - 1, hN1⟩ := Fin.ext (by simp; omega)
        subst hl'
        rw [div_mul_cancel₀ _ (hS i)]
        ring
  have hbase : ∀ e, PowerSeries.constantCoeff
      (sys N ξ s (fun i => PowerSeries.C (Sum.elim y₀ 0 i)) e) = 0 := by
    intro e
    rcases e with _ | ⟨i, l⟩
    · simp [sys, map_sum, h0]
    · simp only [sys, map_sum, map_mul, PowerSeries.constantCoeff_C, Sum.elim_inl, Sum.elim_inr]
      have h' : ∀ j, PowerSeries.constantCoeff ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst
          (PowerSeries.C ((0 : I → k) i)) : PowerSeries k) = PowerSeries.coeff l.1 (s i j) := by
        intro j; rw [cc_subst _ _ (by simp), hA]
      simp only [h']
      exact hlow i l.1 l.2
  have htay : ∀ (x h : J ⊕ I → PowerSeries k) (m : ℕ), 1 ≤ m →
      (∀ i, PowerSeries.constantCoeff (x i) = Sum.elim y₀ 0 i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ sys N ξ s (fun i => x i + PowerSeries.X ^ m * h i) e
        - sys N ξ s x e - PowerSeries.X ^ m *
          PowerSeries.C (lin N ξ s y₀ (fun i => PowerSeries.constantCoeff (h i)) e) := by

    intro x h m hm hx0 e
    rcases e with _ | ⟨i, l⟩
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl]
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) * ξ j - ∑ j, x (Sum.inl j) * ξ j
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))
          = PowerSeries.X ^ m * (∑ j, h (Sum.inl j) * ξ j - PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))) := by
        rw [mul_sub, Finset.mul_sum]; simp only [add_mul, Finset.sum_add_distrib, mul_assoc]; ring
      rw [heq, pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [PowerSeries.X_dvd_iff]
      simp [map_sum]
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk]
      set a := x (Sum.inr i)
      set b := h (Sum.inr i)
      have ha : PowerSeries.constantCoeff a = 0 := by simpa using hx0 (Sum.inr i)
      have key : ∀ j, (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
          (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)))) := by
        intro j
        have T := GlobalTheory.taylor_subst_first_order k (GlobalTheory.PicDiv.hasse l.1 (s i j)) a b m hm ha
        exact dvd_step hm _ _ _ _ _ _ _ (by simpa using hx0 (Sum.inl j)) T.1 T.2
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - ∑ j, x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + PowerSeries.constantCoeff b * ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)))
          = ∑ j, ((x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j))))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum,
          Finset.sum_add_distrib, Finset.mul_sum (a := PowerSeries.constantCoeff b)]
        congr 4
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [heq]
      exact Finset.dvd_sum fun j _ => key j
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.newton_powerSeries_target k (J ⊕ I) (Option (I × Fin N)) (sys N ξ s) (Sum.elim y₀ 0)
    (lin N ξ s y₀) hsur hbase htay
  refine ⟨fun j => x (Sum.inl j), fun i => x (Sum.inr i), fun j => by simpa using hx0 (Sum.inl j),
    fun i => by simpa using hx0 (Sum.inr i), hx none, ?_⟩
  intro i l hl
  exact hx (some (i, ⟨l, hl⟩))

end GlobalTheory.PicDiv.DeformZerosHasse
