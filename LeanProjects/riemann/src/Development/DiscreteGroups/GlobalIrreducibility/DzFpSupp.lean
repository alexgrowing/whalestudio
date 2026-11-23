import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFpMat

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzFp

variable {k : Type} [Field k]

theorem eq_zero_of_eq_inv_mul {ψ : AddChar k Circle} {s : k} (hs : ψ s ≠ 1) {z : ℂ}
    (h : z = (((ψ s)⁻¹ : Circle) : ℂ) * z) : z = 0 := by
  have hc : ((ψ s)⁻¹ : Circle) ≠ 1 := by rwa [ne_eq, inv_eq_one]
  have hc' : (((ψ s)⁻¹ : Circle) : ℂ) ≠ 1 := fun h' => hc (Circle.ext (by rw [h', Circle.coe_one]))
  have h0 : ((((ψ s)⁻¹ : Circle) : ℂ) - 1) * z = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hc')

theorem vanish_perm {k' : ℕ} (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (W : GL (Fin (k' + 1)) k → ℂ)
    (h1 : ∀ u ∈ unipB k (Fin (k' + 1)), ∀ x, W (u * x) = (((ψ (superDiag u))⁻¹ : Circle) : ℂ) * W x)
    (h2 : ∀ b ∈ lowB k (k' + 1), ∀ x, W (x * b) = W x)
    (π : Equiv.Perm (Fin (k' + 1))) (hπ : π ≠ 1) (b : GL (Fin (k' + 1)) k) (hb : b ∈ lowB k (k' + 1)) :
    W (GroundTheory.Automorphic.permGL k π * b) = 0 := by
  obtain ⟨i, hi⟩ := exists_descent π⁻¹ (inv_ne_one.2 hπ)
  obtain ⟨s, hs⟩ := AddChar.ne_one_iff.1 hψ
  have hne : i.succ ≠ i.castSucc := (ne_of_lt Fin.castSucc_lt_succ).symm
  have ha : (Pi.single i.castSucc s : Fin (k' + 1) → k) i.succ = 0 := by rw [Pi.single_apply, if_neg hne]
  have hemem : colElt (Pi.single i.castSucc s) i.succ ha ∈ unipB k (Fin (k' + 1)) := colElt_mem _ _ ha fun r hr => by
    rw [Pi.single_apply, if_neg (ne_of_gt (lt_trans Fin.castSucc_lt_succ hr))]
  have hesd : superDiag (colElt (Pi.single i.castSucc s) i.succ ha) = s := by
    rw [superDiag_colElt, Pi.single_eq_same]
  have hf : (GroundTheory.Automorphic.permGL k π)⁻¹ * colElt (Pi.single i.castSucc s) i.succ ha *
      GroundTheory.Automorphic.permGL k π ∈ lowB k (k' + 1) := by
    refine mem_lowB.2 fun r c hrc => ?_
    rw [permConj_apply, colElt_apply, Matrix.one_apply_ne (π.injective.ne (ne_of_lt hrc))]
    by_cases hc : π c = i.succ
    · have hr : π r ≠ i.castSucc := by
        intro hr
        have h1' : π⁻¹ i.succ = c := by rw [← hc]; simp
        have h2' : π⁻¹ i.castSucc = r := by rw [← hr]; simp
        rw [h1', h2'] at hi
        exact absurd hrc (not_lt.2 hi.le)
      rw [if_pos hc, Pi.single_apply, if_neg hr, zero_add]
    · rw [if_neg hc, zero_add]
  have key : W (GroundTheory.Automorphic.permGL k π * b) =
      (((ψ s)⁻¹ : Circle) : ℂ) * W (GroundTheory.Automorphic.permGL k π * b) := by
    have e1 : colElt (Pi.single i.castSucc s) i.succ ha * (GroundTheory.Automorphic.permGL k π * b) =
        GroundTheory.Automorphic.permGL k π * (((GroundTheory.Automorphic.permGL k π)⁻¹ *
          colElt (Pi.single i.castSucc s) i.succ ha * GroundTheory.Automorphic.permGL k π) * b) := by group
    have := h1 _ hemem (GroundTheory.Automorphic.permGL k π * b)
    rw [hesd, e1, h2 _ (mul_mem hf hb), ← h2 b hb (GroundTheory.Automorphic.permGL k π)] at this
    exact this
  exact eq_zero_of_eq_inv_mul hs key

theorem supp {m : ℕ} (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (W : GL (Fin m) k → ℂ)
    (h1 : ∀ u ∈ unipB k (Fin m), ∀ x, W (u * x) = (((ψ (superDiag u))⁻¹ : Circle) : ℂ) * W x)
    (h2 : ∀ b ∈ lowB k m, ∀ x, W (x * b) = W x) (x : GL (Fin m) k) (hx : W x ≠ 0) :
    ∃ u ∈ unipB k (Fin m), ∃ b ∈ lowB k m, x = u * b := by
  cases m with
  | zero => exact ⟨1, one_mem _, x, mem_lowB.2 fun i => i.elim0, (one_mul x).symm⟩
  | succ k' =>
  have hww : ∀ z, longElt (k' + 1) k * (longElt (k' + 1) k * z) = z := fun z => by
    rw [← mul_assoc, longElt_mul_self, one_mul]
  obtain ⟨σ, hσ⟩ := GroundTheory.Automorphic.exists_mem_doubleCoset_permGL (x * longElt (k' + 1) k)
  obtain ⟨b1, hb1, b2, hb2, he⟩ := DoubleCoset.mem_doubleCoset.1 hσ
  have hb2' : longElt (k' + 1) k * b2 * longElt (k' + 1) k ∈ lowB k (k' + 1) := by
    refine mem_lowB.2 fun i j hij => ?_
    rw [Units.val_mul, Units.val_mul, mul_longElt_apply, longElt_mul_apply]
    exact (GroundTheory.Automorphic.mem_borel_iff b2).1 hb2 _ _ (Fin.rev_lt_rev.2 hij)
  have hd : ∀ i, (b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) i i ≠ 0 :=
    GroundTheory.Automorphic.borel_diag_ne_zero hb1
  let t : GL (Fin (k' + 1)) k := ⟨diagonal fun i => (b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) i i,
    diagonal fun i => ((b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) i i)⁻¹,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd i),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hd i)⟩
  have hu : b1 * t⁻¹ ∈ unipB k (Fin (k' + 1)) := by
    refine (mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [Units.val_mul]
      show ((b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) * (diagonal _ : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k)) i j = 0
      rw [mul_diagonal, (GroundTheory.Automorphic.mem_borel_iff b1).1 hb1 i j hji, zero_mul]
    · rw [Units.val_mul]
      show ((b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) * (diagonal _ : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k)) i i = 1
      rw [mul_diagonal, mul_inv_cancel₀ (hd i)]
  have hPw : GroundTheory.Automorphic.permGL k σ * longElt (k' + 1) k = GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) := by
    rw [longElt_eq_permGL, map_mul]
  have ht : (GroundTheory.Automorphic.permGL k (σ * Fin.revPerm))⁻¹ * t * GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) ∈
      lowB k (k' + 1) := by
    refine mem_lowB.2 fun r c hrc => ?_
    rw [permConj_apply]
    exact diagonal_apply_ne _ ((σ * Fin.revPerm).injective.ne (ne_of_lt hrc))
  have hx' : x = b1 * GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) * (longElt (k' + 1) k * b2 * longElt (k' + 1) k) := by
    calc x = x * longElt (k' + 1) k * longElt (k' + 1) k := by rw [mul_assoc, longElt_mul_self, mul_one]
    _ = b1 * GroundTheory.Automorphic.permGL k σ * b2 * longElt (k' + 1) k := by rw [he]
    _ = _ := by rw [← hPw]; simp only [mul_assoc, hww]
  have hx'' : x = (b1 * t⁻¹) * (GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) *
      (((GroundTheory.Automorphic.permGL k (σ * Fin.revPerm))⁻¹ * t * GroundTheory.Automorphic.permGL k (σ * Fin.revPerm)) *
        (longElt (k' + 1) k * b2 * longElt (k' + 1) k))) := by
    rw [hx']; group
  by_cases hπ : σ * Fin.revPerm = 1
  · refine ⟨b1 * t⁻¹, hu, _, mul_mem ht hb2', ?_⟩
    rw [hx'', hπ, map_one, one_mul]
  · exfalso
    apply hx
    have h0 := vanish_perm ψ hψ W h1 h2 _ hπ _ (mul_mem ht hb2')
    rw [hx'', h1 _ hu, h0, mul_zero]

end DiscreteGroups.sglob.DzFp
