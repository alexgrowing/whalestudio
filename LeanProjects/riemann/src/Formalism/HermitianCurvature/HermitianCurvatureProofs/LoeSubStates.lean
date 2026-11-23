import Formalism.HermitianCurvature.HermitianCurvatureProofs.LoeZeroOfPsd

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Finset
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

open Classical

section abstract

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

theorem psd_wsum {ι : Type} [Fintype ι] (Y : Finset α) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (V : ι → α → H) :
    TB.PSDOn Y (fun P Q => ∑ i, (d i : ℂ) * gramH (V i) P Q) := by
  have h := loe_sum (Finset.univ : Finset ι) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun i P Q => (d i : ℂ) * gramH (V i) P Q) fun i _ => by
      have := loe_smul (d i) (hd i) (loe_zero_of_psd (psd_gramH Y (V i)))
      refine loe_congr (fun x _ y _ => by ring) (fun x _ y _ => rfl) this
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

theorem loe_sub_states {ι ι' : Type} [Fintype ι] [Fintype ι'] (Y : Finset α) (g : ι → ι') (hg : Function.Injective g)
    (K : ι' → α → α → ℂ) (hK : ∀ j, TB.PSDOn Y (K j)) :
    Loe Y (fun x y => ∑ i, K (g i) x y) (fun x y => ∑ j, K j x y) := by
  have e : ∀ x y, ∑ j, K j x y = ∑ j ∈ Finset.univ.image g, K j x y +
      ∑ j ∈ Finset.univ \ Finset.univ.image g, K j x y := by
    intro x y
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have e2 : ∀ x y, ∑ j ∈ Finset.univ.image g, K j x y = ∑ i, K (g i) x y := by
    intro x y
    rw [Finset.sum_image fun i _ i' _ h => hg h]
  have h1 := loe_sum (Finset.univ \ Finset.univ.image g) (Y := Y) (A := fun _ _ _ => (0 : ℂ)) (B := K)
    fun j _ => loe_zero_of_psd (hK j)
  have h2 := loe_add (loe_refl Y (fun x y => ∑ i, K (g i) x y)) h1
  refine loe_congr (fun x _ y _ => by simp) (fun x _ y _ => ?_) h2
  rw [e, e2]

theorem top_kernel {Ea R N : Type} {Ew : N → Type} [Fintype Ea] [∀ n, Fintype (Ew n)] [Fintype R] [Fintype N]
    (Y : Finset α) (g : ∀ n, Ea → Ew n) (hg : ∀ n, Function.Injective (g n)) (Va : Ea → R → α → H)
    (Vn : ∀ n, Ew n → R → α → H) (da : Ea → R → ℝ) (dn : ∀ n, Ew n → R → ℝ) (hda : ∀ e ρ, 0 ≤ da e ρ)
    (hdn : ∀ n e ρ, 0 ≤ dn n e ρ)
    (lam : N → ℝ) (Pn : N → ℝ) (hPn : ∀ n, 0 < Pn n) (c : ℂ) (C0 : ℝ) (K : ℕ) (hC0 : 0 ≤ C0)
    (hdeg : ∀ P ∈ Y, ∀ e ρ, Va e ρ P = c • ∑ n, (lam n : ℂ) • Vn n (g n e) ρ P)
    (hwt : ∀ n e ρ, da e ρ * Pn n ≤ C0 ^ K * dn n (g n e) ρ) :
    Loe Y (fun P Q => ∑ e, ∑ ρ, (da e ρ : ℂ) * gramH (Va e ρ) P Q)
      (fun P Q => ((‖c‖ ^ 2 * (∑ n, |lam n|) * C0 ^ K : ℝ) : ℂ) *
        ∑ n, ((|lam n| / Pn n : ℝ) : ℂ) * ∑ e', ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q) := by
  set Λ : ℝ := ∑ n, |lam n| with hΛ

  have s1 : ∀ e ρ, Loe Y (fun P Q => (da e ρ : ℂ) * gramH (Va e ρ) P Q)
      (fun P Q => (da e ρ : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) * (((∑ n, ‖(lam n : ℂ)‖ : ℝ) : ℂ) *
        ∑ n, ((‖(lam n : ℂ)‖ : ℝ) : ℂ) * gramH (Vn n (g n e) ρ) P Q)) := by
    intro e ρ
    have hc := loe_convex Y (fun n => (lam n : ℂ)) (fun n P => Vn n (g n e) ρ P)
    have hc2 := loe_smul (da e ρ * ‖c‖ ^ 2) (mul_nonneg (hda e ρ) (sq_nonneg _)) hc
    refine loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => by push_cast; ring) hc2
    have : gramH (Va e ρ) P Q = gramH (fun P => c • ∑ n, (lam n : ℂ) • Vn n (g n e) ρ P) P Q := by
      unfold gramH; rw [hdeg P hP e ρ, hdeg Q hQ e ρ]
    rw [this, gramH_smul]
    push_cast; ring
  have hnorm : ∀ n, ‖(lam n : ℂ)‖ = |lam n| := fun n => by rw [Complex.norm_real, Real.norm_eq_abs]
  simp only [hnorm] at s1

  have s2 : ∀ e ρ n, Loe Y (fun P Q => (da e ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)
      (fun P Q => ((C0 ^ K / Pn n : ℝ) : ℂ) * ((dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)) := by
    intro e ρ n
    have h := loe_scale (psd_gramH Y (Vn n (g n e) ρ)) (r := da e ρ) (r' := C0 ^ K / Pn n * dn n (g n e) ρ) (by
      have := hwt n e ρ
      rw [sub_nonneg, div_mul_eq_mul_div, le_div_iff₀ (hPn n)]
      linarith)
    refine loe_congr (fun _ _ _ _ => rfl) (fun P _ Q _ => by push_cast; ring) h

  have s3 : ∀ n, Loe Y (fun P Q => ∑ e, ∑ ρ, (dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)
      (fun P Q => ∑ e', ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q) :=
    fun n => loe_sub_states Y (g n) (hg n) (fun e' P Q => ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q)
      fun e' => psd_wsum Y (fun ρ => dn n e' ρ) (fun ρ => hdn n e' ρ) (fun ρ => Vn n e' ρ)

  have c1 := loe_sum (Finset.univ : Finset Ea) fun e _ => loe_sum (Finset.univ : Finset R) fun ρ _ => s1 e ρ
  refine loe_trans c1 ?_

  have c2 : ∀ e ρ, Loe Y (fun P Q => (da e ρ : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) * ((Λ : ℂ) *
        ∑ n, ((|lam n| : ℝ) : ℂ) * gramH (Vn n (g n e) ρ) P Q))
      (fun P Q => ((‖c‖ ^ 2 * Λ : ℝ) : ℂ) * ∑ n, ((|lam n| : ℝ) : ℂ) *
        (((C0 ^ K / Pn n : ℝ) : ℂ) * ((dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q))) := by
    intro e ρ
    have h := loe_smul (‖c‖ ^ 2 * Λ) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _))
      (loe_sum (Finset.univ : Finset N) fun n _ => loe_smul (|lam n|) (abs_nonneg _) (s2 e ρ n))
    refine loe_congr (fun P _ Q _ => ?_) (fun _ _ _ _ => rfl) h
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast; ring
  have c3 := loe_sum (Finset.univ : Finset Ea) fun e _ => loe_sum (Finset.univ : Finset R) fun ρ _ => c2 e ρ
  refine loe_trans (loe_congr (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) c3) ?_
  have c4 := loe_smul (‖c‖ ^ 2 * Λ) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _))
    (loe_sum (Finset.univ : Finset N) fun n _ => loe_smul (|lam n| * (C0 ^ K / Pn n))
      (mul_nonneg (abs_nonneg _) (div_nonneg (pow_nonneg hC0 _) (hPn n).le)) (s3 n))
  refine loe_congr (fun P _ Q _ => ?_) (fun P _ Q _ => ?_) c4
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun ρ _ => ?_
    push_cast; ring
  · simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun ρ _ => ?_
    push_cast; ring

end abstract

end

end Formalism.FourierDecayAlt.P.PBL
