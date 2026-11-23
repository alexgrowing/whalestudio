import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Classical

namespace GlobalTheory.SchrodingerUniq

section Abstract

variable {G Y : Type} [AddCommGroup G] [AddCommGroup Y] (χ : Y → G → ℂ)

theorem chi_nsmul (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ) (hzero : ∀ ξ, χ 0 ξ = 1) (y : Y) (ξ : G) :
    ∀ m : ℕ, χ (m • y) ξ = χ y ξ ^ m
  | 0 => by rw [zero_nsmul, hzero, pow_zero]
  | m + 1 => by rw [succ_nsmul, hadd, chi_nsmul hadd hzero y ξ m, pow_succ]

theorem norm_avg_le_one (f : ℕ → ℂ) (hf : ∀ m, ‖f m‖ = 1) {M : ℕ} (hM : 0 < M) :
    ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, f m‖ ≤ 1 := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  calc (M : ℝ)⁻¹ * ‖∑ m ∈ Finset.range M, f m‖ ≤ (M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, ‖f m‖ := by
        gcongr; exact norm_sum_le _ _
    _ = 1 := by simp only [hf, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]; field_simp

theorem norm_avg_pow_le {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {M : ℕ} (hM : 0 < M) :
    ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, z ^ m‖ ≤ 2 / (M * ‖z - 1‖) := by
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : ‖z ^ M - 1‖ ≤ 2 := by
    calc ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  rw [geom_sum_eq hz1, norm_mul, norm_div, norm_inv, Complex.norm_natCast]
  calc (M : ℝ)⁻¹ * (‖z ^ M - 1‖ / ‖z - 1‖) ≤ (M : ℝ)⁻¹ * (2 / ‖z - 1‖) := by gcongr
    _ = 2 / (M * ‖z - 1‖) := by field_simp

variable (c : G → ℂ)

def Good (a : G → ℂ) : Prop := (∀ ξ, ‖a ξ‖ ≤ 1) ∧ a 0 = 1 ∧ ∀ y, ∑' ξ, c ξ * χ y ξ * a ξ = 0

variable {χ c}

theorem good_avg (hnorm : ∀ y ξ, ‖χ y ξ‖ = 1) (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ)
    (h0 : ∀ y, χ y 0 = 1) (hc : Summable fun ξ => ‖c ξ‖) {a : G → ℂ} (ha : Good χ c a) (y' : Y) {M : ℕ}
    (hM : 0 < M) : Good χ c (fun ξ => a ξ * ((M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') ξ)) := by
  refine ⟨fun ξ => ?_, ?_, fun y => ?_⟩
  · rw [norm_mul]
    calc ‖a ξ‖ * ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') ξ‖ ≤ 1 * 1 :=
          mul_le_mul (ha.1 ξ) (norm_avg_le_one _ (fun m => hnorm _ _) hM) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · simp only [ha.2.1, h0, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, one_mul]
    exact inv_mul_cancel₀ (by exact_mod_cast hM.ne')
  · have hs : ∀ m ∈ Finset.range M, Summable fun ξ => c ξ * χ y ξ * a ξ * χ (m • y') ξ := fun m _ =>
      Summable.of_norm_bounded hc fun ξ => by
        rw [norm_mul, norm_mul, norm_mul, hnorm, hnorm, mul_one, mul_one]
        exact mul_le_of_le_one_right (norm_nonneg _) (ha.1 ξ)
    calc ∑' ξ, c ξ * χ y ξ * (a ξ * ((M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') ξ))
        = ∑' ξ, (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, c ξ * χ y ξ * a ξ * χ (m • y') ξ := by
          congr 1; funext ξ
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
      _ = (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, ∑' ξ, c ξ * χ y ξ * a ξ * χ (m • y') ξ := by
          rw [tsum_mul_left, Summable.tsum_finsetSum hs]
      _ = 0 := by
          rw [Finset.sum_eq_zero fun m _ => ?_, mul_zero]
          rw [← ha.2.2 (y + m • y')]
          congr 1; funext ξ; rw [hadd]; ring

theorem exists_good_small (hnorm : ∀ y ξ, ‖χ y ξ‖ = 1) (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ)
    (hzero : ∀ ξ, χ 0 ξ = 1) (h0 : ∀ y, χ y 0 = 1) (hsep : ∀ ξ, ξ ≠ 0 → ∃ y, χ y ξ ≠ 1)
    (hc : Summable fun ξ => ‖c ξ‖) (h1 : Good χ c fun _ => 1) :
    ∀ (T : Finset G), (0 : G) ∉ T → ∀ ε > 0, ∃ a, Good χ c a ∧ ∀ ξ ∈ T, ‖a ξ‖ ≤ ε := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _ ε _; exact ⟨fun _ => 1, h1, by simp⟩
  | insert ξ T hξT ih =>
    intro h0T ε hε
    have hξ0 : ξ ≠ 0 := fun e => h0T (by rw [← e]; exact Finset.mem_insert_self ξ T)
    obtain ⟨a, ha, haT⟩ := ih (fun e => h0T (Finset.mem_insert_of_mem e)) ε hε
    obtain ⟨y', hy'⟩ := hsep ξ hξ0
    have hd : 0 < ‖χ y' ξ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hy')
    obtain ⟨M, hM⟩ := exists_nat_gt (2 / (ε * ‖χ y' ξ - 1‖))
    have hM0 : 0 < M := by
      have : (0 : ℝ) < M := lt_trans (by positivity) hM
      exact_mod_cast this
    refine ⟨_, good_avg hnorm hadd h0 hc ha y' hM0, fun η hη => ?_⟩
    rw [norm_mul]
    rcases Finset.mem_insert.1 hη with rfl | hη
    · simp_rw [chi_nsmul χ hadd hzero]
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
      calc ‖a η‖ * ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ y' η ^ m‖ ≤ 1 * (2 / (M * ‖χ y' η - 1‖)) :=
            mul_le_mul (ha.1 _) (norm_avg_pow_le (hnorm _ _) hy' hM0) (norm_nonneg _) zero_le_one
        _ ≤ ε := by
            rw [one_mul, div_le_iff₀ (by positivity)]
            rw [div_lt_iff₀ (by positivity)] at hM
            have : ε * (M * ‖χ y' η - 1‖) = M * (ε * ‖χ y' η - 1‖) := by ring
            linarith
    · calc ‖a η‖ * ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') η‖ ≤ ε * 1 :=
            mul_le_mul (haT η hη) (norm_avg_le_one _ (fun m => hnorm _ _) hM0) (norm_nonneg _) hε.le
        _ = ε := mul_one ε

theorem coeff_zero_eq_zero (hnorm : ∀ y ξ, ‖χ y ξ‖ = 1) (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ)
    (hzero : ∀ ξ, χ 0 ξ = 1) (h0 : ∀ y, χ y 0 = 1) (hsep : ∀ ξ, ξ ≠ 0 → ∃ y, χ y ξ ≠ 1)
    (hc : Summable fun ξ => ‖c ξ‖) (h : ∀ y, ∑' ξ, c ξ * χ y ξ = 0) : c 0 = 0 := by
  have h1 : Good χ c fun _ => 1 := ⟨fun _ => by simp, rfl, fun y => by simpa using h y⟩
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
  set S := ∑' ξ, ‖c ξ‖
  have hS : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.1
    ((tendsto_tsum_compl_atTop_zero fun ξ => ‖c ξ‖).eventually (gt_mem_nhds (half_pos hδ)))
  set s := insert (0 : G) s₀
  have htail := hs₀ s (Finset.subset_insert _ _)
  have hε : 0 < δ / (2 * (S + 1)) := by positivity
  obtain ⟨a, ha, haT⟩ := exists_good_small hnorm hadd hzero h0 hsep hc h1 (s.erase 0)
    (Finset.notMem_erase 0 s) _ hε
  have hsumm : Summable fun ξ => c ξ * a ξ := Summable.of_norm_bounded hc fun ξ => by
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (ha.1 ξ)
  have hsum : ∑' ξ, c ξ * a ξ = 0 := by simpa [hzero] using ha.2.2 0
  have hsplit := hsumm.sum_add_tsum_compl (s := s)
  rw [hsum, ← Finset.add_sum_erase s _ (Finset.mem_insert_self 0 s₀), ha.2.1, mul_one] at hsplit
  have hc0 : c 0 = -(∑ x ∈ s.erase 0, c x * a x + ∑' x : ↑((s : Set G)ᶜ), c x * a x) := by
    linear_combination hsplit
  have hA : ‖∑ x ∈ s.erase 0, c x * a x‖ ≤ δ / (2 * (S + 1)) * S := by
    calc ‖∑ x ∈ s.erase 0, c x * a x‖ ≤ ∑ x ∈ s.erase 0, ‖c x * a x‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ s.erase 0, δ / (2 * (S + 1)) * ‖c x‖ := Finset.sum_le_sum fun x hx => by
          rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (haT x hx) (norm_nonneg _)
      _ = δ / (2 * (S + 1)) * ∑ x ∈ s.erase 0, ‖c x‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ δ / (2 * (S + 1)) * S := by
          gcongr; exact hc.sum_le_tsum _ fun _ _ => norm_nonneg _
  have hB : ‖∑' x : ↑((s : Set G)ᶜ), c x * a x‖ ≤ ∑' x : {x // x ∉ s}, ‖c x‖ := by
    calc ‖∑' x : ↑((s : Set G)ᶜ), c x * a x‖ ≤ ∑' x : ↑((s : Set G)ᶜ), ‖c x * a x‖ :=
          norm_tsum_le_tsum_norm ((hsumm.subtype _).norm)
      _ ≤ ∑' x : ↑((s : Set G)ᶜ), ‖c x‖ := Summable.tsum_le_tsum
          (fun x => by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (ha.1 x))
          (hsumm.subtype _).norm (hc.subtype _)
      _ = ∑' x : {x // x ∉ s}, ‖c x‖ := rfl
  have hSS : δ / (2 * (S + 1)) * S ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  rw [hc0, norm_neg, zero_add]
  calc _ ≤ ‖∑ x ∈ s.erase 0, c x * a x‖ + ‖∑' x : ↑((s : Set G)ᶜ), c x * a x‖ := norm_add_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add (hA.trans hSS) (hB.trans htail.le)
    _ = δ := add_halves δ

end Abstract

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w : (κ → AF D.host.F) × (κ → AF D.host.F), GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ) =
        GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ')) → φ = φ' := by
  intro D ψ hψ κ _ φ hφ φ' hφ' h
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  obtain ⟨a₀, ha₀⟩ := hψ.1.2.2.2
  let ι : (κ → D.host.F) → (κ → AF D.host.F) := fun ξ i => algebraMap D.host.F (AF D.host.F) (ξ i)
  have hι0 : ι 0 = 0 := by funext i; simp [ι]
  funext x
  rw [← sub_eq_zero]
  have hΦ : (fun z => (φ - φ') (z + x)) ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    GlobalTheory.SchwartzTranslate.schA_translate D.host.F x (sub_mem hφ hφ')
  have hc : Summable fun ξ => ‖(φ - φ') (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F hΦ using 1
  have sφ : Summable fun ξ => ‖φ (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F (GlobalTheory.SchwartzTranslate.schA_translate D.host.F x hφ) using 1
  have sφ' : Summable fun ξ => ‖φ' (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F (GlobalTheory.SchwartzTranslate.schA_translate D.host.F x hφ') using 1
  have key := coeff_zero_eq_zero (χ := fun (y : κ → AF D.host.F) (ξ : κ → D.host.F) => ψ (ι ξ ⬝ᵥ y))
    (c := fun ξ => (φ - φ') (ι ξ + x)) (fun y ξ => hn _)
    (fun y y' ξ => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
    (fun ξ => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
    (fun y => by simp only [hι0, zero_dotProduct, AddChar.map_zero_eq_one])
    (fun ξ hξ => by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      have hi' : ξ i ≠ 0 := hi
      refine ⟨Pi.single i (algebraMap D.host.F (AF D.host.F) (ξ i)⁻¹ * a₀), ?_⟩
      show ψ (ι ξ ⬝ᵥ Pi.single i (algebraMap D.host.F (AF D.host.F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [dotProduct_single]
      show ψ (algebraMap D.host.F (AF D.host.F) (ξ i) * (algebraMap D.host.F (AF D.host.F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
      exact ha₀)
    hc (fun y => ?_)
  · simpa [hι0] using key
  · have h' := h (x, y)
    simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, AddChar.map_add_eq_mul] at h'
    set b := ψ (⅟(2 : AF D.host.F) * (x ⬝ᵥ y))
    have hb : b ≠ 0 := by
      intro e
      have h1 : ‖b‖ = 1 := hn _
      rw [e, norm_zero] at h1
      exact zero_ne_one h1
    have s1 : Summable fun ξ : κ → D.host.F => ψ (ι ξ ⬝ᵥ y) * b * φ (ι ξ + x) :=
      Summable.of_norm_bounded sφ fun ξ => by rw [norm_mul, norm_mul, hn, hn, one_mul, one_mul]
    have s2 : Summable fun ξ : κ → D.host.F => ψ (ι ξ ⬝ᵥ y) * b * φ' (ι ξ + x) :=
      Summable.of_norm_bounded sφ' fun ξ => by rw [norm_mul, norm_mul, hn, hn, one_mul, one_mul]
    have e : ∑' ξ : κ → D.host.F, (ψ (ι ξ ⬝ᵥ y) * b * φ (ι ξ + x) - ψ (ι ξ ⬝ᵥ y) * b * φ' (ι ξ + x)) = 0 := by
      rw [s1.tsum_sub s2, sub_eq_zero]; exact h'
    have e2 : ∑' ξ : κ → D.host.F, (φ - φ') (ι ξ + x) * ψ (ι ξ ⬝ᵥ y) =
        b⁻¹ * ∑' ξ : κ → D.host.F, (ψ (ι ξ ⬝ᵥ y) * b * φ (ι ξ + x) - ψ (ι ξ ⬝ᵥ y) * b * φ' (ι ξ + x)) := by
      rw [← tsum_mul_left]; congr 1; funext ξ; simp only [Pi.sub_apply]; field_simp
    rw [e2, e, mul_zero]

end GlobalTheory.SchrodingerUniq
