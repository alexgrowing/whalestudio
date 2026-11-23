import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame.DualFrame

theorem mdiff_det {n : ℕ} {M : ℍ → Matrix (Fin n) (Fin n) ℂ} (hM : ∀ a b, MDiff fun τ => M τ a b) :
    MDiff fun τ => (M τ).det := by
  have : (fun τ => (M τ).det) =
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∏ a, (fun τ => M τ (σ a) a) := by
    ext τ; simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact MDifferentiable.sum fun σ _ => (MDifferentiable.prod fun a _ => hM _ _).const_smul _

variable {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ)

def dualEntry (i j : Fin r) : ℍ → ℂ := fun τ => ModularForm.discriminant τ * (evM s w F τ)⁻¹ j i

variable {s w F}

theorem evM_smul {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ}
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (τ : ℍ) (i k : Fin r) :
    evM s w F (y • τ) i k = c i * evM s w F τ (π i) k * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  simp only [evM, Matrix.of_apply]
  calc (F k ∣[w k] s i) (y • τ)
      = (F k ∣[w k] s i) (y • τ) * denom (y : GL (Fin 2) ℝ) τ ^ (-w k) * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
        rw [mul_assoc, ← zpow_add₀ hJ]; simp
    _ = c i * (F k ∣[w k] s (π i)) τ * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
        rw [← slash_mul_apply, hc]; simp [smul_eq_mul]

theorem inv_evM_smul {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ} (hcc : ∀ i, c i * c i = 1)
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (τ : ℍ) (hA : (evM s w F τ).det ≠ 0)
    (i j : Fin r) :
    (evM s w F (y • τ))⁻¹ j i = denom (y : GL (Fin 2) ℝ) τ ^ (-w j) * c i * (evM s w F τ)⁻¹ j (π i) := by
  set J := denom (y : GL (Fin 2) ℝ) τ with hJdef
  have hJ : J ≠ 0 := denom_ne_zero _ _
  have key : (Matrix.of fun j i => J ^ (-w j) * c i * (evM s w F τ)⁻¹ j (π i)) * evM s w F (y • τ) = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, evM_smul hc, ← hJdef]
    have h1 : ∀ l, J ^ (-w j) * c l * (evM s w F τ)⁻¹ j (π l) * (c l * evM s w F τ (π l) k * J ^ w k)
        = (J ^ (-w j) * J ^ w k) * ((evM s w F τ)⁻¹ j (π l) * evM s w F τ (π l) k) := by
      intro l
      linear_combination (J ^ (-w j) * (evM s w F τ)⁻¹ j (π l) * evM s w F τ (π l) k * J ^ w k) * hcc l
    rw [Finset.sum_congr rfl fun l _ => h1 l, ← Finset.mul_sum, Equiv.sum_comp π (fun l => (evM s w F τ)⁻¹ j l * evM s w F τ l k), ← Matrix.mul_apply,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)]
    rcases eq_or_ne j k with rfl | hjk
    · rw [← zpow_add₀ hJ]; simp
    · simp [Matrix.one_apply_ne hjk]
  rw [Matrix.inv_eq_left_inv key]; rfl

theorem discriminant_smul (y : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (y • τ) = ModularForm.discriminant τ * denom (y : GL (Fin 2) ℝ) τ ^ (12 : ℤ) := by
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have h := congrFun (SlashInvariantForm.slash_action_generators_SL2Z ModularForm.discriminant_S_invariant
    ModularForm.discriminant_T_invariant y) τ
  rw [ModularForm.SL_slash_apply] at h
  rw [← h, mul_assoc, ← zpow_add₀ hJ]; simp

theorem dualEntry_slash {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ} (hcc : ∀ i, c i * c i = 1)
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    (i j : Fin r) : dualEntry s w F i j ∣[12 - w j] y = c i • dualEntry s w F (π i) j := by
  ext τ
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [ModularForm.SL_slash_apply]
  simp only [dualEntry, Pi.smul_apply, smul_eq_mul, discriminant_smul, inv_evM_smul hcc hc τ (hA τ)]
  have hJJ : denom (y : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * denom (y : GL (Fin 2) ℝ) τ ^ (-w j) *
      denom (y : GL (Fin 2) ℝ) τ ^ (-(12 - w j)) = 1 := by
    rw [← zpow_add₀ hJ, ← zpow_add₀ hJ, show (12 : ℤ) + -w j + -(12 - w j) = 0 by ring, zpow_zero]
  linear_combination (c i * ModularForm.discriminant τ * (evM s w F τ)⁻¹ j (π i)) * hJJ

theorem dualEntry_slash_of_eq {Γ : Subgroup SL(2, ℤ)} (hΓ : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    {y γ : SL(2, ℤ)} (hγ : γ ∈ Γ) {i i' : Fin r} (hy : s i * y = γ * s i') (j : Fin r) :
    dualEntry s w F i j ∣[12 - w j] y = dualEntry s w F i' j := by
  classical
  obtain ⟨π, hπ⟩ := hs.exists_perm y
  choose g hg hdec using hπ
  let c : Fin r → ℂ := fun l => if s l * y = g l * s (π l) then 1 else -1
  have hcc : ∀ l, c l * c l = 1 := by
    intro l; simp only [c]; split_ifs <;> norm_num
  have hc : ∀ l j, F j ∣[w j] (s l * y) = c l • F j ∣[w j] s (π l) := by
    intro l j
    by_cases hp : s l * y = g l * s (π l)
    · simp only [c, if_pos hp]
      rw [hp, (hF j).2.slash_mul (hg l), one_smul]
    · simp only [c, if_neg hp]
      rw [(hdec l).resolve_left hp, slash_neg_of_odd (hF j).1, (hF j).2.slash_mul (hg l), neg_one_smul]
  have hπi : π i = i' := by
    apply hs.2 (π i) i' ((g i)⁻¹ * γ) (Γ.mul_mem (Γ.inv_mem (hg i)) hγ)
    rcases hdec i with h | h
    · left; rw [mul_assoc, ← hy, h, inv_mul_cancel_left]
    · right; rw [mul_assoc, ← hy, h, mul_neg, neg_neg, inv_mul_cancel_left]
  have hp : s i * y = g i * s (π i) := by
    by_contra hp
    have h := (hdec i).resolve_left hp
    rw [hy, hπi, ← neg_mul] at h
    have h2 : γ = -g i := mul_right_cancel h
    apply hΓ
    have h3 : (-1 : SL(2, ℤ)) = γ * (g i)⁻¹ := by rw [h2, neg_mul, mul_inv_cancel]
    rw [h3]
    exact Γ.mul_mem hγ (Γ.inv_mem (hg i))
  rw [dualEntry_slash hcc hc hA, hπi]
  simp only [c, if_pos hp, one_smul]

theorem mdiff_dualEntry (hF : ∀ j, MDiff (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0) (i j : Fin r) :
    MDiff (dualEntry s w F i j) := by
  have e : dualEntry s w F i j = ModularForm.discriminant * ((fun τ => (evM s w F τ).det)⁻¹ *
      fun τ => ((evM s w F τ).updateRow i (Pi.single j 1)).det) := by
    ext τ
    simp [dualEntry, Matrix.inv_def, Matrix.adjugate_apply, Ring.inverse_eq_inv']
  rw [e]
  refine CuspForm.discriminant.holo'.mul (((mdiff_det_evM s w hF).inv hA).mul (mdiff_det fun a b => ?_))
  by_cases h : a = i
  · simp only [Matrix.updateRow_apply, if_pos h]
    exact mdifferentiable_const
  · simp only [Matrix.updateRow_apply, if_neg h]
    exact mdiff_slash (hF b) _ _

theorem exists_dual_cuspForms (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hΓ : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    (hT : Tendsto (fun τ => ModularForm.discriminant τ • (evM s w F τ)⁻¹) atImInfty (𝓝 0)) :
    ∃ G : Fin r → ℍ → ℂ, (∀ j, IsCF Γ (12 - w j) (G j)) ∧
      ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  let G : Fin r → ℍ → ℂ := fun j => dualEntry s w F j j ∣[12 - w j] (s j)⁻¹
  have hodd : ∀ j, Odd (12 - w j) := fun j => by
    obtain ⟨k, hk⟩ := (hF j).1
    exact ⟨5 - k, by omega⟩
  have hpos : ∀ j i, ∀ γ ∈ Γ, G j ∣[12 - w j] (γ * s i) = dualEntry s w F i j := by
    intro j i γ hγ
    simp only [G]
    rw [← SlashAction.slash_mul]
    exact dualEntry_slash_of_eq hΓ hs hF hA hγ (mul_inv_cancel_left _ _) j
  have hzero : ∀ i j, IsZeroAtImInfty (dualEntry s w F i j) := fun i j =>
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hT j) i
  refine ⟨G, fun j => ⟨fun γ hγ => ?_, mdiff_slash (mdiff_dualEntry (fun j => (hF j).2.2.1) hA j j) _ _,
    fun x => ?_⟩, fun τ => ?_⟩
  · obtain ⟨i, g, hg, h | h⟩ := hs.1 1
    · calc G j ∣[12 - w j] γ = G j ∣[12 - w j] (γ * g * s i) := by rw [mul_assoc, ← h, mul_one]
        _ = G j ∣[12 - w j] (g * s i) := by rw [hpos j i _ (Γ.mul_mem hγ hg), hpos j i g hg]
        _ = G j := by rw [← h, SlashAction.slash_one]
    · calc G j ∣[12 - w j] γ = G j ∣[12 - w j] (-(γ * g * s i)) := by
            rw [mul_assoc, ← mul_neg, ← h, mul_one]
        _ = G j ∣[12 - w j] (-(g * s i)) := by
            rw [slash_neg_of_odd (hodd j), slash_neg_of_odd (hodd j), hpos j i _ (Γ.mul_mem hγ hg),
              hpos j i g hg]
        _ = G j := by rw [← h, SlashAction.slash_one]
  · obtain ⟨i, g, hg, rfl | rfl⟩ := hs.1 x
    · rw [hpos j i g hg]; exact hzero i j
    · rw [slash_neg_of_odd (hodd j), hpos j i g hg]; exact (hzero i j).neg
  · have e : evM s (fun j => 12 - w j) G τ = (ModularForm.discriminant τ • (evM s w F τ)⁻¹).transpose := by
      ext i j
      have h := hpos j i 1 Γ.one_mem
      rw [one_mul] at h
      change (G j ∣[12 - w j] s i) τ = _
      rw [h]; rfl
    rw [e, Matrix.det_transpose, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ)) (inv_ne_zero (hA τ))

end GlobalTheory.OddFrame.DualFrame
