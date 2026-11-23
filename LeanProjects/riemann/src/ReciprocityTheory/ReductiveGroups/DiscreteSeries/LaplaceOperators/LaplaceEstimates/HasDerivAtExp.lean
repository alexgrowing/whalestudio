import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement

open Matrix Filter Topology

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

namespace ExponentialSlopeDerivatives

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

theorem hasDerivAt_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ))
  have h2 := h.scomp (x := (0:ℝ)) Complex.ofRealCLM.hasDerivAt
  exact h2.congr_deriv (by simp)

end Linfty

theorem slope_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 X) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedSpace (R := ℝ) (m := Fin n) (n := Fin n) (α := ℂ)
  exact (hasDerivAt_exp X).tendsto_slope

theorem rdv_of_linear {n : ℕ} (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g X Y : Matrix (Fin n) (Fin n) ℂ)
    (Lf : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hf : ∀ t : ℝ, f (g * NormedSpace.exp ((t : ℂ) • X)) = Lf (NormedSpace.exp ((t : ℂ) • Y))) :
    S7.RdV X f g = Lf Y := by
  have hc : Continuous Lf := LinearMap.continuous_of_finiteDimensional Lf
  have hT := (hc.tendsto Y).comp (slope_exp Y)
  have hD : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (Lf Y) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine hT.congr (fun t => ?_)
    simp only [Function.comp_apply, slope_def_module, hf]
    rw [LinearMap.map_smul_of_tower, map_sub]
  exact hD.deriv

end ExponentialSlopeDerivatives

end ReciprocityTheory.ChartRestriction.DS.Lap

namespace ReciprocityTheory.ChartRestriction.DS.Lap
namespace ExponentialSlopeDerivatives
open Formalism.QuantumDeterminants

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

theorem sg_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (sg k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold sg; split_ifs <;> rfl

theorem sg_sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  apply Fin.ext; rw [sg_val, sg_val]; split_ifs <;> omega

theorem sg_mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : (sg k r i).val = r + k ↔ i.val = r + k := by
  rw [sg_val]; split_ifs <;> omega

theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sg k r i then (if i.val = r + k then -1 else 1) else 0 := by
  have key : j = sg k r i ↔ j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := by
    rw [← sg_val, Fin.ext_iff]
  unfold Hpk
  simp only [key, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_self (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sg_sg, sg_mid]
  by_cases hij : i = j
  · subst hij; split_ifs <;> simp_all
  · have : ¬ j = i := fun h => hij h.symm
    simp [hij, this]

theorem inv_of_UH {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) (hg : gᴴ * H * g = H) :
    g⁻¹ = H * gᴴ * H := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, hH]

theorem inv_mul_of_UH {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) (hg : gᴴ * H * g = H) :
    g⁻¹ * g = 1 := by
  rw [inv_of_UH hH hg, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, hH]

theorem herm_UH {n : ℕ} {H s : Matrix (Fin n) (Fin n) ℂ} (hs : sᴴ * H * s = H) (a b : Fin n → ℂ) :
    star (s *ᵥ a) ⬝ᵥ (H *ᵥ (s *ᵥ b)) = star a ⬝ᵥ (H *ᵥ b) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hs]

end ExponentialSlopeDerivatives
end ReciprocityTheory.ChartRestriction.DS.Lap

namespace ReciprocityTheory.ChartRestriction.DS.Lap
namespace ExponentialSlopeDerivatives
open Formalism.QuantumDeterminants

theorem s_fix (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    ∀ s ∈ Sset k r z, s ∈ UH (Hpk k r) ∧ s *ᵥ xOne k r z = xOne k r z := by
  rintro s ⟨h, ⟨hU, hfix, hz⟩, m, ⟨mU, mcol, mmid⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · show (h * m)ᴴ * Hpk k r * (h * m) = Hpk k r
    have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
    have mU' : mᴴ * Hpk k r * m = Hpk k r := mU
    rw [Matrix.conjTranspose_mul]
    calc mᴴ * hᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hU', mU']
  · rw [← Matrix.mulVec_mulVec]
    unfold xOne
    split_ifs with hr
    · have hm : m = 1 := by
        ext i j
        rw [mmid i j (by omega) (by omega) (by omega), Matrix.one_apply]
      rw [hm, Matrix.one_mulVec, hz]
    · have hm : m *ᵥ Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ) =
          Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ) := by
        funext i
        rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
        exact mcol ⟨0, by omega⟩ i (Nat.zero_le _)
      rw [hm]
      exact (hfix ⟨0, by omega⟩).1

theorem dot_bound {n : ℕ} (a b : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖a ⬝ᵥ (M *ᵥ b)‖ ≤ ((∑ i, ‖a i‖) * (∑ j, ‖b j‖)) * ∑ i, ∑ j, ‖M i j‖ := by
  have h1 : a ⬝ᵥ (M *ᵥ b) = ∑ i, ∑ j, a i * M i j * b j := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul]
  have ha : ‖a i‖ ≤ ∑ i, ‖a i‖ :=
    Finset.single_le_sum (f := fun i => ‖a i‖) (fun i _ => norm_nonneg (a i)) (Finset.mem_univ i)
  have hb : ‖b j‖ ≤ ∑ j, ‖b j‖ :=
    Finset.single_le_sum (f := fun j => ‖b j‖) (fun j _ => norm_nonneg (b j)) (Finset.mem_univ j)
  calc ‖a i‖ * ‖M i j‖ * ‖b j‖ ≤ (∑ i, ‖a i‖) * ‖M i j‖ * (∑ j, ‖b j‖) := by gcongr
    _ = _ := by ring

end ExponentialSlopeDerivatives

open ExponentialSlopeDerivatives Formalism.QuantumDeterminants

theorem mult : MultStatement := by
  intro k r z _
  have hH := hpk_mul_self k r
  refine ⟨?_, ?_, ?_⟩
  · intro y β s hs g hg
    obtain ⟨hsU, hsx⟩ := s_fix k r z s hs
    have hsU' : sᴴ * Hpk k r * s = Hpk k r := hsU
    refine ⟨?_, ?_⟩
    · show star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((s * g) *ᵥ y)) =
        star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ y))
      rw [← Matrix.mulVec_mulVec]
      have := herm_UH hsU' (xOne k r z) (g *ᵥ y)
      rwa [hsx] at this
    · show β ⬝ᵥ ((s * g)⁻¹ *ᵥ xOne k r z) = β ⬝ᵥ (g⁻¹ *ᵥ xOne k r z)
      have hinv : s⁻¹ *ᵥ xOne k r z = xOne k r z := by
        conv_lhs => rw [← hsx]
        rw [Matrix.mulVec_mulVec, inv_mul_of_UH hH hsU', Matrix.one_mulVec]
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
  · intro y β X g _
    refine ⟨?_, ?_⟩
    · let Lf : Mat k r →ₗ[ℂ] ℂ :=
        { toFun := fun M => star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((g * M) *ᵥ y))
          map_add' := by
            intro A B
            simp [Matrix.mul_add, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
          map_smul' := by
            intro c A
            simp [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }
      rw [rdv_of_linear (cMul k r z y) g X X Lf (fun t => rfl)]
      show star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((g * X) *ᵥ y)) =
        star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ (X *ᵥ y)))
      rw [Matrix.mulVec_mulVec y g X]
    · let Lf : Mat k r →ₗ[ℂ] ℂ :=
        { toFun := fun M => β ⬝ᵥ (M *ᵥ (g⁻¹ *ᵥ xOne k r z))
          map_add' := by
            intro A B
            simp only [Matrix.add_mulVec, dotProduct_add]
          map_smul' := by
            intro c A
            simp [Matrix.smul_mulVec, dotProduct_smul] }
      have hf : ∀ t : ℝ, cMulD k r z β (g * NormedSpace.exp ((t : ℂ) • X)) =
          Lf (NormedSpace.exp ((t : ℂ) • -X)) := by
        intro t
        show β ⬝ᵥ ((g * NormedSpace.exp ((t : ℂ) • X))⁻¹ *ᵥ xOne k r z) =
          β ⬝ᵥ (NormedSpace.exp ((t : ℂ) • -X) *ᵥ (g⁻¹ *ᵥ xOne k r z))
        rw [Matrix.mul_inv_rev, smul_neg, Matrix.exp_neg, ← Matrix.mulVec_mulVec]
      rw [rdv_of_linear (cMulD k r z β) g X (-X) Lf hf]
      show β ⬝ᵥ ((-X) *ᵥ (g⁻¹ *ᵥ xOne k r z)) = -((β ᵥ* X) ⬝ᵥ (g⁻¹ *ᵥ xOne k r z))
      rw [Matrix.neg_mulVec, dotProduct_neg, Matrix.dotProduct_mulVec]
  · intro y β
    set x1 := xOne k r z
    set C1 : ℝ := (∑ i, ‖(star x1 ᵥ* Hpk k r) i‖) * (∑ j, ‖y j‖)
    set C2 : ℝ := (∑ i, ‖(β ᵥ* Hpk k r) i‖) * (∑ j, ‖(Hpk k r *ᵥ x1) j‖)
    refine ⟨max C1 C2, fun g hg => ?_⟩
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    have hS : 0 ≤ ∑ i, ∑ j, ‖g i j‖ :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
    refine ⟨?_, ?_⟩
    · have e : cMul k r z y g = (star x1 ᵥ* Hpk k r) ⬝ᵥ (g *ᵥ y) := by
        show star x1 ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ y)) = _
        rw [Matrix.dotProduct_mulVec]
      rw [e]
      exact (dot_bound _ _ _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hS)
    · have e : cMulD k r z β g = (β ᵥ* Hpk k r) ⬝ᵥ (gᴴ *ᵥ (Hpk k r *ᵥ x1)) := by
        show β ⬝ᵥ (g⁻¹ *ᵥ x1) = _
        rw [inv_of_UH hH hg', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.dotProduct_mulVec]
      have hT : ∑ i, ∑ j, ‖gᴴ i j‖ = ∑ i, ∑ j, ‖g i j‖ := by
        simp only [Matrix.conjTranspose_apply, norm_star]
        exact Finset.sum_comm
      rw [e]
      refine (dot_bound _ _ _).trans ?_
      rw [hT]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hS

end ReciprocityTheory.ChartRestriction.DS.Lap
