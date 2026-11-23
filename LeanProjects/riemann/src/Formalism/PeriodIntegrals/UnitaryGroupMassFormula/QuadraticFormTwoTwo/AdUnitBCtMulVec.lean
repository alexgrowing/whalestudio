import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.InLieW

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2

variable {k r : ℕ}

theorem ad_herm_bvec (q : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec q) w = ∑ s, star (w s) * Hpk k r s q := by
  unfold herm bvec
  simp only [dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem ad_herm_sum (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ q, v q * herm (Hpk k r) (bvec q) w := by
  simp only [ad_herm_bvec]
  unfold herm
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem ad_herm_symm (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  first
    | rw [star_dotProduct]
    | rw [Matrix.star_dotProduct]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, GBasic.Hpk_herm]

theorem ad_unitB_mulVec {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    (v : Fin (2 * r + k + 1) → ℂ) :
    unitB (Hpk k r) Bs a b *ᵥ v = herm (Hpk k r) v (Bs b) • Bs a := by
  unfold unitB
  rw [ad_herm_sum v (Bs b)]
  funext p
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem ad_unitB_ct_mulVec {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    (v : Fin (2 * r + k + 1) → ℂ) :
    (unitB (Hpk k r) Bs a b)ᴴ *ᵥ (Hpk k r *ᵥ v) =
      herm (Hpk k r) v (Bs a) • fun p => star (herm (Hpk k r) (bvec p) (Bs b)) := by
  unfold unitB
  funext p
  show ∑ q, star (Bs a q * herm (Hpk k r) (bvec p) (Bs b)) * (Hpk k r *ᵥ v) q =
    herm (Hpk k r) v (Bs a) * star (herm (Hpk k r) (bvec p) (Bs b))
  rw [show herm (Hpk k r) v (Bs a) = ∑ q, star (Bs a q) * (Hpk k r *ᵥ v) q from rfl, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [star_mul']
  ring

theorem ad_hpart_kill {Z : Mx k r} {v : Fin (2 * r + k + 1) → ℂ} (h1 : Z *ᵥ v = 0)
    (h2 : Zᴴ *ᵥ (Hpk k r *ᵥ v) = 0) :
    hpart1 (Hpk k r) Z *ᵥ v = 0 ∧ hpart2 (Hpk k r) Z *ᵥ v = 0 := by
  have hs : ∀ (c : ℂ) (A : Mx k r) (x : Fin (2 * r + k + 1) → ℂ), (c • A) *ᵥ x = c • (A *ᵥ x) := by
    intro c A x
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]
  have e : ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]
  unfold hpart1 hpart2
  constructor
  · rw [hs, Matrix.sub_mulVec, h1, e, sub_zero, smul_zero]
  · rw [hs, Matrix.add_mulVec, h1, e, add_zero, smul_zero]

theorem ad_unitB_kill {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    {v : Fin (2 * r + k + 1) → ℂ} (ha : herm (Hpk k r) v (Bs a) = 0) (hb : herm (Hpk k r) v (Bs b) = 0) :
    hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 ∧ hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 := by
  apply ad_hpart_kill
  · rw [ad_unitB_mulVec, hb, zero_smul]
  · rw [ad_unitB_ct_mulVec, ha, zero_smul]

theorem ad_herm_g {g : Mx k r} (hg : gᴴ * Hpk k r * g = Hpk k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ x) (g *ᵥ y) = herm (Hpk k r) x y := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem ad_unitB_conj {g : Mx k r} (hg : gᴴ * Hpk k r * g = Hpk k r) (hgi : g * g⁻¹ = 1)
    {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m) :
    unitB (Hpk k r) (fun c => g *ᵥ Bs c) a b = g * unitB (Hpk k r) Bs a b * g⁻¹ := by
  have key : ∀ v, unitB (Hpk k r) (fun c => g *ᵥ Bs c) a b *ᵥ v =
      (g * unitB (Hpk k r) Bs a b * g⁻¹) *ᵥ v := by
    intro v
    rw [ad_unitB_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ad_unitB_mulVec, Matrix.mulVec_smul]
    congr 1
    conv_lhs => rw [show v = g *ᵥ (g⁻¹ *ᵥ v) by rw [Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]]
    exact ad_herm_g hg _ _
  ext p q
  have := congrFun (key (Pi.single q 1)) p
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem ad_hpart_conj {g : Mx k r} (hg : gᴴ * Hpk k r * g = Hpk k r) (hgi : g * g⁻¹ = 1) (Z : Mx k r) :
    hpart1 (Hpk k r) (g * Z * g⁻¹) = g * hpart1 (Hpk k r) Z * g⁻¹ ∧
      hpart2 (Hpk k r) (g * Z * g⁻¹) = g * hpart2 (Hpk k r) Z * g⁻¹ := by
  have hH : Hpk k r * Hpk k r = 1 := hpk_sq'
  have e1 : gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
    calc gᴴ * Hpk k r = gᴴ * Hpk k r * (g * g⁻¹) := by rw [hgi, Matrix.mul_one]
      _ = (gᴴ * Hpk k r * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  have e2 : Hpk k r * (g⁻¹)ᴴ = g * Hpk k r := by
    have h := congrArg Matrix.conjTranspose e1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_h] at h

    calc Hpk k r * (g⁻¹)ᴴ = Hpk k r * ((g⁻¹)ᴴ * Hpk k r) * Hpk k r := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = Hpk k r * (Hpk k r * g) * Hpk k r := by rw [h]
      _ = _ := by rw [← Matrix.mul_assoc, hH, Matrix.one_mul]
  have key : (Hpk k r)⁻¹ * (g * Z * g⁻¹)ᴴ * Hpk k r = g * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) * g⁻¹ := by
    rw [hpk_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc Hpk k r * ((g⁻¹)ᴴ * (Zᴴ * gᴴ)) * Hpk k r = (Hpk k r * (g⁻¹)ᴴ) * Zᴴ * (gᴴ * Hpk k r) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [e1, e2]; simp only [Matrix.mul_assoc]
  unfold hpart1 hpart2
  rw [key]
  constructor
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
