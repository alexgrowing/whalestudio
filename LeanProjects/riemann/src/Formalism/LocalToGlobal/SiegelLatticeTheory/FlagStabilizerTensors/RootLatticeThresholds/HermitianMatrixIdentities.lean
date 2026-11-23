import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp

noncomputable section

open Matrix Formalism.QuantumDeterminants

namespace Formalism.L2.SG.HermitianMatrixIdentities

variable {k r : ℕ}

theorem hpk_isUnit : IsUnit (Hpk k r).det := by
  exact Formalism.FourierDecayAlt.P.B2x5.isUnit_det_Hpk k r

theorem star_dot_conjT' {n m : Type*} [Fintype n] [Fintype m] (Q : Matrix n m ℂ) (x : m → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (Qᴴ *ᵥ y) = star (Q *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem herm_sum_left (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ) :
    herm H (∑ i ∈ s, c i • v i) w = ∑ i ∈ s, c i * herm H (v i) w := by
  classical
  unfold herm
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.mulVec_add, dotProduct_add, ih,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_sum_right (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (v : Fin (2 * r + k + 1) → ℂ) (w : ι → Fin (2 * r + k + 1) → ℂ) :
    herm H v (∑ i ∈ s, c i • w i) = ∑ i ∈ s, star (c i) * herm H v (w i) := by
  classical
  unfold herm
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, star_add, add_dotProduct, ih, star_smul,
    smul_dotProduct, smul_eq_mul]

private lemma isUnit_det_of_mem_UH_Hpk' {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  have hH := hpk_isUnit (k := k) (r := r)
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  have h3 : gᴴ.det * g.det * (Hpk k r).det = 1 * (Hpk k r).det := by linear_combination h2
  have h4 := mul_right_cancel₀ hH.ne_zero h3
  exact isUnit_iff_exists.mpr ⟨gᴴ.det, by rw [mul_comm]; exact h4, h4⟩

theorem herm_UH {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hρ : ρ ∈ UH (Hpk k r))
    (x y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) (ρ *ᵥ x) y = herm (Hpk k r) x (ρ⁻¹ *ᵥ y) := by
  have hρ' : ρᴴ * Hpk k r * ρ = Hpk k r := hρ
  have hdet := isUnit_det_of_mem_UH_Hpk' hρ
  have hinv : (ρ⁻¹)ᴴ * ρᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one]
  have hkey : (ρ⁻¹)ᴴ * Hpk k r = Hpk k r * ρ := by
    calc (ρ⁻¹)ᴴ * Hpk k r = (ρ⁻¹)ᴴ * (ρᴴ * Hpk k r * ρ) := by rw [hρ']
      _ = ((ρ⁻¹)ᴴ * ρᴴ) * Hpk k r * ρ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * ρ := by rw [hinv, Matrix.one_mul]
  unfold herm
  rw [← star_dot_conjT' (ρ⁻¹) y (Hpk k r *ᵥ x)]
  simp only [Matrix.mulVec_mulVec, hkey]

private lemma mulVec_fvec_eq_sum_uMap_smul_of_mem_Nset {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.FourierDecayAlt.C2.StdZ k r z)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) (b : Fin (r + 1)) :
    m *ᵥ fvec k r z b = ∑ c, Formalism.FourierDecayAlt.C2.uMap k r z m c b • fvec k r z c := by
  have hF := Formalism.QuantumDeterminants.N_F hz.1 hm
  rw [Formalism.FourierDecayAlt.P.C2x5.uMap_eq hz m _ (Formalism.FourierDecayAlt.P.C2x5.colEq hF)]
  exact Formalism.FourierDecayAlt.P.C2x5.colEq hF b

theorem zhat_uMap {z z' : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.FourierDecayAlt.C2.StdZ k r z) (hz' : Formalism.FourierDecayAlt.C2.StdZ k r z')
    {δ ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hδ : δ ∈ UH (Hpk k r)) (hρ : ρ ∈ Nset k r)
    (hρ' : δ⁻¹ * ρ * δ ∈ Nset k r) :
    Zhat k r z z' δ * Formalism.FourierDecayAlt.C2.uMap k r z' (δ⁻¹ * ρ * δ) =
      (Formalism.FourierDecayAlt.C2.uMap k r z ρ⁻¹)ᴴ * Zhat k r z z' δ := by
  have hδd := isUnit_det_of_mem_UH_Hpk' hδ
  have hρU : ρ ∈ UH (Hpk k r) := hρ.1
  have hρi : ρ⁻¹ ∈ Nset k r := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hρ
  have hδs : δ * (δ⁻¹ * ρ * δ) = ρ * δ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hδd, Matrix.one_mul]
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]

  have e1 : ∑ c, Zhat k r z z' δ a c * Formalism.FourierDecayAlt.C2.uMap k r z' (δ⁻¹ * ρ * δ) c b =
      herm (Hpk k r) (δ *ᵥ ((δ⁻¹ * ρ * δ) *ᵥ fvec k r z' b)) (fvec k r z a) := by
    rw [mulVec_fvec_eq_sum_uMap_smul_of_mem_Nset hz' hρ' b, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rw [herm_sum_left]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Zhat]
    ring
  have e2 : ∑ c, (Formalism.FourierDecayAlt.C2.uMap k r z ρ⁻¹)ᴴ a c * Zhat k r z z' δ c b =
      herm (Hpk k r) (δ *ᵥ fvec k r z' b) (ρ⁻¹ *ᵥ fvec k r z a) := by
    rw [mulVec_fvec_eq_sum_uMap_smul_of_mem_Nset hz hρi a, herm_sum_right]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Zhat, Matrix.conjTranspose_apply]
  rw [e1, e2, Matrix.mulVec_mulVec, hδs, ← Matrix.mulVec_mulVec, herm_UH hρU]

end Formalism.L2.SG.HermitianMatrixIdentities

end
