import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXSig

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

theorem inN_indep {n r : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ}
    (hz' : ∀ a, hJ ε (e a) z' = 0) {g : Matrix (Fin n) (Fin n) ℂ} (h : InN ε e z g) : InN ε e z' g :=
  ⟨⟨h.1.1, h.2 z' hz'⟩, h.2⟩

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem Qm_mulVec_eq_sum (w : Fin (2 * r + k + 1) → ℂ) : Qm e f wf z0 *ᵥ w = ∑ j, w j • colQ e f wf z0 j := by
  funext i
  simp only [mulVec, dotProduct, Qm, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem Qm_mem_spanLt {a : ℕ} (ha : a ≤ r) (w : Fin (2 * r + k + 1) → ℂ)
    (hw : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → w i = 0) : Qm e f wf z0 *ᵥ w ∈ spanLt e a := by
  rw [Qm_mulVec_eq_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j.val < a
  · have hjr : j.val < r := lt_of_lt_of_le hj ha
    have hc : colQ e f wf z0 j = e ⟨j.val, hjr⟩ := by simp [colQ, hjr]
    rw [hc]
    unfold spanLt
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j.val, hjr⟩, hj, rfl⟩)
  · rw [hw j (not_lt.mp hj), zero_smul]
    exact Submodule.zero_mem _

theorem sub_one_eI {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) (a : Fin r)
    (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) : ((m - 1) *ᵥ bvec (eI k r a)) i = 0 := by
  rw [bvec, mulVec_single_one, col_apply, Matrix.sub_apply, hm.2.1 a i hi, one_apply, sub_self]

theorem sub_one_mulVec_apply_eq_zero_of_mem_Nset {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r)
    (w : Fin (2 * r + k + 1) → ℂ) (hw : ∀ j : Fin (2 * r + k + 1), r + k < j.val → w j = 0)
    (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) : ((m - 1) *ᵥ w) i = 0 := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases lt_or_ge (r + k) j.val with hj | hj
  · rw [hw j hj, mul_zero]
  · rcases lt_or_ge j.val r with hj' | hj'
    · have h1 := hm.2.1 ⟨j.val, hj'⟩ i (by show j.val ≤ i.val; omega)
      have he : eI k r ⟨j.val, hj'⟩ = j := Fin.ext rfl
      rw [he] at h1
      rw [Matrix.sub_apply, h1, one_apply, sub_self, zero_mul]
    · rw [Matrix.sub_apply, hm.2.2 i j hj' hj hi, one_apply, sub_self, zero_mul]

theorem Qi_perp (y : Fin (2 * r + k + 1) → ℂ) (hy : ∀ a, hJ ε (e a) y = 0) (j : Fin (2 * r + k + 1))
    (hj : r + k < j.val) : (Qi ε e f wf z0 *ᵥ y) j = 0 := by
  have hv : ∀ l : Fin (2 * r + k + 1), l.val < r → ((Qm e f wf z0)ᴴ *ᵥ (REAL.Jm ε *ᵥ y)) l = 0 := by
    intro l hl
    have hc : colQ e f wf z0 l = e ⟨l.val, hl⟩ := by simp [colQ, hl]
    have h1 := hy ⟨l.val, hl⟩
    rw [← hc] at h1
    rw [← h1]
    simp only [hJ, mulVec, dotProduct, conjTranspose_apply, Qm, of_apply, Pi.star_apply]
  unfold Qi
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  change ∑ l, Hpk k r j l * ((Qm e f wf z0)ᴴ *ᵥ (REAL.Jm ε *ᵥ y)) l = 0
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < r
  · rw [hv l hl, mul_zero]
  · have h0 : Hpk k r j l = 0 := by
      simp only [Hpk]
      split_ifs with h1 h2 h3 <;> first | rfl | omega
    rw [h0, zero_mul]

theorem inN_of_conj (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hzB : inWb k r zB)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : Qi ε e f wf z0 * g * Qm e f wf z0 ∈ Nset k r) :
    InN ε e (Qm e f wf z0 *ᵥ zB) g := by
  have hg : Qm e f wf z0 * (Qi ε e f wf z0 * g * Qm e f wf z0) * Qi ε e f wf z0 = g := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul, Matrix.mul_assoc,
      Qm_mul_Qi hF, Matrix.mul_one]
  have key : ∀ v, (g - 1) *ᵥ v
      = Qm e f wf z0 *ᵥ ((Qi ε e f wf z0 * g * Qm e f wf z0 - 1) *ᵥ (Qi ε e f wf z0 *ᵥ v)) := by
    intro v
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, hg, Matrix.mul_one, Qm_mul_Qi hF]
  have hz : Qi ε e f wf z0 *ᵥ (Qm e f wf z0 *ᵥ zB) = zB := by
    rw [mulVec_mulVec, Qi_mul_Qm hF, one_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, Qi_e hF]
    exact Qm_mem_spanLt (le_of_lt a.isLt) _ (fun i hi => sub_one_eI hm a i hi)
  · rw [key, hz]
    exact Qm_mem_spanLt le_rfl _ (fun i hi => sub_one_mulVec_apply_eq_zero_of_mem_Nset hm zB (fun j hj => hzB j (Or.inr hj)) i hi)
  · rw [key]
    exact Qm_mem_spanLt le_rfl _ (fun i hi => sub_one_mulVec_apply_eq_zero_of_mem_Nset hm _ (fun j hj => Qi_perp y hy j hj) i hi)

theorem refN_map (hF : IsFrameJ ε e f wf z0) :
    (refN ε e f wf z0).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) = Jac.N1 k r := by
  have h := measN_of hF 1
  rwa [ENNReal.ofReal_one, one_smul] at h

theorem refN_isHaarLoc (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hzB : inWb k r zB)
    (hz0 : ∃ t : ℂ, z0 = t • (Qm e f wf z0 *ᵥ zB)) :
    IsHaarLoc (NLoc ε e (Qm e f wf z0 *ᵥ zB)) (refN ε e f wf z0) := by
  set C := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hC
  have hE : MeasurableEmbedding C := embQ hF
  have hmap : Measure.map C (refN ε e f wf z0) = Jac.N1 k r := refN_map hF
  have hH := Jac.nilradical_measure_is_haar (k := k) (r := r)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : SigmaFinite (Measure.map C (refN ε e f wf z0)) := by
      rw [hmap]
      exact hH.1
    exact SigmaFinite.of_map _ hE.measurable.aemeasurable hs
  · intro h0
    apply hH.2.1
    rw [← hmap, h0, Measure.map_zero]
  · refine measure_mono_null (t := C ⁻¹' {x : Mt k r | of x ∉ Nset k r}) ?_ ?_
    · intro g hg
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      intro hm
      exact hg (inN_of_conj hF hzB hm)
    · rw [← hE.map_apply, hmap]
      exact hH.2.2.1
  · intro s hs
    have hsN := conj_mem_Nset hF hz0 (uMat_mem s) hs
    have hcomp : C ∘ (fun x => s * x) = lmulM (Qi ε e f wf z0 * uMat s * Qm e f wf z0) ∘ C := by
      funext x
      simp only [Function.comp_apply, hC]
      rw [lmulM_cM]
      show Qi ε e f wf z0 * uMat (s * x) * Qm e f wf z0
        = Qi ε e f wf z0 * uMat s * Qm e f wf z0 * Qi ε e f wf z0 * uMat x * Qm e f wf z0
      rw [uMat_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Qm e f wf z0) (Qi ε e f wf z0), Qm_mul_Qi hF, Matrix.one_mul]
    have hms : Measurable (fun x : ↥(REAL.UJ ε) => s * x) := by
      rw [← hE.measurable_comp_iff, hcomp]
      exact (measurable_lmulM _).comp hE.measurable
    have hmm : Measure.map C (Measure.map (fun x => s * x) (refN ε e f wf z0))
        = Measure.map C (refN ε e f wf z0) := by
      rw [Measure.map_map hE.measurable hms, hcomp, ← Measure.map_map (measurable_lmulM _) hE.measurable,
        hmap, hH.2.2.2 _ hsN]
    calc Measure.map (fun x => s * x) (refN ε e f wf z0)
        = Measure.comap C (Measure.map C (Measure.map (fun x => s * x) (refN ε e f wf z0))) :=
          (hE.comap_map _).symm
      _ = Measure.comap C (Measure.map C (refN ε e f wf z0)) := by rw [hmm]
      _ = refN ε e f wf z0 := hE.comap_map _

end Formalism.L2.SG.Pf.NcReal.JX
