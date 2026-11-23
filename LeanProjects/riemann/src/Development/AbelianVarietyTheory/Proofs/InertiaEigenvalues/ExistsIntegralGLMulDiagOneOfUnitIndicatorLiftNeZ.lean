import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLeMaxUltra
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem exists_emb_of_last {F : Type} [Field F] (r : ℕ) (m : GL (Fin (r + 1)) F)
    (hc : (m : Matrix _ _ F) *ᵥ GlobalTheory.JR.Step.eL r F = GlobalTheory.JR.Step.eL r F)
    (hr : GlobalTheory.JR.Step.eL r F ᵥ* (m : Matrix _ _ F) = GlobalTheory.JR.Step.eL r F) :
    ∃ s : GL (Fin r) F, m = GlobalTheory.JR.Step.emb r F s := by
  classical
  set t : Matrix (Fin r) (Fin r) F := (m : Matrix _ _ F).submatrix Fin.castSucc Fin.castSucc with ht
  have hcol : ∀ i, (m : Matrix _ _ F) i (Fin.last r) = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) i := by
    intro i
    have := congrFun hc i
    simpa [GlobalTheory.JR.Step.eL, Matrix.mulVec_single_one] using this
  have hrow : ∀ j, (m : Matrix _ _ F) (Fin.last r) j = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) j := by
    intro j
    have := congrFun hr j
    simpa [GlobalTheory.JR.Step.eL, Matrix.single_one_vecMul] using this
  have hm : (m : Matrix _ _ F) = GlobalTheory.JR.Step.embHom r F t := by
    ext i j
    induction i using Fin.lastCases with
    | last =>
      rw [hrow j]
      induction j using Fin.lastCases with
      | last => simp [GlobalTheory.JR.Step.embHom]
      | cast j => simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [hcol]; simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
      | cast j => simp [GlobalTheory.JR.Step.embHom, ht]
  have hdet : (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F).det = t.det := by
    rw [hm]
    simp [GlobalTheory.JR.Step.embHom, Matrix.det_fromBlocks_zero₂₁]
  have hu : IsUnit t.det := by
    rw [← hdet]
    exact (Matrix.isUnit_iff_isUnit_det (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F)).mp (Units.isUnit m)
  refine ⟨Matrix.nonsingInvUnit t hu, ?_⟩
  ext : 1
  rw [hm]
  rfl

end GlobalTheory.JR.GLift

namespace GlobalTheory.JR.GLift

theorem support_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 →
    ∀ g : GL (Fin (r + 1)) F, unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
      ∃ k ∈ glO (r + 1) F, ∃ s : GL (Fin r) F, g = k * GlobalTheory.JR.Step.emb r F s := by
  intro F E _ _ _ _ _ r Z μ l hμ g hg
  classical
  obtain ⟨-, hb, hc, -⟩ := Set.mem_of_indicator_ne_zero hg
  simp only [act, GlobalTheory.JR.Step.lift] at hb hc
  set e : Fin (r + 1) → F := GlobalTheory.JR.Step.eL r F with he
  have hv : ∀ i, ‖((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e) i‖ ≤ 1 := by
    intro i
    have := hb i
    rwa [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hμ, one_mul] at this
  have hw : ∀ i, ‖(e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) i‖ ≤ 1 := hc
  have hgg : ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.inv_mul g
  have hee : e ⬝ᵥ e = 1 := by simp [he, GlobalTheory.JR.Step.eL]
  have hwv : (e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) ⬝ᵥ ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e) = 1 := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, hee]
  obtain ⟨k, hk, hkv, hkw⟩ := GlobalTheory.LatL.glO_transitive_pairs F E r _ _ hv hw hwv
  have hkv' : (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e = (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e := hkv
  have hkw' : (e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) ᵥ* (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = e := hkw
  have hkk : ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.inv_mul k
  have hkk' : (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.mul_inv k
  have hek : e ᵥ* ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
    conv_lhs => rw [← hkw']
    rw [Matrix.vecMul_vecMul, hkk', Matrix.vecMul_one]
  obtain ⟨s, hs⟩ := exists_emb_of_last r (k⁻¹ * g) (by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hkv', Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec])
    (by rw [Units.val_mul, ← Matrix.vecMul_vecMul, hek, Matrix.vecMul_vecMul, hgg, Matrix.vecMul_one])
  exact ⟨k, hk, s, by rw [← hs, mul_inv_cancel_left]⟩

end GlobalTheory.JR.GLift
