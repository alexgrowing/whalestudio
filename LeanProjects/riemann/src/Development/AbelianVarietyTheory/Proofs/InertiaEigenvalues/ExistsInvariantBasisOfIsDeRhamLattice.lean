import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleDeRhamPeriodMatrixOfIsDR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.DRMat

theorem toMatrix_qRep {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (g : Γ) :
    LinearMap.toMatrix (Pi.basisFun ℚ_[l] (Fin d)) (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ g) =
      (ρ g).val.map (algebraMap ℤ_[l] ℚ_[l]) := by
  rw [LinearMap.toMatrix_eq_toMatrix']
  change LinearMap.toMatrix' (Matrix.toLin' ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l]))) = _
  rw [LinearMap.toMatrix'_toLin']

theorem invariant_basis_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∃ x : Fin d → Fin d → P.R.BdR, LinearIndependent ↥K.1 x ∧ (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) ∧ ∀ c : Fin d → P.R.BdR, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c) → c ∈ Submodule.span ↥K.1 (Set.range x) := by
  intro l _ P AI T K d ρ hDR
  obtain ⟨Q, hQ⟩ := exists_period_matrix_of_isDR l P AI T (Fin d) K (Fin d → ℚ_[l])
    (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ) hDR
  set M : ↥(GK K) → Matrix (Fin d) (Fin d) P.R.BdR :=
    fun g => (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) with hM
  have hQ' : ∀ g : ↥(GK K), M g * (Q : Matrix (Fin d) (Fin d) P.R.BdR).map (P.actQdR (g : GQ l)) = Q := by
    intro g
    have h := hQ g
    rw [toMatrix_qRep, Matrix.map_map] at h
    exact h
  letI : Field P.R.BdR := (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1.toField
  set Qm : Matrix (Fin d) (Fin d) P.R.BdR := (Q : Matrix (Fin d) (Fin d) P.R.BdR) with hQm
  have hQinj : ∀ v w : Fin d → P.R.BdR, Qm *ᵥ v = Qm *ᵥ w → v = w := by
    intro v w h
    have := congrArg (fun u => ((Q⁻¹ : GL (Fin d) P.R.BdR) : Matrix (Fin d) (Fin d) P.R.BdR) *ᵥ u) h
    simp only [Matrix.mulVec_mulVec, hQm] at this
    rwa [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_mulVec, Matrix.one_mulVec] at this
  refine ⟨fun j i => Qm i j, ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have hv : Qm *ᵥ (fun j => algebraMap ↥K.1 P.R.BdR (c j)) = Qm *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      funext i
      have := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at this
      simp only [Algebra.smul_def] at this
      rw [Pi.zero_apply, ← this]
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h0 := hQinj _ _ hv
    intro j
    have := congrFun h0 j
    simp only [Pi.zero_apply] at this
    exact (FaithfulSMul.algebraMap_injective ↥K.1 P.R.BdR) (by rw [this, map_zero])
  · intro j g
    funext i
    have h := congrFun (congrFun (hQ' g) i) j
    simpa [hM, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  · intro c hc
    obtain ⟨w, hw⟩ : ∃ w, Qm *ᵥ w = c :=
      ⟨((Q⁻¹ : GL (Fin d) P.R.BdR) : Matrix (Fin d) (Fin d) P.R.BdR) *ᵥ c, by
        rw [Matrix.mulVec_mulVec, hQm, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]⟩
    have hfix : ∀ (g : ↥(GK K)) j, P.actQdR (g : GQ l) (w j) = w j := by
      intro g
      have key : Qm *ᵥ (fun j => P.actQdR (g : GQ l) (w j)) = Qm *ᵥ w := by
        have hact : (fun i => P.actQdR (g : GQ l) (c i)) =
            Qm.map (P.actQdR (g : GQ l)) *ᵥ (fun j => P.actQdR (g : GQ l) (w j)) := by
          funext i
          rw [← hw]
          exact RingHom.map_mulVec ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR) Qm w i
        have := hc g
        rw [hact, Matrix.mulVec_mulVec, hQ' g] at this
        rw [this, hw]
      exact congrFun (hQinj _ _ key)
    have hwK : ∀ j, ∃ k : ↥K.1, algebraMap ↥K.1 P.R.BdR k = w j := fun j =>
      (P.PD K).invdR (w j) fun g => by rw [P.PD_actdR]; exact hfix g j
    choose k hk using hwK
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨k, ?_⟩
    rw [← hw]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    simp only [Algebra.smul_def, hk]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.DRMat
