import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantPhiSolutionMemOEStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesLiftOfPeriodPowSmulIntegralMatrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantPhiModuleMatrixMemOE
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.EquivKisin

set_option maxHeartbeats 1000000 in

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N N' d d' : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Pre bk N d ρ) (F' : Pre bk N' d' ρ') (f : Matrix (Fin d') (Fin d) (ℤ_[l])), (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) (bk.S), F'.T * Y.map bk.evW = zW f * F.T := by
  intro l _ K bk τ hτ N N' d d' ρ ρ' F F' f hf
  obtain ⟨u, hu⟩ := F'.unit
  have cancel : ∀ M M' : Matrix (Fin d') (Fin d) (WCb l), F'.T * M = F'.T * M' → M = M' := by
    intro M M' h
    have h2 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) h
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  set Xm : Matrix (Fin d') (Fin d) (WCb l) := (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * (zW f * F.T) with hXm
  have hX : F'.T * Xm = zW f * F.T := by
    rw [hXm, ← hu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

  have hfix : ∀ g : ↥(GK K), bk.FixFlat g → Xm.map (galW l (g : GQ l)) = Xm := by
    intro g hg
    let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M :=
      fun M => Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have a1 : zW (ρ' g) * F'.T.map G = F'.T := F'.fix g hg
    have a2 : zW (ρ g) * F.T.map G = F.T := F.fix g hg
    change Xm.map G = Xm
    apply cancel
    have h1 := congrArg (fun M => M.map G) hX
    simp only [Matrix.map_mul, hzG] at h1
    calc F'.T * Xm.map G = zW (ρ' g) * (F'.T.map G * Xm.map G) := by
          rw [← Matrix.mul_assoc, a1]
      _ = zW (ρ' g * f) * F.T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * F.T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = F'.T * Xm := by rw [a2, hX]

  have hφ : bk.evW bk.E ^ N • (F'.A.map bk.evW * Xm.map (frobW l)) =
      bk.evW bk.E ^ N' • (Xm * F.A.map bk.evW) := by
    let Fr : WCb l →+* WCb l := (frobW l).toRingHom
    have hzF : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map Fr = zW M :=
      fun M => Matrix.ext fun i j => (frobW l).commutes _
    have b1 : bk.evW bk.E ^ N • F.T.map Fr = F.T * F.A.map bk.evW := F.φ
    have b2 : bk.evW bk.E ^ N' • F'.T.map Fr = F'.T * F'.A.map bk.evW := F'.φ
    change bk.evW bk.E ^ N • (F'.A.map bk.evW * Xm.map Fr) = bk.evW bk.E ^ N' • (Xm * F.A.map bk.evW)
    apply cancel
    have h1 := congrArg (fun M => M.map Fr) hX
    simp only [Matrix.map_mul, hzF] at h1
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← b2, Matrix.smul_mul, h1, smul_smul,
      ← Matrix.mul_assoc, hX, Matrix.mul_assoc, ← b1, Matrix.mul_smul, smul_smul, mul_comm]

  have hOE : ∀ i j, Xm i j ∈ bk.OE := by
    obtain ⟨w, hw, hew⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.2.1 bk.E (GlobalTheory.BSP.EquivOE.not_dvd_E bk)
    have hA : F.A.map bk.evW * F.A'.map bk.evW =
        bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
      rw [← Matrix.map_mul, F.A_mul]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    have h1 : Xm = (w ^ (N' + 2 * N) * bk.evW bk.E ^ N) •
        (F'.A.map bk.evW * Xm.map (frobW l) * F.A'.map bk.evW) := by
      rw [mul_smul, ← Matrix.smul_mul, hφ, Matrix.smul_mul, Matrix.mul_assoc, hA, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, smul_smul, mul_assoc, ← pow_add, ← mul_pow, mul_comm w, hew, one_pow, one_smul]
    intro i j
    refine GlobalTheory.T.mem_OE_of_invariant_frobenius_solution l K bk (Fin d' × Fin d) (fun p => Xm p.1 p.2)
      (fun p q => w ^ (N' + 2 * N) * bk.evW bk.E ^ N * bk.evW (F'.A q.1 p.1) * bk.evW (F.A' p.2 q.2))
      (fun p q => ?_) (fun q => ?_) (fun g h q => ?_) (i, j)
    · exact bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.pow_mem hw _)
        (bk.OE.pow_mem (GlobalTheory.BSP.EquivOE.evW_mem bk _) _)) (GlobalTheory.BSP.EquivOE.evW_mem bk _))
        (GlobalTheory.BSP.EquivOE.evW_mem bk _)
    · have h2 := congrFun (congrFun h1 q.1) q.2
      rw [h2, Fintype.sum_prod_type_right]
      simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
    · exact congrFun (congrFun (hfix g h) q.1) q.2

  obtain ⟨Y₁, Y₁', hY₁, hY₁'⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N' d' ρ' F'
  obtain ⟨Y₂, Y₂', hY₂, hY₂'⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F
  set t : WCb l := inclW l τ with ht
  have hinv : t ^ N' • Y₁'.map (inclW l) = t ^ N' • (t ^ N' • (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l))) := by
    have e1 := congrArg (fun M => M.map (inclW l)) hY₁'
    simp only [Matrix.map_mul, hY₁] at e1
    have e2 : (τ ^ (2 * N') • (1 : Matrix (Fin d') (Fin d') (Ainf l))).map (inclW l) =
        (t ^ N' * t ^ N') • (1 : Matrix (Fin d') (Fin d') (WCb l)) := by
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply, ht, ← pow_add, two_mul]
    rw [e2, Matrix.smul_mul, ← hu] at e1
    have e3 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) e1
    simp only [Matrix.mul_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_one] at e3
    rw [e3, smul_smul]
  have hzf : (f.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW f := by
    exact Matrix.ext fun i j => (inclWA l).commutes (f i j)
  let x : Matrix (Fin d') (Fin d) (Ainf l) := τ ^ N' • (Y₁' * f.map (algebraMap ℤ_[l] (Ainf l)) * Y₂)
  have hx : x.map (inclW l) = inclW l τ ^ (2 * N' + N) • Xm := by
    have : x.map (inclW l) = t ^ N' • (Y₁'.map (inclW l) * zW f * (t ^ N • F.T)) := by
      have e : x.map (inclW l) = t ^ N' • ((Y₁' * f.map (algebraMap ℤ_[l] (Ainf l)) * Y₂).map (inclW l)) :=
        Matrix.ext fun i j => by simp only [x, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, ht]
      rw [e, Matrix.map_mul, Matrix.map_mul, hzf, hY₂]
    rw [this, ← Matrix.smul_mul, ← Matrix.smul_mul, hinv, hXm]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [← ht]
    congr 1
    ring
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_powerSeries_lift_of_period_pow_smul_integral_matrix l K bk τ hτ d d' (2 * N' + N) Xm x hOE hx
  exact ⟨Y, by rw [hY, hX]⟩

end GlobalTheory.BKLim.EquivKisin

end
