import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabUMapEqOfRoots
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

open scoped Classical

namespace GlobalTheory.FrameStab

open Formalism.L2.SG.RealObj

variable {n m r : ℕ}

def colMat (f : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin m) ℂ := Matrix.of fun i a => f a i

theorem isMatOn_iff (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin m → Fin n → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.LoopAct.IsMatOn g f M ↔ g * colMat f = colMat f * M := by
  constructor
  · intro h
    ext i b
    have := congrFun (h b) i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, colMat, Matrix.of_apply, this, mul_comm]
  · intro h b
    ext i
    have := congrFun (congrFun h i) b
    simp only [Matrix.mul_apply, colMat, Matrix.of_apply] at this
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, this, mul_comm]

theorem zhat_eq (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.L2.SG.RealObj.Zhat ε f f' G = (colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  ext a b
  simp only [Formalism.L2.SG.RealObj.Zhat, Formalism.L2.SG.HidaSetting.hJ, Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat,
    Matrix.of_apply, Matrix.conjTranspose_apply, Pi.star_apply]

theorem conjTranspose_mul_zhat_mul {ε : Fin n → Bool} {f f' : Fin (r + 1) → Fin n → ℂ}
    {Y G Gi : Matrix (Fin n) (Fin n) ℂ} {P M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hY : Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε) (hG : G * Gi = 1)
    (hP : GlobalTheory.LoopAct.IsMatOn Y f P) (hM : GlobalTheory.LoopAct.IsMatOn (Gi * Y * G) f' M) :
    Pᴴ * (Formalism.L2.SG.RealObj.Zhat ε f f' G * M) = Formalism.L2.SG.RealObj.Zhat ε f f' G := by
  rw [isMatOn_iff] at hP hM
  rw [zhat_eq]
  calc Pᴴ * ((colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' * M)
      = (colMat f * P)ᴴ * Formalism.REAL.Jm ε * G * (colMat f' * M) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Y * colMat f)ᴴ * Formalism.REAL.Jm ε * G * (Gi * Y * G * colMat f') := by rw [hP, hM]
    _ = (colMat f)ᴴ * (Yᴴ * Formalism.REAL.Jm ε * ((G * Gi) * Y)) * G * colMat f' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' := by
        rw [hG, Matrix.one_mul, hY]

theorem isLoUni_conjTranspose {N : ℕ} {P : Matrix (Fin N) (Fin N) ℂ} (h : Formalism.MainNotions.S.IsUpUni P) :
    Formalism.MainNotions.S.IsLoUni Pᴴ := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.conjTranspose_apply, (h j i).1 hij, star_zero]
  · rw [Matrix.conjTranspose_apply, (h j i).2 hij.symm, star_one]

theorem mem_stabU_of_conjTranspose_mul {N : ℕ} {Z P M : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det)
    (hP : Formalism.MainNotions.S.IsUpUni P) (hM : Formalism.MainNotions.S.IsUpUni M) (h : Pᴴ * (Z * M) = Z) :
    M ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨hM, ?_⟩
  have e : Pᴴ * (Z * M * Z⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_nonsing_inv _ hZ]
  rw [← Matrix.inv_eq_right_inv e]
  exact (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv (isLoUni_conjTranspose hP)).1

end GlobalTheory.FrameStab

namespace GlobalTheory.FrameStab

variable {n r : ℕ}

theorem exists_coeff_of_mem_spanLt {e : Fin r → Fin n → ℂ} {k : ℕ} {x : Fin n → ℂ}
    (hx : x ∈ Formalism.L2.SG.HidaSetting.spanLt e k) :
    ∃ c : Fin r → ℂ, (∀ b : Fin r, ¬ b.1 < k → c b = 0) ∧ x = ∑ b, c b • e b := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hx
  refine ⟨l, fun b hb => ?_, ?_⟩
  · exact (Finsupp.mem_supported' ℂ l).1 hl b hb
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul _ _

theorem exists_isUpUni_isMatOn {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.L2.SG.HidaSetting.InS e z Y) :
    ∃ P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, Formalism.MainNotions.S.IsUpUni P ∧
      GlobalTheory.LoopAct.IsMatOn Y (Formalism.L2.SG.RealObj.fam e z) P := by
  choose ca hca0 hcae using fun a : Fin r => exists_coeff_of_mem_spanLt (h.1 a)
  obtain ⟨cz, -, hcz⟩ := exists_coeff_of_mem_spanLt h.2
  let Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := fun i j =>
    Fin.lastCases (motive := fun _ => ℂ) 0
      (fun c : Fin r => Fin.lastCases (motive := fun _ => ℂ) (cz c) (fun a : Fin r => ca a c) j) i
  have hQl : ∀ j, Q (Fin.last r) j = 0 := fun j => by simp [Q]
  have hQcl : ∀ c, Q (Fin.castSucc c) (Fin.last r) = cz c := fun c => by simp [Q]
  have hQcc : ∀ c a, Q (Fin.castSucc c) (Fin.castSucc a) = ca a c := fun c a => by simp [Q]
  refine ⟨1 + Q, fun i j => ?_, fun b => ?_⟩
  · refine Fin.lastCases ?_ (fun c => ?_) i
    · refine ⟨fun hj => ?_, fun hj => ?_⟩
      · rw [Matrix.add_apply, hQl, Matrix.one_apply_ne (ne_of_lt hj).symm, add_zero]
      · rw [Matrix.add_apply, hQl, hj, Matrix.one_apply_eq, add_zero]
    · refine Fin.lastCases ?_ (fun a => ?_) j
      · exact ⟨fun hj => absurd hj (not_lt.2 (Fin.castSucc_lt_last c).le),
          fun hj => absurd hj (Fin.castSucc_lt_last c).ne⟩
      · refine ⟨fun hj => ?_, fun hj => ?_⟩
        · rw [Matrix.add_apply, hQcc, Matrix.one_apply_ne (ne_of_lt hj).symm, zero_add]
          exact hca0 a c (not_lt.2 (Fin.castSucc_lt_castSucc_iff.1 hj).le)
        · rw [Matrix.add_apply, hQcc, hj, Matrix.one_apply_eq, Fin.castSucc_inj.1 hj]
          rw [hca0 a a (lt_irrefl _), add_zero]
  · rw [Fin.sum_univ_castSucc]
    simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, Fin.snoc_last, Matrix.add_apply, add_smul,
      Finset.sum_add_distrib, hQl, zero_smul, add_zero]
    refine Fin.lastCases ?_ (fun a => ?_) b
    · simp only [Fin.snoc_last, hQcl, Matrix.one_apply_eq, one_smul,
        Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne, zero_smul, Finset.sum_const_zero, zero_add]
      rw [← hcz, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
    · simp only [Fin.snoc_castSucc, hQcc, Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne', zero_smul,
        add_zero]
      have e1 : ∑ x : Fin r, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.castSucc x) (Fin.castSucc a) • e x
          = e a := by
        simp only [Matrix.one_apply, Fin.castSucc_inj, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [e1, ← hcae a, Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]

end GlobalTheory.FrameStab

namespace GlobalTheory.FrameStab

theorem frameMat_mem_stabU : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ y : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), y ∈ Formalism.L2.SG.RealObj.StInf X u u' γ → IsUpUni M → GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * y * γ) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) M → IsUnit (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v).det → M ∈ GlobalTheory.LoopV.stabU (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v) := by
  intro D X u u' γ y v M hy hMu hM hZ
  obtain ⟨P, hPu, hP⟩ := exists_isUpUni_isMatOn ((hy.1 v).1)
  have hf : Formalism.L2.SG.RealObj.frm X u 1 v = Formalism.L2.SG.RealObj.fam
      (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc]
  rw [← hf] at hP
  have hY : (uMat (y v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (y v) = Formalism.REAL.Jm (X.B.I.ε v) := (y v).2
  have hG : uMat (γ v) * uMat (γ⁻¹ v) = 1 := by
    show uMat ((γ * γ⁻¹) v) = 1
    rw [mul_inv_cancel]
    rfl
  exact mem_stabU_of_conjTranspose_mul hZ hPu hMu (conjTranspose_mul_zhat_mul hY hG hP hM)

end GlobalTheory.FrameStab

end
