import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.OppositeCellIntegration
import GroundTheory.AutomorphicForms.DixmierMalliavinHaar
import GroundTheory.AutomorphicForms.AdelicDixmierMalliavinLie
noncomputable section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GroundTheory.Automorphic
open scoped InnerProductSpace Topology ENNReal NNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.ModP

variable {n a : ℕ}

def jAdj (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun Y := Jm ε * Yᴴ * Jm ε
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' r Y := by
    ext i k
    simp [Matrix.conjTranspose_smul]

theorem jAdj_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : jAdj ε Y = Jm ε * Yᴴ * Jm ε := rfl

theorem jAdj_one (ε : Fin n → Bool) : jAdj ε 1 = 1 := by
  simp [jAdj_apply, Jm_mul_self]

theorem jAdj_mul (ε : Fin n → Bool) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    jAdj ε (X * Y) = jAdj ε Y * jAdj ε X := by
  simp only [jAdj_apply, Matrix.conjTranspose_mul]
  calc Jm ε * (Yᴴ * Xᴴ) * Jm ε = Jm ε * Yᴴ * 1 * Xᴴ * Jm ε := by simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = _ := by rw [← Jm_mul_self ε]; simp only [Matrix.mul_assoc]

theorem jAdj_jAdj (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : jAdj ε (jAdj ε Y) = Y := by
  simp only [jAdj_apply, Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.conjTranspose_conjTranspose]
  calc Jm ε * (Jm ε * (Y * Jm ε)) * Jm ε = (Jm ε * Jm ε) * Y * (Jm ε * Jm ε) := by simp only [Matrix.mul_assoc]
    _ = Y := by rw [Jm_mul_self]; simp

def jPerp (ε : Fin n → Bool) (U : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {y | ∀ z ∈ U, star z ⬝ᵥ (Jm ε *ᵥ y) = 0}
  add_mem' {y y'} h h' z hz := by
    have e1 := h z hz
    have e2 := h' z hz
    rw [Matrix.mulVec_add, dotProduct_add, e1, e2, add_zero]
  zero_mem' z _ := by simp
  smul_mem' c y h z hz := by
    have e1 := h z hz
    rw [Matrix.mulVec_smul, dotProduct_smul, e1, smul_zero]

def flagChain (ε : Fin n → Bool) (W : Flag n a) (k : Fin (2 * a + 2)) : Submodule ℂ (Fin n → ℂ) :=
  if h : (k : ℕ) ≤ a then W ⟨k, by omega⟩ else jPerp ε (W ⟨2 * a + 1 - k, by omega⟩)

def qAlg (ε : Fin n → Bool) (W : Flag n a) : Subalgebra ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | ∀ i, ∀ y ∈ W i, Y *ᵥ y ∈ W i ∧ jAdj ε Y *ᵥ y ∈ W i}
  mul_mem' {X Y} hX hY i y hy := by
    refine ⟨?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec]; exact (hX i _ (hY i y hy).1).1
    · rw [jAdj_mul, ← Matrix.mulVec_mulVec]; exact (hY i _ (hX i y hy).2).2
  add_mem' {X Y} hX hY i y hy := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.add_mulVec]; exact (W i).add_mem (hX i y hy).1 (hY i y hy).1
    · rw [map_add, Matrix.add_mulVec]; exact (W i).add_mem (hX i y hy).2 (hY i y hy).2
  algebraMap_mem' c i y hy := by
    have e : algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) c = c • (1 : Matrix (Fin n) (Fin n) ℂ) := Algebra.algebraMap_eq_smul_one c
    refine ⟨?_, ?_⟩
    · rw [e, Matrix.smul_mulVec, Matrix.one_mulVec]; exact (W i).smul_mem c hy
    · have e2 : jAdj ε (c • (1 : Matrix (Fin n) (Fin n) ℂ)) = (star c) • 1 := by
        simp only [jAdj_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Jm_mul_self]
      rw [e, e2, Matrix.smul_mulVec, Matrix.one_mulVec]; exact (W i).smul_mem _ hy

theorem mem_qAlg {ε : Fin n → Bool} {W : Flag n a} {Y : Matrix (Fin n) (Fin n) ℂ} :
    Y ∈ qAlg ε W ↔ ∀ i, ∀ y ∈ W i, Y *ᵥ y ∈ W i ∧ jAdj ε Y *ᵥ y ∈ W i := Iff.rfl

theorem jAdj_mem_qAlg {ε : Fin n → Bool} {W : Flag n a} {Y : Matrix (Fin n) (Fin n) ℂ} (h : Y ∈ qAlg ε W) :
    jAdj ε Y ∈ qAlg ε W := fun i y hy => ⟨(h i y hy).2, by rw [jAdj_jAdj]; exact (h i y hy).1⟩

instance (ε : Fin n → Bool) (W : Flag n a) : FiniteDimensional ℂ (qAlg ε W) :=
  inferInstanceAs (FiniteDimensional ℂ (Subalgebra.toSubmodule (qAlg ε W)))

instance (ε : Fin n → Bool) (W : Flag n a) : FiniteDimensional ℝ (qAlg ε W) :=
  Module.Finite.trans ℂ _

abbrev QA (ε : Fin n → Bool) (W : Flag n a) : Type := RegNorm (qAlg ε W)

def qMat {ε : Fin n → Bool} {W : Flag n a} (x : QA ε W) : Matrix (Fin n) (Fin n) ℂ :=
  ((RegNorm.toRegNorm (qAlg ε W)).symm x : qAlg ε W).1

def qAdj (ε : Fin n → Bool) (W : Flag n a) : QA ε W →ₗ[ℝ] QA ε W where
  toFun x := RegNorm.toRegNorm (qAlg ε W) ⟨jAdj ε (qMat x), jAdj_mem_qAlg ((RegNorm.toRegNorm (qAlg ε W)).symm x).2⟩
  map_add' x y := by
    apply (RegNorm.toRegNorm (qAlg ε W)).symm.injective
    apply Subtype.ext
    exact map_add (jAdj ε) (qMat x) (qMat y)
  map_smul' r x := by
    apply (RegNorm.toRegNorm (qAlg ε W)).symm.injective
    apply Subtype.ext
    exact map_smul (jAdj ε) r (qMat x)

theorem qMat_qAdj (ε : Fin n → Bool) (W : Flag n a) (x : QA ε W) : qMat (qAdj ε W x) = jAdj ε (qMat x) := rfl

theorem qMat_injective {ε : Fin n → Bool} {W : Flag n a} : Function.Injective (qMat (ε := ε) (W := W)) :=
  fun _ _ h => (RegNorm.toRegNorm (qAlg ε W)).symm.injective (Subtype.ext h)

theorem qMat_one {ε : Fin n → Bool} {W : Flag n a} : qMat (1 : QA ε W) = 1 := rfl

theorem qMat_mul {ε : Fin n → Bool} {W : Flag n a} (x y : QA ε W) : qMat (x * y) = qMat x * qMat y := rfl

theorem qAdj_one (ε : Fin n → Bool) (W : Flag n a) : qAdj ε W 1 = 1 :=
  qMat_injective (by rw [qMat_qAdj, qMat_one, jAdj_one])

theorem qAdj_mul (ε : Fin n → Bool) (W : Flag n a) (x y : QA ε W) : qAdj ε W (x * y) = qAdj ε W y * qAdj ε W x :=
  qMat_injective (by rw [qMat_qAdj, qMat_mul, jAdj_mul, qMat_mul, qMat_qAdj, qMat_qAdj])

abbrev qGroup (ε : Fin n → Bool) (W : Flag n a) : Subgroup (QA ε W)ˣ :=
  formGroup (qAdj ε W) (qAdj_one ε W) (qAdj_mul ε W) 1

end GlobalTheory.CompanionTheory.ModP
