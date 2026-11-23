import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicModulus.Row

theorem transpose_unitary {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) {J K g : Matrix n n A} (hKJ : K * J = 1)
    (hg : Formalism.UG.cT s g * J * g = J) : Formalism.UG.cT s gᵀ * Kᵀ * gᵀ = Kᵀ := by
  have hJK : J * K = 1 := mul_eq_one_comm.1 hKJ
  have h1 : (K * Formalism.UG.cT s g * J) * g = 1 := by
    rw [Matrix.mul_assoc K, Matrix.mul_assoc K, hg, hKJ]
  have h2 : g * (K * Formalism.UG.cT s g * J) = 1 := mul_eq_one_comm.1 h1
  have h3 : g * (K * Formalism.UG.cT s g) = K := by
    calc g * (K * Formalism.UG.cT s g) = g * (K * Formalism.UG.cT s g) * (J * K) := by rw [hJK, Matrix.mul_one]
      _ = g * (K * Formalism.UG.cT s g * J) * K := by simp only [Matrix.mul_assoc]
      _ = K := by rw [h2, Matrix.one_mul]
  have h4 := congrArg Matrix.transpose h3
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at h4
  exact h4

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem isHermND_inv_transpose {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) : IsHermND σ (J⁻¹)ᵀ := by
  have hu : IsUnit J.det := hJ.2.isUnit
  have hm : J.map (σ : E →+* E) = Jᵀ := by
    ext i j
    exact hJ.1 j i
  have h1 : (J⁻¹).map (σ : E →+* E) * Jᵀ = 1 := by
    rw [← hm, ← Matrix.map_mul, Matrix.nonsing_inv_mul J hu]
    simp
  have h2 : (Jᵀ)⁻¹ = (J⁻¹).map (σ : E →+* E) := Matrix.inv_eq_left_inv h1
  refine ⟨fun i j => ?_, ?_⟩
  · have h3 := congrFun (congrFun h2 i) j
    rw [← Matrix.transpose_nonsing_inv] at h3
    exact h3.symm
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det J hu).ne_zero

def transposeGL {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (g : GL n A) : GL n A :=
  ⟨g.1ᵀ, (g⁻¹).1ᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem exists_transpose (R : Type) [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (g : HA R σ J) :
    ∃ g' : HA R σ (J⁻¹)ᵀ, (HA.mat R σ (J⁻¹)ᵀ g').1 = ((HA.mat R σ J g).1)ᵀ := by
  have hu : IsUnit J.det := hJ.2.isUnit
  have hKJ : JR (F := F) R J⁻¹ * JR (F := F) R J = 1 := by
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul J hu]
    simp
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).1 * JR (F := F) R J * (HA.mat R σ J g).1 =
      JR (F := F) R J := (show HR R σ J from g).2
  exact ⟨(⟨transposeGL (HA.mat R σ J g), transpose_unitary (sigR R σ) hKJ hg⟩ : HR R σ (J⁻¹)ᵀ), rfl⟩

theorem map_vecMul_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : HA (AF F) σ J) (μ : Measure (Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → μ.map (fun x => Matrix.vecMul x ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) = μ := by
  intro F E _ _ _ _ _ σ hσ M J hJ g μ hμ
  obtain ⟨g', hg'⟩ := exists_transpose (AF F) hJ g
  have h := PI.VolSemiDirect.W.Cj.unipotent_modulus_holds F E σ hσ M _ (isHermND_inv_transpose hJ) g' μ hμ
  have e : (fun x => Matrix.vecMul x ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) =
      fun x => ((HA.mat (AF F) σ (J⁻¹)ᵀ g').1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).mulVec x := by
    funext x
    rw [hg', Matrix.mulVec_transpose]
  rw [e]
  exact h

end GlobalTheory.AdelicModulus.Row
