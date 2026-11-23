import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

section AntiTranspose

variable {R : Type*} [CommRing R]

def antiTr (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![A 1 1, A 0 1; A 1 0, A 0 0]

theorem antiTr_mul (A B : Matrix (Fin 2) (Fin 2) R) : antiTr (A * B) = antiTr B * antiTr A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antiTr, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem antiTr_one : antiTr (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antiTr]

theorem antiTr_antiTr (A : Matrix (Fin 2) (Fin 2) R) : antiTr (antiTr A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antiTr]

def antiTrGL (g : GL (Fin 2) R) : GL (Fin 2) R where
  val := antiTr (g : Matrix (Fin 2) (Fin 2) R)
  inv := antiTr ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
  val_inv := by rw [← antiTr_mul, Units.inv_mul, antiTr_one]
  inv_val := by rw [← antiTr_mul, Units.mul_inv, antiTr_one]

theorem coe_antiTrGL (g : GL (Fin 2) R) :
    (antiTrGL g : Matrix (Fin 2) (Fin 2) R) = antiTr (g : Matrix (Fin 2) (Fin 2) R) := rfl

theorem antiTrGL_mul (x y : GL (Fin 2) R) : antiTrGL (x * y) = antiTrGL y * antiTrGL x :=
  Units.ext (antiTr_mul _ _)

theorem antiTrGL_inv (x : GL (Fin 2) R) : antiTrGL x⁻¹ = (antiTrGL x)⁻¹ :=
  Units.ext rfl

theorem antiTrGL_antiTrGL (x : GL (Fin 2) R) : antiTrGL (antiTrGL x) = x :=
  Units.ext (antiTr_antiTr _)

end AntiTranspose

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem antiTr_entries_mem {A : Matrix (Fin 2) (Fin 2) F} (hA : ∀ a b, A a b ∈ 𝒪[F]) (a b : Fin 2) :
    antiTr A a b ∈ 𝒪[F] := by
  fin_cases a <;> fin_cases b <;> simpa [antiTr] using hA _ _

theorem antiTrGL_mem_integralGL {x : GL (Fin 2) F} (hx : x ∈ integralGL F 2) :
    antiTrGL x ∈ integralGL F 2 := by
  obtain ⟨h1, h2⟩ := (mem_integralGL_iff F 2).1 hx
  refine (mem_integralGL_iff F 2).2 ⟨fun a b => antiTr_entries_mem h1 a b, fun a b => ?_⟩
  rw [← antiTrGL_inv]
  exact antiTr_entries_mem h2 a b

theorem antiTrGL_rowRep (l : Fin 2 → ℕ) (c : NormalData F l) :
    antiTrGL (rowRep (l 1) (l 0) (c ⟨(0, 1), by decide⟩)) = normalGL F l c := by
  refine Units.ext ?_
  rw [coe_antiTrGL, coe_rowRep, coe_normalGL]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [antiTr] using (normalMat_self l c 0).symm
  · simpa [antiTr] using (normalMat_of_lt l c (i := 0) (j := 1) (by decide)).symm
  · simpa [antiTr] using (normalMat_of_gt l c (i := 1) (j := 0) (by decide)).symm
  · simpa [antiTr] using (normalMat_self l c 1).symm

theorem exists_mul_rowRep_inv_mem (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (g : GL (Fin 2) F)
    (hg : ∀ a b, (g : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) :
    ∃ (i j : ℕ) (c : Fin j → 𝓀[F]), g * (rowRep i j c)⁻¹ ∈ integralGL F 2 := by
  obtain ⟨l, c, hc⟩ := exists_normalGL (g := antiTrGL g) (fun a b => antiTr_entries_mem hg a b)
  have h1 : (normalGL F l c)⁻¹ * antiTrGL g ∈ integralGL F 2 := QuotientGroup.eq.1 hc
  refine ⟨l 1, l 0, c ⟨(0, 1), by decide⟩, ?_⟩
  have h2 : antiTrGL (g * (rowRep (l 1) (l 0) (c ⟨(0, 1), by decide⟩))⁻¹) ∈ integralGL F 2 := by
    rw [antiTrGL_mul, antiTrGL_inv, antiTrGL_rowRep]
    exact h1
  have h3 := antiTrGL_mem_integralGL h2
  rwa [antiTrGL_antiTrGL] at h3

end GlobalTheory.CompanionTheory.LFUDom
