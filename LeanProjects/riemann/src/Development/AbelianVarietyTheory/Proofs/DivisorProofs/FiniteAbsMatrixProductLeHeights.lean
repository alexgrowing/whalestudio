import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory

theorem absFin_mul_mul_transpose_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (g : GL (Fin n) (AF F ⊗[F] E)) (X : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (j : Fin d), absFin F v (compFin F E v (((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * X * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) i j)) ≤ htFin F v (bc (compFin F E v) g) * (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) * htFin F v (bc (compFin F E v) h) := by
  intro F E _ _ _ _ _ n d g X h v i j
  have hg : ∀ a b, ((bc (compFin F E v) g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b = compFin F E v ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b) := by
    intro a b; rfl
  have hh : ∀ a b, ((bc (compFin F E v) h : GL (Fin d) (Fv F v ⊗[F] E)) : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E)) a b = compFin F E v ((h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) a b) := by
    intro a b; rfl
  have hG : ∀ a b, absFin F v (compFin F E v ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b)) ≤ htFin F v (bc (compFin F E v) g) := by
    intro a b
    have h1 := absFin_le_normFin F v ((bc (compFin F E v) g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b
    rw [hg] at h1
    exact h1.trans (le_htOf (normFin F v) _)
  have hH : ∀ a b, absFin F v (compFin F E v ((h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) a b)) ≤ htFin F v (bc (compFin F E v) h) := by
    intro a b
    have h1 := absFin_le_normFin F v ((bc (compFin F E v) h : GL (Fin d) (Fv F v ⊗[F] E)) : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E)) a b
    rw [hh] at h1
    exact h1.trans (le_htOf (normFin F v) _)
  have hX : ∀ a b, absFin F v (compFin F E v (X a b)) ≤ Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2)) := by
    intro a b
    exact Finset.le_sup (f := fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) (b := (a, b)) (Finset.mem_univ _)
  rw [Matrix.mul_apply, map_sum]
  refine absFin_sum_le F v _ _ fun l _ => ?_
  rw [Matrix.transpose_apply, Matrix.mul_apply, map_mul, map_sum]
  refine (absFin_mul_le F v _ _).trans (mul_le_mul' (absFin_sum_le F v _ _ fun k _ => ?_) (hH _ _))
  rw [map_mul]
  exact (absFin_mul_le F v _ _).trans (mul_le_mul' (hG _ _) (hX _ _))

end GlobalTheory
