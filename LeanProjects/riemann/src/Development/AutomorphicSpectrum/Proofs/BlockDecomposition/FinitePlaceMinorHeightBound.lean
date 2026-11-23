import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem absFin_minor_mul_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (v : Pl F) (X : GL ι (AE F E)) (κ : Matrix ι ι (AE F E))
    (hκ : ∀ i j, absFin F v (compFin F E v (κ i j)) ≤ 1) (f e : Fin n → ι) :
    absFin F v (compFin F E v ((X.1 * κ).submatrix f e).det) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
  have hent : ∀ i j, absFin F v (compFin F E v ((X.1 * κ) i j)) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) := by
    intro i j
    have h1 : compFin F E v ((X.1 * κ) i j) = ((X.1.map (compFin F E v)) * (κ.map (compFin F E v))) i j := by
      rw [← Matrix.map_mul]; rfl
    rw [h1]
    refine (absFin_le_normFin F v _ i j).trans ((normFin_mul_le F v _ _).trans ?_)
    have h2 : normFin F v (κ.map (compFin F E v)) ≤ 1 := (normFin_le_iff F v).2 fun a b => hκ a b
    exact (mul_le_of_le_one_right' h2).trans (le_htOf (normFin F v) (Formalism.UG.bc (compFin F E v) X))
  rw [RingHom.map_det, Matrix.det_apply]
  refine absFin_sum_le F v _ _ fun σ _ => ?_
  have hprod : absFin F v (∏ i : Fin n, ((compFin F E v).mapMatrix ((X.1 * κ).submatrix f e)) (σ i) i)
      ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
    calc _ ≤ ∏ i : Fin n, absFin F v (((compFin F E v).mapMatrix ((X.1 * κ).submatrix f e)) (σ i) i) :=
          Finset.le_prod_of_submultiplicative _ (absFin_one F v).le (absFin_mul_le F v) _ _
      _ ≤ ∏ _i : Fin n, htFin F v (Formalism.UG.bc (compFin F E v) X) :=
          Finset.prod_le_prod' fun i _ => hent _ _
      _ = _ := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hprod
  · rw [h, Units.neg_smul, one_smul, absFin_neg]; exact hprod

end GlobalTheory.CompanionTheory.GodementH
