import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinFunctionalEquation

noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE npow)
open scoped TensorProduct NNReal

namespace GlobalTheory.Published

def SphericalEisensteinConvergence : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (j : ℕ) (hj : j ≤ r) (C D : Matrix (Fin n) (Fin j) E), 0 < j → C = X.submatrix id (Fin.castLE hj) →
        D = Y.submatrix id (Fin.castLE hj) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ≥0,
        (∀ (p : GAd σ J) (b : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * b.1 →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det b)) →
      ∀ g : GAd σ J,
        ((∀ s : ℂ, ((n : ℝ) - j) / 2 < s.re →
          GlobalTheory.Eis.CosetConv (parFlag σ J C fun _ => 0) (ratPts σ J) (fun x => npow (h x) (s + ((n : ℂ) - j) / 2)) g) ∧
        DifferentiableOn ℂ (fun s : ℂ => GlobalTheory.Eis.cosetSum (parFlag σ J C fun _ => 0) (ratPts σ J)
          (fun x => npow (h x) (s + ((n : ℂ) - j) / 2)) g) {s | ((n : ℝ) - j) / 2 < s.re}) ∧
        ∀ w ∈ ratPts σ J, Exchanges σ J C D w → ∀ μ : Measure (unipRad σ J C), μ.IsHaarMeasure →
          (∀ s : ℂ, ((n : ℝ) - j) / 2 < s.re →
            Integrable (fun u : unipRad σ J C => npow (h (w * u * g)) (s + ((n : ℂ) - j) / 2)) μ) ∧
          DifferentiableOn ℂ (fun s : ℂ => ∫ u : unipRad σ J C, npow (h (w * u * g)) (s + ((n : ℂ) - j) / 2) ∂μ)
            {s | ((n : ℝ) - j) / 2 < s.re}

end GlobalTheory.Published

end
