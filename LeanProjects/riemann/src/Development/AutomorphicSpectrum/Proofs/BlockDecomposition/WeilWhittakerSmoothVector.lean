import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WinertLin

theorem Wc_sum : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → ∀ (χ : AddChar F Circle), Continuous χ → ∀ (σ : E ≃ₐ[F] E) (lam : ℂ) (c : Eˣ →* ℂˣ) (n : ℕ) (a : Fin n → ℂ) (Ψ : Fin n → E → ℂ), (∀ j, Continuous (Ψ j)) → (∀ j, HasCompactSupport (Ψ j)) → ∀ g : GL (Fin 2) F, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c (fun z => ∑ j, a j * Ψ j z) g = ∑ j, a j * GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c (Ψ j) g := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hfin hcont χ hχ σ lam c n a Ψ hΨc hΨs g
  classical
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI := isModuleTopology F E
  have hN : Continuous (Algebra.norm F : E → F) := continuous_algebraNorm F E
  have hT : Continuous (Algebra.trace F E) := IsModuleTopology.continuous_of_linearMap _
  set μ := selfDualMeasure (GL2LocalData.chE E χ) with hμ
  have hint : ∀ (p q r : F) (t : Eˣ) (j : Fin n), Integrable (fun u : E =>
      (χ ((p * Algebra.norm F (1 : E) + q * Algebra.norm F u - Algebra.trace F E (σ 1 * u)) / r) : ℂ)
        * Ψ j (u * (t : E))) μ := by
    intro p q r t j
    have hcu : Continuous (fun u : E =>
        (χ ((p * Algebra.norm F (1 : E) + q * Algebra.norm F u - Algebra.trace F E (σ 1 * u)) / r) : ℂ)) := by
      have h1 : Continuous (fun u : E => Algebra.trace F E (σ 1 * u)) := by
        simp only [map_one, one_mul]
        exact hT
      have h2 : Continuous (fun u : E =>
          (p * Algebra.norm F (1 : E) + q * Algebra.norm F u - Algebra.trace F E (σ 1 * u)) / r) :=
        ((continuous_const.add (continuous_const.mul hN)).sub h1).div_const r
      exact continuous_subtype_val.comp (hχ.comp h2)
    have hcs : HasCompactSupport (fun u : E => Ψ j (u * (t : E))) :=
      (hΨs j).comp_homeomorph (Homeomorph.mulRight₀ (t : E) t.ne_zero)
    have hcj : Continuous (fun u : E => Ψ j (u * (t : E))) :=
      (hΨc j).comp (continuous_id.mul continuous_const)
    exact (hcu.mul hcj).integrable_of_hasCompactSupport hcs.mul_left
  have key : ∀ (p q r s : F) (t : Eˣ),
      GL2LocalData.rW χ σ μ lam p q r s (fun x => ∑ j, a j * Ψ j (x * (t : E))) 1 =
        ∑ j, a j * GL2LocalData.rW χ σ μ lam p q r s (fun x => Ψ j (x * (t : E))) 1 := by
    intro p q r s t
    unfold GL2LocalData.rW
    split_ifs with hr
    · rw [Finset.mul_sum, Finset.sum_congr rfl]
      intro j _
      ring
    · have : (fun u : E => (χ ((p * Algebra.norm F (1 : E) + s * Algebra.norm F u
            - Algebra.trace F E (σ 1 * u)) / r) : ℂ) * ∑ j, a j * Ψ j (u * (t : E))) =
          fun u => ∑ j, a j * ((χ ((p * Algebra.norm F (1 : E) + s * Algebra.norm F u
            - Algebra.trace F E (σ 1 * u)) / r) : ℂ) * Ψ j (u * (t : E))) := by
        funext u
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, integral_finset_sum _ fun j _ => (hint p s r t j).const_mul (a j),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
      ring
  unfold GL2LocalData.Wc
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · simp only [dif_pos h]
    rw [key, Finset.mul_sum, Finset.sum_congr rfl]
    intro j _
    ring
  · simp [dif_neg h]

end GlobalTheory.CompanionTheory.WinertLin
