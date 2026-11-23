import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.OrbitCptW

theorem orbit_cpt_w : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (N : GLw n w), N.val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ x : GLw n w, x⁻¹ * N * x ∈ C → ∃ z : GLw n w, z * N = N * z ∧ ∃ d ∈ D, x = z * d := by
  intro E _ _ _ _ n w N hN C hC
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  obtain ⟨C', hC', hC'g⟩ := GlobalTheory.OrbCpt.gl_orbit_cpt (k := w.adicCompletion E) N.val hN
    ((fun y : GLw n w => (y : Matrix (Fin n) (Fin n) (w.adicCompletion E))) '' C)
    (hC.image Units.continuous_val)
  refine ⟨(fun y => y⁻¹) '' C', hC'.image continuous_inv, fun x hx => ?_⟩
  obtain ⟨c, hc, t, ht, hxt⟩ := hC'g x⁻¹ ⟨_, hx, by simp [mul_assoc]⟩
  refine ⟨t⁻¹, ?_, c⁻¹, ⟨c, hc, rfl⟩, ?_⟩
  · have h1 : t * N = N * t := Units.ext ht
    calc t⁻¹ * N = t⁻¹ * (N * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * N) * t⁻¹ := by rw [h1]
      _ = N * t⁻¹ := by group
  · rw [← _root_.mul_inv_rev, ← hxt, inv_inv]

end GlobalTheory.OrbitCptW
