import Formalism.LocalToGlobal.ProjectiveLattices.PerFrLact

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem eq_zero_of_trace_int {z : E} (h : ∀ c : 𝓞 E, Algebra.trace ℚ E ((c : E) * z) = 0) : z = 0 := by
  refine (traceForm_nondegenerate ℚ E).1 z fun n => ?_
  rw [Algebra.traceForm_apply, ← (integralBasis E).sum_repr n, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_smul_comm, map_smul, integralBasis_apply, mul_comm z]
  have := h (RingOfIntegers.basis E i)
  rw [RingOfIntegers.coe_eq_algebraMap] at this
  rw [this, smul_zero]

theorem smul_coord (x : 𝓞 E) (w : Fin r → E) (a : Fin r) : (x • w) a = (x : E) * w a := by
  simp [Algebra.smul_def]

end Lat

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u w : Fin r → E) :
    herm G (c • u) w = (c : E) * herm G u w := by
  simp only [herm, smul_coord, Finset.mul_sum, mul_assoc]

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u w : Fin r → E) :
    herm G u (c • w) = cc (c : E) * herm G u w := by
  simp only [herm, smul_coord, Finset.mul_sum, cc, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem herm_mulVec_smul (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u : Fin r → E) :
    γ *ᵥ (c • u) = c • (γ *ᵥ u) := Matrix.mulVec_smul γ c u

end Herm

section Gam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {r : ℕ}

end Gam

end Formalism.L2.Pj
