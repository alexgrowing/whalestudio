import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem MuVal.eq_one_of_fixed {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ}
    (h : MuVal V χ mu) (y : (AE D)ˣ)
    (hy : sigR (AF D.host.F) D.sp.cm.sig (y : AE D) = y) : χ y = 1 := by
  obtain ⟨x, hx⟩ := h.1 1
  have hxy : IsDetRoot V 1 (x * y) := by
    unfold IsDetRoot at hx ⊢
    rw [Units.val_mul, map_mul, hy, ← mul_assoc, ← hx]
  have e2 := h.2 1 (x * y) hxy
  rw [h.2 1 x hx, map_mul] at e2
  have e3 : χ x * 1 = χ x * χ y := by
    apply Subtype.ext
    simpa [Circle.coe_mul] using e2
  exact (mul_left_cancel e3).symm

end Formalism.L2.Pj
