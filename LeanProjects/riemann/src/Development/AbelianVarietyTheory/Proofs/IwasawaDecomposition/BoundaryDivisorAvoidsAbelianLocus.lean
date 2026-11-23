import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem jQ_not_mem_support_comap_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (n : ℕ),
    (∀ x ∈ BY.idealSheaf.support, x ∉ abLocus Y.t.G) → ∀ z, Y.jQ z ∉ ((BY.idealSheaf ^ n).comap (genι Y)).support := by
  intro E _ _ _ H D l Xo c Y BY n hB z hz
  rw [Scheme.IdealSheafData.support_comap] at hz
  have hz' : genι Y (Y.jQ z) ∈ (BY.idealSheaf ^ n).support := hz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top] at hz'
    exact hz'
  · rw [Scheme.IdealSheafData.support_pow _ _ hn.ne'] at hz'
    refine hB _ hz' ?_
    have h : Y.jQ z ∈ pullback.fst Y.s (spMap (RingHom.id c.F)) ⁻¹' abLocus Y.t.G := Y.ab_gen ▸ Set.mem_range_self _
    exact h

end GlobalTheory.TorRef
