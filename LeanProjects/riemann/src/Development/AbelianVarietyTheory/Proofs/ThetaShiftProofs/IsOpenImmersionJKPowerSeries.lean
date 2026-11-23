import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys

noncomputable section

namespace GlobalTheory.ThetaShiftProofs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem isOpenImmersion_jK_powerSeries (k : Type) [Field k] : IsOpenImmersion (Out.jK (PowerSeries k)) := by
  have hX : Irreducible (PowerSeries.X : PowerSeries k) := PowerSeries.X_irreducible
  have : IsLocalization.Away (PowerSeries.X : PowerSeries k) (FractionRing (PowerSeries k)) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers (PowerSeries.X : PowerSeries k))
      (nonZeroDivisors (PowerSeries k)) (powers_le_nonZeroDivisors_of_noZeroDivisors hX.ne_zero)
      fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hX
    exact ⟨PowerSeries.X ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization (PowerSeries.X : PowerSeries k)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem j_mem_abLocus {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (p : Xo.XF c) :
    Y.j p ∈ abLocus Y.t.G := by
  have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨_, rfl⟩
  simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using hz

theorem mono_j {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (hm : Mono (spMap β)) : Mono Y.j := by
  have := Y.jQ_open
  unfold Model.j; infer_instance

theorem j_over {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  unfold Model.j
  rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

end GlobalTheory.ThetaShiftProofs
