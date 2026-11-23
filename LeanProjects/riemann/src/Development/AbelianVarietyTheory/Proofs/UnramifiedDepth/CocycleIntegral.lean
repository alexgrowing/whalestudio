import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffAddFirstSecond

noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.GaugeCocycle

open MvPowerSeries

variable {C : Type} [Field C]

def valRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

theorem intS_iff_ig (V : VF C) {σ : Type} (f : MvPowerSeries σ C) : IntS V f ↔ f ∈ Ig (valRing V) C σ := by
  constructor
  · intro hf
    let g : MvPowerSeries σ (valRing V) := fun n => ⟨coeff n f, hf n⟩
    refine RingHom.mem_range.2 ⟨g, ?_⟩
    ext n
    rw [coeff_map]
    rfl
  · intro hf n
    obtain ⟨g, rfl⟩ := RingHom.mem_range.1 hf
    rw [coeff_map]
    exact (coeff n g).2

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {d : ℕ}

omit [CharZero C] in
theorem map_self {σ : Type} (f : MvPowerSeries σ C) : MvPowerSeries.map (algebraMap C C) f = f := by
  ext n
  rw [coeff_map]
  rfl

end GlobalTheory.GaugeCocycle
