import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
open NumberField IsDedekindDomain

namespace GlobalTheory.CuspRep.AeFix

theorem eventually_mem_fixed : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (x : π.V), ∀ᶠ v in Filter.cofinite, x ∈ GlobalTheory.PRep.fixed (π.locRep v) (GlobalTheory.LFun.KGL v a) := by
  intro E _ _ _ a π x
  filter_upwards [GlobalTheory.CuspRep.LocSph.eventually_mem ((π.cusp x.1 x.2).1.level.mem_nhds (by simp))] with w hw
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ?_
  obtain ⟨g, rfl⟩ := hk
  exact hw g

end GlobalTheory.CuspRep.AeFix
