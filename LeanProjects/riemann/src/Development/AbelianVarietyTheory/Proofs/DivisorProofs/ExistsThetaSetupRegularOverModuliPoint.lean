import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemGenericPointsMemClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.SetupAt

theorem exists_generic_specializes {X : Scheme.{0}} (x : X) : ∃ η ∈ genericPoints X, η ⤳ x := by
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  refine ⟨hirr.genericPoint, ?_, ?_⟩
  · show closure {hirr.genericPoint} ∈ irreducibleComponents X
    rw [hirr.isGenericPoint_genericPoint_closure.def, hcl.closure_eq]
    exact irreducibleComponent_mem_irreducibleComponents x
  · rw [specializes_iff_mem_closure, hirr.isGenericPoint_genericPoint_closure.def, hcl.closure_eq]
    exact mem_irreducibleComponent

theorem exists_uSetup_regular_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x : Xo.XF c), ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w :=
  GlobalTheory.UPoinc.exists_uSetup_regular_at

end GlobalTheory.UPoinc.SetupAt
