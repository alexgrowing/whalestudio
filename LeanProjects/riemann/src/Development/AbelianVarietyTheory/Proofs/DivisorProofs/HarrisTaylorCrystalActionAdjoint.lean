import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem crysAct_adjoint : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (c : D.O) x y, φ (GlobalTheory.HTCount.crysAct o₀ c x) y = φ x (GlobalTheory.HTCount.crysAct o₀ (D.star c).unop y) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ hφ c x y
  haveI := o₀.act.hom c
  haveI := o₀.act.hom (D.star c).unop
  have hA := o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k o₀.A hA
  have C := GlobalTheory.AbDual.cupSquare_of_free GlobalTheory.abelianDeRham.1
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA) (GlobalTheory.AbDual.smooth_prod hg hg)
  have e := GlobalTheory.AbDual.IsCorrForm.adjoint C o₀.isLB o₀.isLB hφ hφ (o₀.act.act c) (o₀.act.act (D.star c).unop)
    (LBIso.symm (o₀.rosati c)) x y
  rw [GlobalTheory.HTCount.crysAct_apply, GlobalTheory.HTCount.crysAct_apply]
  exact e.symm

end GlobalTheory.HTCount
