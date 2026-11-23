import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHodgeWt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.GenInterior

theorem exists_j₀_eq_genericPoint (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] :
    ∃ v : V₀ TF.Y Z, j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  obtain ⟨x, hx⟩ := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).nonempty
  have hxm : TF.Y.j x ∈ barComp TF.Y Z := (j_mem_barComp Z x).2 hx
  let v : V₀ TF.Y Z := ⟨x, hxm⟩
  have hU : IsOpen (Set.range (j₀ TF.Y Z)) := (j₀ TF.Y Z).isOpenEmbedding.isOpen_range
  exact ((genericPoint_spec (X₀ TF.Y Z)).mem_open_set_iff hU).2 ⟨j₀ TF.Y Z v, trivial, v, rfl⟩

end GlobalTheory.GenInterior
