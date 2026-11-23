import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.LinSys

variable {k : Type} [Field k] (S : LinSys k)

def secGerm (y : S.Y) (s : S.L.Sec) : S.Y.presheaf.stalk y :=
  S.Y.presheaf.germ _ y (S.mem_chartAt y) (s.f (S.chartAt y))

def CrossNormallyAt {M : ℕ} (s : Fin M → S.L.Sec) (y : S.Y) : Prop :=
  LinearIndependent (IsLocalRing.ResidueField (S.Y.presheaf.stalk y))
    (fun j : {j : Fin M // S.secGerm y (s j) ∈ IsLocalRing.maximalIdeal (S.Y.presheaf.stalk y)} =>
      ((IsLocalRing.maximalIdeal (S.Y.presheaf.stalk y)).toCotangent ⟨_, j.2⟩ :
        IsLocalRing.CotangentSpace (S.Y.presheaf.stalk y)))

end GlobalTheory.Adelic.LinSys
