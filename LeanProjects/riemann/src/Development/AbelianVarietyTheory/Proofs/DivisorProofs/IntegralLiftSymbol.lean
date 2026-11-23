import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDataOfPositivity
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore.IntLift

variable {K : Type} [Field K] [NumberField K]

theorem mulPow_mem_global (G : Geo K) (s : Fin G.D → Fin G.N → K) {a j l : ℕ} (h : j + a = l)
    (α : MonoDeg (Fin G.D) a) {m : G.Sec j} (hm : m ∈ G.global j) : mulPow G s h α m ∈ G.global l := by
  obtain ⟨F, rfl⟩ := hm
  refine ⟨(Vanishing.powChart (isLB_tens G.K.isLB G.isLBA) G.isLB ((Nat.cast_add j a).symm.trans (congrArg _ h))).mul
    (H0.ofSec G.str ⊤ (monoSec (G.sec s) α)) F, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec]
  rfl

end GlobalTheory.HSCore.IntLift

namespace GlobalTheory.HSCore

end GlobalTheory.HSCore
