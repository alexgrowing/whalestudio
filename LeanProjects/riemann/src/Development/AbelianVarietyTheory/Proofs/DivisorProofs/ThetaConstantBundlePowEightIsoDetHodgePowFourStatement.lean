import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantBundlePowEightIsoDetHodgePowFour
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstantBundle_pow_eight_iso_detHodge_pow_four : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), 1 ≤ S.g → S.Over₀ M U₀ → IsOpen (abLocus Zh.G) → ∀ (δ : LB M.Z) (t : S.Gam → δ.Sec), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → ZM.SecCoord δ t M.pt S.th → LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge Zh.G S.g) 4) := by
  first | exact @GlobalTheory.KeyZh.key_zh | exact GlobalTheory.KeyZh.key_zh | (intros; apply GlobalTheory.KeyZh.key_zh <;> assumption)
