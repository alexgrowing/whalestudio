import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedThetaSectionNonzeroEveryFibre
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glued_thetaSection_nonzero_every_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (δ : LB M.Z) (t : S.Gam → δ.Sec), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → ZM.SecCoord δ t M.pt S.th → (∀ a, ∀ z ∈ nonzeroLocus (t a), a ∈ S.supI M z) → ∃ σ : (CechPic.tens Zh.L.L (δ.pull Zh.G.hom)).Sec, NzFib σ := by
  first | exact @GlobalTheory.KeyTheta.exists_nzFib | exact GlobalTheory.KeyTheta.exists_nzFib | (intros; apply GlobalTheory.KeyTheta.exists_nzFib <;> assumption)
