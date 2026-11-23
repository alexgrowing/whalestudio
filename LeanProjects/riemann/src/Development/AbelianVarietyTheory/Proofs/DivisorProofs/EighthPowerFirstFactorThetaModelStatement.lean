import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFirstFactorThetaModel
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighth_power_first_factor_theta_model : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZHOut ρ M U₀ EE) (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), S.Over₀ M U₀ → OpenAt F β u M U c → ∃ (G : Over M.Z) (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left) (_ : IsCommMonObj G), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e ∧ LBIso (hodge Zh.G S.g) (lbPow (hodge G g) 8) := by
  first | exact @GlobalTheory.SiegFactor.firstFactor | exact GlobalTheory.SiegFactor.firstFactor | (intros; apply GlobalTheory.SiegFactor.firstFactor <;> assumption)
