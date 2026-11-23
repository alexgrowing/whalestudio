import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentSecondDifferenceConstantMembers
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameExponent_second_difference_constant_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ c : X₁.S.Gam → X₁.S.Gam → ZMod ((X₁.S.r * X₁.S.N) ^ 2), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (E : X₁.S.Gam → ℕ), (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ (E a)) → ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ b ∈ X₁.S.HH X₁.M z₁, ((E (a + b) : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E b : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) + ((E 0 : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = c a b := by
  first | exact @GlobalTheory.GSep.FrExpCube.frExp_second_diff | exact GlobalTheory.GSep.FrExpCube.frExp_second_diff | (intros; apply GlobalTheory.GSep.FrExpCube.frExp_second_diff <;> assumption)
