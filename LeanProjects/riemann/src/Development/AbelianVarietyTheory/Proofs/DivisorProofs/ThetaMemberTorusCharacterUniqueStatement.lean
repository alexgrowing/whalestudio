import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusCharacterUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigTorsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsDividingGroupLabelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelKilledCharOfTorusLabelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
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
theorem _root_.GlobalTheory.T.thetaMember_torus_character_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (τ : X₁.S.Gam) (χ χ' : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ → GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ' → χ = χ' := by
  first | exact @GlobalTheory.GSep.TorCharUnique.torChar_unique | exact GlobalTheory.GSep.TorCharUnique.torChar_unique | (intros; apply GlobalTheory.GSep.TorCharUnique.torChar_unique <;> assumption)
