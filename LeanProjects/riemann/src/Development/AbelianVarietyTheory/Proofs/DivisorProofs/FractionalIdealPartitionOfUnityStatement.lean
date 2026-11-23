import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealPartitionOfUnity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractional_ideal_partition_of_unity : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F), ∃ (n : ℕ) (d : Fin n → 𝔠.elt) (a : Fin n → 𝓞 F),
    (∀ j (e : 𝔠.elt), ∃ b : 𝓞 F, a j • e = b • d j) ∧ ∑ j, a j = 1 := by
  first | exact @GlobalTheory.PartitionFracId.exists_partition | exact GlobalTheory.PartitionFracId.exists_partition | (intros; apply GlobalTheory.PartitionFracId.exists_partition <;> assumption)
