import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.FullExtend

theorem main : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (K K' : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K'] (f : K →+* K') (o : Full D K), ∃ o' : Full D K', FullExt f o o' ∧ (∀ m v, o.Theta m v → o'.Theta m fun x => f (v x)) ∧ ∀ m j z v, 0 < j → o.Coord m (o.I.ev j z) v → o'.Coord m (o'.I.ev j z) fun x => f (v x) := by
  intro hV _ _ _ _ _ _ E _ _ _ H D K K' _ _ _ _ _ f o
  obtain ⟨o', h₁, h₂, h₃⟩ := exists_fullExt hV.1.1 D f o
  exact ⟨o', h₁, h₂, fun m j z v _ => h₃ m j z v⟩

end GlobalTheory.FullExtend
