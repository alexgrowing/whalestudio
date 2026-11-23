import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapComp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineCombinationInChart_specMap_comp : ∀ (Y : Scheme.{0}) (V : Y.Opens) (S S' : Type) [CommRing S] [CommRing S'] (g : S →+* S') (ι : Type) [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), GlobalTheory.SecGlue.IsCombIn V u c w a →
    GlobalTheory.SecGlue.IsCombIn V (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  first | exact @GlobalTheory.SecGlue.isCombIn_spMap_comp | exact GlobalTheory.SecGlue.isCombIn_spMap_comp | (intros; apply GlobalTheory.SecGlue.isCombIn_spMap_comp <;> assumption)
