import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzLieConditionModuleIffIdealLeKer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzLieConditionModule_iff_ideal_le_ker : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (T : Type) [CommRing T] (f : B →+* T),
    LieMod (matAct M f) D.ω (f (βB b.ρ)) (fun i => (f.comp βB).comp (b.t i)) ↔ lieIdeal b βB M ≤ RingHom.ker f := by
  first | exact @GlobalTheory.UPel.HT.LieLin.lieMod_matAct_iff_lieIdeal_le_ker | exact GlobalTheory.UPel.HT.LieLin.lieMod_matAct_iff_lieIdeal_le_ker | (intros; apply GlobalTheory.UPel.HT.LieLin.lieMod_matAct_iff_lieIdeal_le_ker <;> assumption)
