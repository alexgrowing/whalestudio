import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSurjectivePullbackNef
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VertForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_of_surjective_pullback_nef : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), Function.Surjective π → ∀ (L : HermLB p) (l : ℕ), l.Prime → NefOver (L.pull π hπ) l → NefOver L l := by
  first | exact @GlobalTheory.NefDescent.nefOver_of_pull | exact GlobalTheory.NefDescent.nefOver_of_pull | (intros; apply GlobalTheory.NefDescent.nefOver_of_pull <;> assumption)
