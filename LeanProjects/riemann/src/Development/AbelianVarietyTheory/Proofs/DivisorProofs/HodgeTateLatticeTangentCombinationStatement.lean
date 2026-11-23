import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeTangentCombination
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_lattice_tangent_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (x : Sp C ⟶ X) (w : Sp (DualNumber C) ⟶ t.G.left), IsTanAtG t x w → w ∈ latHT t p x → ∀ (n : ℕ) (a : Fin n → 𝓞 E) (c : Fin n → C), (∀ j, ‖c j‖ ≤ 1) → ∀ W : Sp (DualNumber C) ⟶ t.G.left, IsCombAtG t x (fun j => w ≫ (t.act.act (a j)).left) c W → W ∈ latHT t p x := by
  first | exact @GlobalTheory.HTStable.latHT_comb_act | exact GlobalTheory.HTStable.latHT_comb_act | (intros; apply GlobalTheory.HTStable.latHT_comb_act <;> assumption)
