import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsometryTorsionEqLevelSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateIsometry_torsion_eq_level_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (T : TateIso Dw k Q act e) (eta : Dw.La → Q) (I : Ideal (𝓞 E)) (g : ℕ), (∀ a b x, act (a + b) x = act a x * act b x) → (∀ x, act 1 x = x) → (∀ (n : ℕ) x, act (n : 𝓞 E) x = x ^ n) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), eta a = T.ev l.M a) → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → l.Mb ≤ I → ∃ t : 𝓞 E, (∀ c ∈ I • (⊤ : Submodule (𝓞 E) Dw.La), t • c ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ ∀ x : Q, (∀ a ∈ I, act a x = 1) → ∃ c : Dw.La, x = eta (t • c) := by
  first | exact @GlobalTheory.TateTorsion.torsion_eq_level_smul | exact GlobalTheory.TateTorsion.torsion_eq_level_smul | (intros; apply GlobalTheory.TateTorsion.torsion_eq_level_smul <;> assumption)
