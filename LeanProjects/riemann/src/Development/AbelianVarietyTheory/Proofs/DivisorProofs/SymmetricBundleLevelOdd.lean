import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFreeOfFiniteProjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_bundle_level_odd : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (β₀ : cycAway M →+* k) (z₀ : kˣ), x₀ ≫ t = spMap β₀ → (z₀ : k) = β₀ (zetaAway M) → (∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x₀) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z₀ ^ (2 * omegaStd a b)))) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S) (β : cycAway M →+* k') (z : k'ˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k') = β (zetaAway M) → ∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b))) := by
  first | (exact @GlobalTheory.WeilOpenLocus.weil_open) | (exact GlobalTheory.WeilOpenLocus.weil_open) | (intros; apply GlobalTheory.WeilOpenLocus.weil_open  <;> assumption)
