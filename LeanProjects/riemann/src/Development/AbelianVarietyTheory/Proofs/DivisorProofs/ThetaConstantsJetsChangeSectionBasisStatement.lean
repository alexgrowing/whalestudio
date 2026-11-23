import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_jets_change_section_basis : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (hp rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → ∀ (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ P.A)) (ϑ ϑ' : I → K) (J J' : I → Fin P.g → K), ThJet ⟨P, hp, rig, hr, th, hth, v, hv⟩ rfl m pt ϑ J → ThJet ⟨P, hp, rig, hr, th', hth', v', hv'⟩ rfl m pt ϑ' J' → (∀ i, ϑ' i = a * ϑ i) ∧ ∃ c : Fin P.g → K, ∀ i j, J' i j = a * ∑ l, M j l * J i l + c j * ϑ i := by
  first | exact @GlobalTheory.MBLow.JetUniq.thJet_change | exact GlobalTheory.MBLow.JetUniq.thJet_change | (intros; apply GlobalTheory.MBLow.JetUniq.thJet_change <;> assumption)
