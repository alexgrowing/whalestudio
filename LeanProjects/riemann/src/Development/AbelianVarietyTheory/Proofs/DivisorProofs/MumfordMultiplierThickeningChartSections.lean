import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaExpansionOfSectionPowerGeThreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierExponentNonzeroSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierOfSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreChartPointMumfordMultiplierNonzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumMult

theorem chart_main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∃ m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, (((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i')), (∀ k : ℕ, 3 ≤ k → ∀ s : H0 U.LG.L k, ∃ F : IntFam (maximalIdeal R) D.toPre (N * k), ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), GlobalTheory.MumMult.ChartExpOn U.toUnifPre e (N * k) i' (((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i') (m e i i' ^ k * ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_left : (((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i') ≤ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom ((((b e).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s.f i))) F.f) ∧ ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ (((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i') := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, hpos, σ₀, x, hx, hσ⟩ := GlobalTheory.T.exists_mumfordMultiplier_exponent_nonzero_section R hB D a a' h h' hE
  obtain ⟨m, hAct, hLead⟩ := GlobalTheory.T.exists_mumfordMultiplier_of_section R hB D A G hG U a a' h h' hE b hb N hN hpos σ₀ x hx hσ
  refine ⟨N, hN, m, fun k hk s => ?_, GlobalTheory.T.exists_closedFibre_chart_point_mumfordMultiplier_nonzero R D A G U b m hLead⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_integralThetaExpansion_of_section_power_ge_three R hB D A G hG U k hk s
  exact hAct k hk f s hf

end GlobalTheory.MumMult
