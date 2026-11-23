import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameExpansionThickeningOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordMultiplierThickeningChartSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformisedStatement
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

namespace GlobalTheory.MumMult

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, 3 ≤ k → ∃ S : H0 U.LG.L k → H0 U.LG.L (N * k), ∃ c : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i'), (∀ (e : ℕ) (s : H0 U.LG.L k) (i i' : Fin 1 → U.LG.L.ι), ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_right : ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i' ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i')).op).hom (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((S s).f i')) = c e i i' * ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_left : ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i' ≤ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom ((((b e).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s.f i))) ∧ ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (c 0 i i') := by
  have hA := GlobalTheory.T.mumfordMultiplier_thickening_chart_sections
  have hU := GlobalTheory.T.eq_of_same_expansion_thickening_open
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, m, hm, y, hy1, hy2⟩ := hA R hB D A G hG U a a' h h' hE b hb
  refine ⟨N, hN, fun k hk => ?_⟩
  choose F hF using hm k hk
  have hNk : 1 ≤ N * k := Nat.mul_pos hN (by omega)
  choose σ hσ using fun s => GlobalTheory.T.exists_expandsAt_section_uniformised R hB D A G U hG (N * k) hNk (F s)
  refine ⟨σ, fun e i i' => m e i i' ^ k, fun e s i i' => ?_, y, hy1, fun i i' hyW => ?_⟩
  · exact hU R _ D A G U.toUnifPre e (N * k) (σ s) (F s).f i' _ inf_le_right _ (hσ s e) (hF s e i i')
  · show y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i' ^ k)
    have hk0 : 0 < k := by omega
    first
      | (rw [Scheme.basicOpen_pow _ _ hk0]; exact hy2 i i' hyW)
      | (rw [Scheme.basicOpen_pow _ hk0]; exact hy2 i i' hyW)
      | (rw [Scheme.basicOpen_pow _ _ _ hk0]; exact hy2 i i' hyW)
      | (simpa [Scheme.basicOpen_pow, hk0] using hy2 i i' hyW)

end GlobalTheory.MumMult
