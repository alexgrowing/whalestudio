import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem isNef_pull : GlobalTheory.Published.ArCalc → SemiPull → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E →
    ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.IsNef D → (L.pull π hπ).IsNef E := by
  intro hA hS k _ X Y _ _ p q D E hX hY π hπ L hN
  obtain ⟨h, hh⟩ := ((hA.arExists k X p D hX).1 L)
  obtain ⟨h', hh'⟩ := ((hA.arExists k Y q E hY).1 (L.pull π hπ))
  have hL := (hh.isNef_iff hX).1 hN
  refine (hh'.isNef_iff hY).2 ⟨hS k X Y p q D E hX hY π hπ L hN.semiPos, fun Z i _ _ hd => ?_⟩
  rw [GlobalTheory.MixHt.heightProj k X Y p q D E hX hY π hπ L h h' hh hh' (i (genericPoint Z))]
  by_cases h0 : π.residueDegree (i (genericPoint Z)) = 0
  · simp [h0]
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  have hAY := GlobalTheory.MixHt.isAmb_of_isArithVar hY
  have hAX := GlobalTheory.MixHt.isAmb_of_isArithVar hX
  obtain ⟨-, -, -, -, hcl, hgd⟩ := GlobalTheory.MixHt.hasDim_basic k Y q hAY
  obtain ⟨⟨m', hm'⟩, -, -, -, hcl', hgd'⟩ := GlobalTheory.MixHt.hasDim_basic k X p hAX
  have hy : GlobalTheory.MixHt.HasDim (i (genericPoint Z)) 1 := (hcl Z i _ 1).2 ((hgd Z 1).2 (by exact_mod_cast hd))
  obtain ⟨d', -, hd'⟩ := hm' (π (i (genericPoint Z)))
  obtain ⟨-, hiff⟩ := GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ _ 1 d' hy hd'
  have e1 : 1 = d' := hiff.1 h0
  subst e1
  obtain ⟨W, j, _, _, hj⟩ := exists_isClosedImmersion_genericPoint (π (i (genericPoint Z)))
  have hW : topologicalKrullDim W = (1 : ℕ) := (hgd' W 1).1 ((hcl' W j _ 1).1 (hj ▸ hd'))
  have := hL.2 W j (by exact_mod_cast hW)
  rwa [hj] at this

end GlobalTheory.HSNef
