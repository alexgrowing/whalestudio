import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes

noncomputable section

namespace GlobalTheory.RowAtOfColLen

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : ℝ) (y : ℚ), RowL i r ρ π w hw Cx x → x ≤ (y : ℝ) → RowAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL Cx.LL)) (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x))) ⇑(TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) y := by
  intro D i r ρ π w hw Cx x y hx hxy
  intro V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 T2 hc2 hm2 V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 T1 hc1 hs1 F hF
  obtain ⟨mm, k, h1, h2, h3⟩ :=
    hx { V := V1, ρ := ρ1, cont := hc1, L := T1 } { V := V2, ρ := ρ2, cont := hc2, L := T2 } F hm2 hs1 hF
  refine ⟨mm, k, h1, h2, ?_⟩
  have h4 : (mm : ℝ) ≤ (y : ℝ) * k := h3.trans (mul_le_mul_of_nonneg_right hxy (Nat.cast_nonneg _))
  exact_mod_cast h4

end GlobalTheory.RowAtOfColLen

end
