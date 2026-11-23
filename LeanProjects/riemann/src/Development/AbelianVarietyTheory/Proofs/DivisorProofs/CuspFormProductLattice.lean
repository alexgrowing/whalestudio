import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem cusp_mul : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (a b : AllWt.Weight (T.Q.Dw j)) (w : Cusp Z Y.U a) (f : Cusp Z Y.U b), GlobalTheory.CovTop.Hypotheses₂ → ∃ g : Cusp Z Y.U (a + b), g.1 = w.1 * f.1 ∧ (w ∈ latOn Y.U Z _ → f ∈ latOn Y.U Z _ → g ∈ latOn Y.U Z _) := by
  intro D T j Y e o _ _ Z a b w f _
  have hm : w.1 * f.1 ∈ Cusp Z Y.U (a + b) := by
    show w.1 * f.1 ∈ cuspOn Y.U Z (wtOf _ (a + b) 0)
    have h := GlobalTheory.AllWt.wtOf_add (Dw := T.Q.Dw j) a b 0 0
    rw [add_zero] at h
    rw [h]
    refine ⟨GlobalTheory.SlopeRec.mul_mem_cuspW ⟨0, by simp [GlobalTheory.AllWt.wtOf_snd]⟩ ⟨0, by simp [GlobalTheory.AllWt.wtOf_snd]⟩ w.2.1 f.2.1,
      GlobalTheory.AllWt.mul_mem_suppOn _ f.2.2⟩
  exact ⟨⟨_, hm⟩, rfl, fun hw hf => GlobalTheory.AllWt.mul_mem_supLat hw hf hm⟩

end GlobalTheory.HSApp
