import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsSeparatedOfProj
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

theorem UpperTheory.complexPoint_eval_pullback_section :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z) (h : c ≫ s = s') (V : Z.Opens) (f : Γ(Z, V)) (y : CxPts s' (RingHom.id ℂ)), y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c ⁻¹ᵁ V) → CxPts.ev s' (RingHom.id ℂ) (c ⁻¹ᵁ V) ((c.app V).hom f) y = CxPts.ev s (RingHom.id ℂ) V f (UpperTheory.A.zpt c h y) := by
  intro Z Y s s' c h V f y _
  exact (GlobalTheory.Points.valR_comp y.1 c V f).symm
