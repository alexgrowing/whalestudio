import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FlatAndSurjectiveOfSurjectivePoints
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SurjHomFlat

open GlobalTheory GlobalTheory.SurjIsogeny GlobalTheory.IsogenyModel

theorem finite_flat :
    ∀ (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (g : ℕ), IsAbelianScheme A → IsAbelianScheme X →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g X.hom →
    ∀ (ψ : A ⟶ X) [IsMonHom ψ] [Surjective ψ.left], IsFinite ψ.left ∧ Flat ψ.left := by
  intro A X _ _ g hA hX hgA hgX ψ _ _
  have := hX.proper
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ X.hom hX.smooth
    hX.geomConnected
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProper (ψ.left ≫ X.hom) := by rw [Over.w]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left X.hom
  have hA' : SmoothOfRelativeDimension g (ψ.left ≫ X.hom) := by rw [Over.w]; exact hgA
  obtain ⟨a, ha⟩ := ψ.left.surjective (genericPoint X.left)
  have : LocallyQuasiFinite ψ.left := by
    refine locallyQuasiFinite_of_finite_fibre ψ a ((Set.finite_singleton (genericPoint _)).subset ?_)
    intro x hx
    exact eq_genericPoint_of_apply_eq ψ.left X.hom hgX hA' (ha ▸ hx)
  have hf : IsFinite ψ.left := .of_isProper_of_locallyQuasiFinite _
  refine ⟨hf, ?_⟩
  exact GlobalTheory.SS.flat_of_isDominant_grpHom ℂ A X ψ

end GlobalTheory.SurjHomFlat
