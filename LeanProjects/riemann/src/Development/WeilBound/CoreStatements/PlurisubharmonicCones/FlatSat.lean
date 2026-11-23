import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

def FlatSat : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L]
    (t' : SAB H (Sp (𝓞 L))) (tB : SAB H (Sp L)) (_ : SABMap tB t' (spMap (algebraMap (𝓞 L) L)))
    (B : HermitianBundle.{0} L) (MB : LieModel t'.G (𝟙 _) B.carrier) (ρM : 𝓞 E →+* Module.End (𝓞 L) B.carrier)
    (s₁ s₂ : 𝓞 E →+* 𝓞 L), IsPrincipal tB → IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB → MB.IsActOf t'.act.act ρM →
    (∃ (ρ : L) (p' q' : ℕ), ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult tB.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult tB.act (spMap g) τ q')) →
    Function.Injective s₁ → (∀ (e : L →+* ℂ) (a : 𝓞 E), e (s₂ a : L) = starRingEnd ℂ (e (s₁ a : L))) →
    |B.normDegree (eigSp ρM s₁) - B.normDegree (eigSp ρM s₂)| ≤
      C * ((B.rank (eigSp ρM s₁) : ℝ) + B.rank (eigSp ρM s₂)) * (1 + Real.log (hostRd E) + |hostLval H|)

end LevelTowerAlt
