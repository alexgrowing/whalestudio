import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullRegCoverIsCInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModifFlag
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.FlagModelExists

theorem nonempty_flagModel : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X],
    (∀ (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q)) →
    IsArithVar p 1 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r), h.IsCInfNorm →
      Nonempty h.FlagModel := by
  intro k _ X p _ hreg hp E r h hN
  obtain ⟨Y, ρ, hY, g, ⟨fl⟩⟩ := exists_modif_flag r k X p E hp h.isVB
  haveI := hY.isIntegral
  obtain ⟨C⟩ := hreg Y (ρ ≫ p) hY
  obtain ⟨a, b⟩ := g
  let D : RegCover p :=
    { Y := C.Y
      ρ := C.ρ ≫ ρ
      reg := by rw [Category.assoc]; exact C.reg
      generic := by
        show (C.ρ ≫ ρ) (genericPoint C.Y) = genericPoint X
        rw [Scheme.Hom.comp_apply, C.generic, a]
      finite := by
        show (C.ρ ≫ ρ).residueDegree (genericPoint C.Y) ≠ 0
        rw [CurveDegreesCompare.residueDegree_comp, C.generic]
        exact mul_ne_zero b C.finite }
  obtain ⟨fl'⟩ := flag_pullback _ _ C.ρ _ r fl
  exact ⟨⟨D, GlobalTheory.VMetric.pull_regCover_isCInf k X p E r h hN D, fl'.ofIso ((Scheme.Modules.pullbackComp C.ρ ρ).app E)⟩⟩

end GlobalTheory.FlagModelExists
