import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniversalFrameTestRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesFramedPointsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFactorOpenImmersion

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem framedPoint_field_fromTest :
    Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
      (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), SpreadSt Xo c := by
  intro hB E _ _ _ H Dw l Xo c S _ _ y
  let xF : Sp S ⟶ Xo.XF c := pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])
  have h1 : xF ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  have h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _
  let q : Sp S := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S)
  obtain ⟨p, j, y₀, hj, hq⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hB E H Dw l Xo c (xF q)
  obtain ⟨g, hg, hfac⟩ := openChart_factor_near_prime E H Dw l Xo c p.R j y₀ hj S xF h2 q hq
  have hg0 : g ≠ 0 := fun h => hg (h ▸ Ideal.zero_mem _)
  obtain ⟨ψ, hψ⟩ := hfac S (AlgHom.id c.F S) (Ne.isUnit hg0)
  have hid : spMap (AlgHom.id c.F S).toRingHom = 𝟙 (Sp S) := Spec.map_id _
  rw [hid, Category.id_comp] at hψ
  have hx : y.x = spMap ψ.toRingHom ≫ y₀.x := by
    rw [← h1, hψ, Category.assoc, hj.2.1]
  obtain ⟨A, π, X, s, u, hu⟩ := GlobalTheory.T.exists_universalFrame_testRing hB E H Dw l Xo c p y₀
  obtain ⟨a, ⟨-, ha⟩, -⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hB E H Dw l Xo c p.R A.R y₀ π X s u hu S y ψ hx
  exact ⟨A, a, u, ha⟩

end GlobalTheory.Frames
