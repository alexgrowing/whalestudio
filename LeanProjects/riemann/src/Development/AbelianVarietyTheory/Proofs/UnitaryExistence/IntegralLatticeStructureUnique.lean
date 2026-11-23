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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnitStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValVEqOneIntegralGeneratorsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_sabMap_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} (T : CDVR) {x x' : Sp T.Fr ⟶ Xo.X} (hx : x' = x) (G G₂ : SAB H (Sp T.V))
    (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t₂ Xo.univ.t x') (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) :
    ∃ (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), k.φ ≫ n₁.φ = m₁.φ ∧ m₂.φ ≫ n.φ = k.φ ≫ n₂.φ := by
  subst hx
  exact GlobalTheory.T.semiAbelian_dvr_extensions_iso_compatible E H Dw l Xo T.V T.Fr x' G G₂ t t₂ m₁ m₂ n₁ n₂

theorem intLatU_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntLatU Xo c := by
  intro E _ _ _ H Dw l Xo c T io y y'
  let := io.toAlgebra
  intro hx
  obtain ⟨G, t, m₁, m₂, ⟨ub, hub⟩, θ, hθ⟩ := y.2.2
  obtain ⟨G₂, t₂, n₁, n₂, ⟨ub₂, hub₂⟩, θ₂, hθ₂⟩ := y'.2.2
  obtain ⟨k, n, hk, hn⟩ := exists_sabMap_of_eq T hx G G₂ t t₂ m₁ m₂ n₁ n₂
  refine ⟨GlobalTheory.T.integral_frames_differ_by_unit' E H Dw l Xo c T io y.1 y'.1 G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn ub ub₂ hub hub₂, ?_⟩
  intro a pm h1 h2 h3
  refine GlobalTheory.T.valV_eq_one_integral_generators E H Dw l Xo c T io y.1 y'.1 G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn θ θ₂ hθ hθ₂ a
    ⟨pm, h1, ?_, h3⟩
  have hid : spMap (RingHom.id T.Fr) = 𝟙 (Sp T.Fr) := Spec.map_id _
  rw [h2, hid]
  exact (Category.comp_id _).symm

end GlobalTheory.Frames
