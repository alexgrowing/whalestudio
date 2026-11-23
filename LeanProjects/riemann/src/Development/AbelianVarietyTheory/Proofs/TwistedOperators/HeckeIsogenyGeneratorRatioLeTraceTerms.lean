import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodicThetaNormMeanFactorLeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioPointwiseBoundStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

namespace GlobalTheory.HeckeEx

theorem cabs_gen_le_of_hkPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → cabs (t none : CAt σ) ≤ (Ideal.absNorm P : ℝ) ^ i := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU P p i k k' x x' C z t hA hC hz hb hx hx'
  obtain ⟨g, Λ, Λ', Fd, Fd', h, u, u', v, c1, c2, f1, f2, hh, u0, u0', up, up', m1, m1', hpt⟩ :=
    GlobalTheory.T.heckeIsogeny_generatorRatio_pointwise_bound E H Dw l Xo c σ r U hσ hU P p i k k' x x' C z t hA hC hz hb hx hx'
  exact_mod_cast GlobalTheory.T.periodic_theta_norm_mean_factor_le g Λ Λ' Fd Fd' h u u' p _ v _ c1 c2 f1 f2 hA.2.2.1.pos hh u0 u0' up up' m1 m1' hpt

end GlobalTheory.HeckeEx
