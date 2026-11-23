import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseOfFlagCpt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieFramesSmoothHermitianOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieGramIsGoodMumfordStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernIntegralEqCovolumeMulFlagDegreeStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem GlobalTheory.LieBase.exists_goodBase : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F]
    (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)),
    Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp),
      ∃ (X : Var F) (Eb : Fr (ratOf X) Dw.mult 0) (E' : Fr (ratOf (Φ.C k).Y) Dw.mult Dw.mult)
        (φ : X.Fn →ₐ[F] (Φ.C k).Y.Fn) (f : (Φ.C k).Y.X ⟶ X.X) (Ob : X.X.Opens)
        (Hm : Mat Dw.mult X.Fn → GlobalTheory.CxPts X.str (σ.comp e.toRingHom) → Mat Dw.mult ℂ),
        Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => (Φ.C k).gr x.1 x.2) ∧ IsMetricOn Eb Ob Hm ∧
          IsGood Eb Ob Hm ∧
          ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ),
            antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^
                (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult →
              HasChernIntegral Eb Ob Hm R
                (GlobalTheory.TrueCx.covol (U.X k) * Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k
  obtain ⟨X, j, f, f₀, Eb, A₀, E', φ, hj, hB, hR, hG⟩ := GlobalTheory.LieBase.exists_base_of_flagCpt E H Dw l Xo c O β Y T F e σ U hσ hU Φ k
  refine ⟨X, Eb, E', φ, f, openPart j, lieGram e U hj f₀ A₀, hR, hG,
    GlobalTheory.LieBase.isMetricOn_lieGram E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hB,
    GlobalTheory.T.hodgeMetric_lieGram_isGood_mumford E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hB,
    fun la R h => ?_⟩
  convert GlobalTheory.T.hodgeMetric_chernIntegral_eq_covolume_mul_flagDegree E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hB la R h using 3
