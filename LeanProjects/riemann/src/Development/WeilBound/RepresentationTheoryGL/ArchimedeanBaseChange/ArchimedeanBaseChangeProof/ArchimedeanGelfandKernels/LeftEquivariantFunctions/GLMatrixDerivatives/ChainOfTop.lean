import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfKer
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ChainOf

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Top

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc PositivityTheory.RgBcC.LfSt.ChainPf.Ker PositivityTheory.RgBcC.LfSt.ChainPf.Gam

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem dc_of_comm (hA : ActDer) (hI : IBPAct) (hK : KapEquiv) (hKZ : KerZero) (hU : Unimod) (hR : RCalc)
    (hL : LgFacts) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
    {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V} (hC : CxData lam E Fr ε ι S Γ T) [MeasurableSpace (G n)]
    [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V))
    (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (hke : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂)
    (hD : ∀ f ∈ CE E, act μ E k (DC ε Fr f) 1 = DC ε Fr (act μ E k f) 1) :
    ∀ y ∈ GLs n, kapL ε Fr k y = kapR ε Fr k y := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨cL, cR, heq⟩ := hK n lam E Fr ε ι S Γ T hC k hks hke
  have hz := hKZ n μ E (fun y => kapL ε Fr k y - kapR ε Fr k y) (cL.sub cR)
    (fun y hy k₂ => by simp only [(heq y hy k₂).1, (heq y hy k₂).2, sub_mul]) (fun f hf hfc => by
      simp only [ContinuousLinearMap.sub_apply]
      rw [integral_sub (int_of_cpt hL μ _ f cL hf.1.continuousOn hfc) (int_of_cpt hL μ _ f cR hf.1.continuousOn hfc),
        ← kapL_int hA hU hL Fr ε μ k hks hkc f hf.1 hfc, ← kapR_int hI hU hR hL Fr ε μ k hks hkc f hf.1 hfc, hD f hf,
        sub_self])
  exact fun y hy => sub_eq_zero.1 (hz y hy)

end PositivityTheory.RgBcC.LfSt.ChainPf.Top
