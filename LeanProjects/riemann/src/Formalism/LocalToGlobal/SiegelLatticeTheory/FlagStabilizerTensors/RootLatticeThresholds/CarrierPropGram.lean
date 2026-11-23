import Mathlib
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.HermitianCurvature.StatementTop

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Carrier

theorem propGram_of_vtTensor {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hB : Formalism.FourierDecayAlt.D.IsBuilt S T f χ ν' m₀ top A₀)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : Formalism.FourierDecayAlt.TB.Pt E → H)
    (hVt : Formalism.FourierDecayAlt.JCT.VtTensor S T f ν' m₀ Vt) : Formalism.FourierDecayAlt.C.PropGram S Vt := by
  exact Formalism.FourierDecayAlt.Final.jc_propGramOfPlaces E Wp Wq S
    _ (fun v => Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v) H Vt hVt
    (Formalism.FourierDecayAlt.Final.jc_gramPlaceBuilt Formalism.FourierDecayAlt.Final.d_ptPermSpec Formalism.FourierDecayAlt.Final.d_ptGSpec
      Formalism.FourierDecayAlt.Final.d_ptRelevant Formalism.FourierDecayAlt.Final.d_muRHaar Formalism.FourierDecayAlt.Final.jc_orbJCutScalar
      E Wp Wq S T f χ ν' m₀ top A₀ hg1 hg2 hB)

end Formalism.L2.SG.Pf.Carrier
