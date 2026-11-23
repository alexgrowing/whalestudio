import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorThetaTorsionTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetIndicatorTheta_torsionTranslates : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → StandardLatticesGL3.Crv D cc dl → ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), IsSdLat L → IsSdLat L' → 0 < c → Pres D (TaylorLogMetric.tor0 D cc dl) (s.lat L) (s.lat L') (B.thMoved a b (s.lat L) (s.lat L')) (toHost s fun z => ((ambOf s B χ cD).chiF a b L L')⁻¹ * (ambOf s B χ cD).thInd S L L' c x z) ((c : ℝ) ^ (Module.finrank ℚ X.E * a * b)) := by
  first | exact @GlobalTheory.ColNorms.IndPres.pres_thInd | exact GlobalTheory.ColNorms.IndPres.pres_thInd | (intros; apply GlobalTheory.ColNorms.IndPres.pres_thInd <;> assumption)
