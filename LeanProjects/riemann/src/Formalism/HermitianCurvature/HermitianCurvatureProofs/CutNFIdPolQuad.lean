import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPol
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem nfPolQuadAll_of (hMeas : TopDMeasCpt) (hApx : NFApxDomAll) : NFPolQuadAll := by
  intro hA Cb
  obtain ⟨C1, H1⟩ := nFTopFormAll_of hMeas hApx hA Cb
  obtain ⟨C2, H2⟩ := nFTopInt_of hMeas hApx Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  have hH1 := nfHyp_mono hH (le_max_left C1 C2) hH.1
  have hH2 := nfHyp_mono hH (le_max_right C1 C2) hH.1
  refine ⟨H2 Wp Wq P p f A₀ p₀ χ Y N hH2 w hw hN ε hε, ?_⟩
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hF := ckOn_fpm p p₀ hH.2.2.1 hid
  have hc := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hH.1 hF ε
  rw [← residual_pairing_eq_self_pairing p hc hw.1]
  exact H1 Wp Wq P p f A₀ p₀ χ Y N hH1 w hw hN ε hε

end

end Formalism.FourierDecayAlt.P.CutBP
