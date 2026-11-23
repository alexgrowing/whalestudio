import Development.WeilBound.ThetaLifts.SphericalLattices.LocModSt
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain

noncomputable section

namespace PositivityTheory.Sph.M2

open scoped Matrix
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas

def ChartSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (r s m : ℕ) (W : Spc F E (m + m)), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v)
    (c : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h c →
    ∀ (Cy : Matrix (Fin (m + m)) (Fin m) (AE F E)), IsLagAt σ W v Cy →
    ∃ Φ : UA σ W.J →* GL (Fin m ⊕ Fin m) (w.adicCompletion E),
      (∀ g, Φ g ∈ GW (w.adicCompletion E) c m) ∧
      (∀ g ∈ USub σ W v, ∀ g' ∈ USub σ W v, Φ g = Φ g' → g = g') ∧
      (∀ M ∈ GW (w.adicCompletion E) c m, ∃ g ∈ USub σ W v, Φ g = M) ∧
      (∀ g ∈ USub σ W v, g ∈ KSub σ W v ↔ Φ g ∈ IntGL (w.adicCompletion E) m) ∧
      (∀ g ∈ USub σ W v, g ∈ PositivityTheory.Sph.PSub σ W v Cy ↔ Φ g ∈ PW (w.adicCompletion E) c m) ∧
      ∀ p ∈ PositivityTheory.Sph.PSub σ W v Cy, ∀ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t →
        ((Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₁₁).det = piE h t.det

end PositivityTheory.Sph.M2

end
