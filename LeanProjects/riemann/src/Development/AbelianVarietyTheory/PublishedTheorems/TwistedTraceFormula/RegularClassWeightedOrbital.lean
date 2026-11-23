import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

def RegularClassWeightedOrbital : Prop :=
  ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure], ∀ f ∈ CcGA V, ∀ γ : GF V, IsRegSS γ.1.1 → ∀ P, IsMinLevi Φ γ P →
      ∀ (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure], ∃ c : ℝ, ∀ T, Regular c T →
        ∫ q, descend (GQ V) (kT Φ (levelAll D.sp.cm.sig V.gram L a) {δ | IsConj γ δ} f T) q ∂autMeasure V μ =
          volA Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) (cent (rat V γ)) dt *
            wOrbInt (cent (rat V γ)) dt μ (rat V γ)
              (fun x => weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) T x) f

example (D : D7) : wittIndex (CuspDecay.Model.plane D) = 1 ∧
    ∃ (Φ : WittFrame (CuspDecay.Model.plane D)) (L : _) (a : _), Φ.IsGood D.sp.cm L a :=
  ⟨wittIndex_plane D, exists_isGood _⟩

end GlobalTheory.Published

end
