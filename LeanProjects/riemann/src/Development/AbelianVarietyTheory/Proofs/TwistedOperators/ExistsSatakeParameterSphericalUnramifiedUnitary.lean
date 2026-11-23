import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

namespace GlobalTheory.LFun.ExSatU

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem exists_hasSatU : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : w.adicCompletion E) (σ : w.adicCompletion E →+* w.adicCompletion E) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    ρ.IsIrreducible → IsAdmissible ρ → GlobalTheory.LGrp.IsSpherical ρ (KU σ n) → ∃ α, HasSatU ϖ q ρ α := by
  intro E _ _ w ϖ σ q n hU V _ _ ρ hi ha hs
  obtain ⟨ho, hc⟩ := GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints (w.adicCompletion E) ϖ σ q n hU
  exact GlobalTheory.LFun.SatCompare.exists_hasSatU hU ⟨ha.1, hi⟩ (ha.2 _ ho hc) hs

end GlobalTheory.LFun.ExSatU

end
