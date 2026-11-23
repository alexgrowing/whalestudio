import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RetieVolTieGAndCdScaleTie
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem volMeas_fundDomain_eq_of_tiedIndep :
    (∀ D : D7, VolTie D → ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → D.vol W = D.vol W₀) → ∀ D : D7, ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)) (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) (μ₀ : Measure (HA (AF D.host.F) D.sp.cm.sig W₀.gram)) (𝓕₀ : Set (HA (AF D.host.F) D.sp.cm.sig W₀.gram)), IsVolMeas D W P Q μ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ → IsVolMeas D W₀ P₀ Q₀ μ₀ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₀.gram) 𝓕₀ μ₀ → μ 𝓕 = μ₀ 𝓕₀ := by
  intro H D W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr μ 𝓕 μ₀ 𝓕₀ hμ h𝓕 hμ₀ h𝓕₀
  have hT : VolTie (GlobalTheory.Mem.retie D) :=
    Formalism.L2.Theta.VolTieG.volTie (GlobalTheory.Mem.retie_volTieG_and_cdScaleTie D).1
  have e1 : μ 𝓕 = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol W) :=
    ((hT W P Q hW hs).2 μ hμ).2 𝓕 h𝓕
  have e2 : μ₀ 𝓕₀ = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol W₀) :=
    ((hT W₀ P₀ Q₀ hW₀ hs₀).2 μ₀ hμ₀).2 𝓕₀ h𝓕₀
  rw [e1, e2, H (GlobalTheory.Mem.retie D) hT W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr]

end GlobalTheory.Glob
