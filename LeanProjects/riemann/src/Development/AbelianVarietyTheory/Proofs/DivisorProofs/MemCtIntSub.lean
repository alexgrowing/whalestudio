import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.CTAdd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def CTInt {d d₁ : ℕ} {W : Spc F E d} (H : Plane E d d₁) (f : UA σ W.J → ℂ) : Prop :=
  ∀ (μ : Measure (unip σ W H)) (𝓕 : Set (unip σ W H)), μ.IsHaarMeasure →
    IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H)) 𝓕 μ → μ 𝓕 = 1 →
      ∀ h, IntegrableOn (fun u : unip σ W H => f (u.1 * h)) 𝓕 μ

def ctIntSub {d d₁ : ℕ} {W : Spc F E d} (H : Plane E d d₁) : Submodule ℂ (UA σ W.J → ℂ) where
  carrier := {f | CTInt H f}
  add_mem' := by
    intro f g hf hg μ 𝓕 hμ h𝓕 h1 h
    exact (hf μ 𝓕 hμ h𝓕 h1 h).add (hg μ 𝓕 hμ h𝓕 h1 h)
  zero_mem' := by
    intro μ 𝓕 hμ h𝓕 h1 h
    exact integrableOn_zero
  smul_mem' := by
    intro r f hf μ 𝓕 hμ h𝓕 h1 h
    exact (hf μ 𝓕 hμ h𝓕 h1 h).smul r

theorem isCT_add {d d₁ : ℕ} {W : Spc F E d} (H : Plane E d d₁) {f g c e : UA σ W.J → ℂ}
    (hf : CTInt H f) (hg : CTInt H g) (hc : IsCT H f c) (he : IsCT H g e) : IsCT H (f + g) (c + e) := by
  intro μ 𝓕 hμ h𝓕 h1 h
  simp only [Pi.add_apply]
  rw [hc μ 𝓕 hμ h𝓕 h1 h, he μ 𝓕 hμ h𝓕 h1 h, ← integral_add (hf μ 𝓕 hμ h𝓕 h1 h) (hg μ 𝓕 hμ h𝓕 h1 h)]

end GlobalTheory.ThK.CTAdd

end
