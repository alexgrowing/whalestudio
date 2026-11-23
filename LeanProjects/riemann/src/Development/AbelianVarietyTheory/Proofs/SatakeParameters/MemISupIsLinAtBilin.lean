import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaLoc

open GlobalTheory.SplitWeil

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ}

theorem isLinAt_comp {Θ Ω : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup Ω] [Module ℂ Ω]
    (ω₁ : GAf E n × GAf E r →* Module.End ℂ Θ) (ω₂ : GAf E n × GAf E r →* Module.End ℂ Ω)
    (P : Θ → Prop) (T : Θ →ₗ[ℂ] Ω) (hT : ∀ p f, P f → T (ω₁ p f) = ω₂ p (T f))
    (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ)
    (ι : SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ) (hP : ∀ Φ, P (ι Φ))
    (h : IsLinAt ω₁ s μ η ι) : IsLinAt ω₂ s μ η (T ∘ₗ ι) := by
  obtain ⟨c, hc, hc', hι⟩ := h
  refine ⟨c, hc, hc', fun h g hh hg Φ Φ' hΦ => ?_⟩
  simp only [LinearMap.comp_apply]
  rw [← hT _ _ (hP Φ), hι h g hh hg Φ Φ' hΦ, map_smul]

def valAct {G Θ A B : Type} [Monoid G] [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (ω : G →* Module.End ℂ Θ) : G →* Module.End ℂ (A →ₗ[ℂ] B →ₗ[ℂ] Θ) where
  toFun p :=
    { toFun := fun φ => φ.compr₂ (ω p)
      map_add' := fun φ φ' => by ext; simp
      map_smul' := fun c φ => by ext; simp }
  map_one' := by ext; simp
  map_mul' p q := by ext; simp

def single {Θ A B : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (α : A →ₗ[ℂ] ℂ) (β : B →ₗ[ℂ] ℂ) : Θ →ₗ[ℂ] (A →ₗ[ℂ] B →ₗ[ℂ] Θ) where
  toFun f := α.smulRight (β.smulRight f)
  map_add' f f' := by ext; simp
  map_smul' c f := by ext; simp [smul_comm c]

end GlobalTheory.ThetaLoc

end
