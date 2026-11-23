import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

noncomputable section
namespace GlobalTheory.KFinReproduce

variable {n : ℕ} {ε : Fin n → Bool}

def kfinFuns (ε : Fin n → Bool) : Submodule ℂ (KG ε → ℂ) where
  carrier := {e | KFinFun ε e}
  add_mem' := by
    rintro a b ⟨F, hF, ha, hc, ht⟩ ⟨F', hF', hb, hc', ht'⟩
    refine ⟨F ⊔ F', inferInstance, Submodule.add_mem_sup ha hb, fun φ hφ => ?_, fun φ hφ k₀ => ?_⟩
    · obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hφ
      exact (hc u hu).add (hc' v hv)
    · obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hφ
      exact ⟨Submodule.add_mem_sup (ht u hu k₀).1 (ht' v hv k₀).1,
        Submodule.add_mem_sup (ht u hu k₀).2 (ht' v hv k₀).2⟩
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, fun φ hφ => by
      rw [(Submodule.mem_bot _).1 hφ]; exact continuous_const,
    fun φ hφ k₀ => by
      rw [(Submodule.mem_bot _).1 hφ]; exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩⟩
  smul_mem' := by
    rintro c a ⟨F, hF, ha, hc, ht⟩
    exact ⟨F, hF, F.smul_mem c ha, hc, ht⟩

theorem continuous_of_kFinFun {e : KG ε → ℂ} (h : KFinFun ε e) : Continuous e := by
  obtain ⟨F, -, he, hc, -⟩ := h
  exact hc e he

theorem integrable_mul {e F : KG ε → ℂ} (he : Continuous e) (hF : Continuous F) :
    Integrable (fun k => e k * F k) (muK ε) :=
  (he.mul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def intSpace {ι : Type} (F : ι → KG ε → ℂ) (hF : ∀ j, Continuous (F j)) : Submodule ℂ (ι → ℂ) where
  carrier := {v | ∃ e, KFinFun ε e ∧ ∀ j, ∫ k, e k * F j k ∂(muK ε) = v j}
  add_mem' := by
    rintro a b ⟨e, he, hea⟩ ⟨e', he', heb⟩
    refine ⟨e + e', (kfinFuns ε).add_mem he he', fun j => ?_⟩
    simp only [Pi.add_apply, add_mul]
    rw [MeasureTheory.integral_add (integrable_mul (continuous_of_kFinFun he) (hF j)) (integrable_mul (continuous_of_kFinFun he') (hF j)), hea, heb]
  zero_mem' := ⟨0, (kfinFuns ε).zero_mem, fun j => by simp⟩
  smul_mem' := by
    rintro c a ⟨e, he, hea⟩
    refine ⟨c • e, (kfinFuns ε).smul_mem c he, fun j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, hea]

end GlobalTheory.KFinReproduce

namespace GlobalTheory.KFinReproduce

end GlobalTheory.KFinReproduce
