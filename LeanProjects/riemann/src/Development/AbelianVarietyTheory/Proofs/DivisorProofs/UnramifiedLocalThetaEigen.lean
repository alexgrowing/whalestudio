import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaNonsplitInvariantStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

theorem fixed_eq_smul_pVac : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (v : Pl F), IsEmpty (E →ₐ[F] Fv F v) → v ∉ X.T → ∀ ξ : Rf.Pi v,
      (∀ k ∈ KAt σ G.W v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, k)) φ φ₁ → Rf.p v φ = ξ → Rf.p v φ₁ = ξ) →
      ∃ c : ℂ, ξ = c • Rf.p v (G.M.vac v) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM v hv _hT ξ hfix
  have hξ : ξ ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by
    rw [hM.fin.onto v]; exact Submodule.mem_top
  obtain ⟨φ, hφ, hpφ⟩ := Submodule.mem_map.1 hξ
  obtain ⟨c, hc⟩ := GlobalTheory.T.local_theta_nonsplit_invariant hKP F E σ B a a' G X om om' R Rf hM v hv φ hφ
    (fun k hk φ₁ hφ₁ hA => (hfix k hk φ hφ φ₁ hφ₁ hA hpφ).trans hpφ.symm)
  exact ⟨c, hpφ ▸ hc⟩

end GlobalTheory.IndLine

end
