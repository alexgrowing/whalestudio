import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitContinuousStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.ThKConeB

theorem continuous_I_pure (hP : GlobalTheory.ThK.KP) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) →
    (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ → ∀ h : UA σ G.W.J,
      Continuous fun f : SInf F (Fin a' × Fin (a + a')) => G.M'.I om' (pure f φ) h := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT φ hSB hev hSo h
  have hPair := GlobalTheory.ThK.Inhab.pairV' hT
  have hstd := hT.geo.hM'.std
  let A : (Fin a' × Fin (a + a') → Af F) → ℂ :=
    fun z => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i)
  have hA : A ∈ SB (Fin a' × Fin (a + a') → Af F) :=
    GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ φ hSB ((hev.and hstd).mono fun v hv => hv.1.trans hv.2)
  have heq : ∀ u : SInf F (Fin a' × Fin (a + a')), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure u φ = pureA F u A := fun _ => rfl
  have hpure : ∀ u : SInf F (Fin a' × Fin (a + a')), pureA F u A ∈ G.M'.So B.ψ B.τ₁ := fun u =>
    Submodule.subset_span ⟨u, φ, hSB, hev, hSo, (heq u).symm⟩
  refine continuous_iff_seqContinuous.2 fun u f hu => ?_
  have hcont := GlobalTheory.T.schwartz_orbit_continuous hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hPair 1 (fun _ => A)
    (fun _ => f) (fun k _ => u k) (fun _ => ⟨hA, hu⟩)
    (fun k => Submodule.sum_mem _ fun _ _ => hpure (u k))
    (Submodule.sum_mem _ fun _ _ => hpure f) h
  simp only [Fin.sum_univ_one] at hcont
  exact hcont

end GlobalTheory.ThKConeB
