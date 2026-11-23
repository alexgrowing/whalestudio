import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatAtHLat

theorem mem_latAt_iff_hat {D : D7} {S T : HSp D} (B : Base S T) (h : Bridge.Gf S) (x : Fin S.rank → D.host.E) :
    x ∈ B.latAt h ↔ (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      GlobalTheory.AdLat.hat D.host.F (B.F.ΛS : Set (Fin S.rank → D.host.E)) := by
  have e : ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) =
      fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (((h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) i) := by
    rw [← map_inv]
    funext i
    change _ = Lev.swapAE D _
    rw [RingHom.map_mulVec (Lev.swapAE D)]
    rfl
  change ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS ↔ _
  rw [e]
  constructor
  · intro hz
    have := GlobalTheory.PrincInLevel.swap_symm_mem_hat B.F.ΛS _ hz
    simpa only [AlgEquiv.symm_apply_apply] using this
  · intro hz
    exact GlobalTheory.PrincInLevel.swap_mem_hatL B.F.ΛS _ hz

theorem latAt_eq_hLat : ∀ (D : D7) (S T : HSp D) (B : Base S T), (B.F.ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → ∀ h, B.latAt h = Bridge.hLat S h := by
  intro D S T B hΛ h
  have e : Bridge.hLat S h = Submodule.span (𝓞 D.host.E) {x : Fin S.rank → D.host.E |
      (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
        GlobalTheory.AdLat.hat D.host.F (B.F.ΛS : Set (Fin S.rank → D.host.E))} := by
    unfold Bridge.hLat
    rw [hΛ]
    rfl
  rw [e, ← Submodule.span_eq (B.latAt h)]
  congr 1
  ext x
  exact mem_latAt_iff_hat B h x

end GlobalTheory.LatAtHLat
