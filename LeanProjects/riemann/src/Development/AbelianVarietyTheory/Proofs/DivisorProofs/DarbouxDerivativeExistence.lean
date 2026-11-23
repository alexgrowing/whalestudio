import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

noncomputable section

namespace GlobalTheory.ThK.PlaneEv.LineDer

variable {F : Type} [Field F] [NumberField F]

def liftI {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), 0)

theorem evI_liftI {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (i : κ) : evI F (liftI x i) = x i := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i)) = x i
  exact RingEquiv.apply_symm_apply _ _

theorem smul_liftI {κ : Type} (t : AF F) (ht : evI F t = 0) (x : κ → mixedEmbedding.mixedSpace F) : t • liftI x = 0 := by
  have h1 : t.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact ht)
  funext i
  show t * liftI x i = 0
  refine Prod.ext ?_ ?_
  · show t.1 * _ = 0
    rw [h1, zero_mul]
  · show t.2 * 0 = 0
    exact mul_zero _

theorem derivLines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (co : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ → GlobalTheory.RealLift.DerEx →
    GlobalTheory.RealLift.ActsLaws → HasDH F κ ∧
      (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
        ActsD (evI F) (fun t => co.rho ψ (realAd F t • u)) f f₁ ↔ ⇑f₁ = dH (cw co u).1 (cw co u).2 ⇑f) ∧
      ∀ a b : κ → mixedEmbedding.mixedSpace F, ∃ u : Matrix α β (AE F E), At (evI F) u ∧ cw co u = (a, b) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB co hψ hD hA
  obtain ⟨D, hDu⟩ := hD F E σ α β κ ψ JA JB co hψ
  have hDf : ∀ u, At (evI F) u → ∀ f : SInf F κ, ⇑(D u f) = dH (cw co u).1 (cw co u).2 ⇑f :=
    fun u hu f => funext fun x => (hDu u hu f).2 x
  have real : ∀ a b : κ → mixedEmbedding.mixedSpace F, ∃ u : Matrix α β (AE F E), At (evI F) u ∧ cw co u = (a, b) := by
    intro a b
    refine ⟨co.e.symm (liftI a, liftI b), fun t ht => ?_, ?_⟩
    · rw [← map_smul, Prod.smul_mk, smul_liftI t ht, smul_liftI t ht, Prod.mk_zero_zero, map_zero]
    · simp only [cw, LinearEquiv.apply_symm_apply, evI_liftI]
  refine ⟨fun a b f => ?_, fun u hu f f₁ => ?_, real⟩
  · obtain ⟨u, hu, hc⟩ := real a b
    exact ⟨D u f, by rw [hDf u hu f, hc]⟩
  · have h0 : ∀ t, (fun t => co.rho ψ (realAd F t • u)) t 0 = 0 := fun t => by
      funext x
      simp [Darboux.rho, schr]
    have h1 : ActsD (evI F) (fun t => co.rho ψ (realAd F t • u)) f (D u f) :=
      (hA F κ f (D u f) (D u f)).1 _ h0 (hDu u hu f).1
    rw [← hDf u hu f]
    constructor
    · intro h2
      rw [(hA F κ f f₁ (D u f)).2.2.1 _ h2 h1]
    · intro e
      rwa [DFunLike.coe_injective e]

end GlobalTheory.ThK.PlaneEv.LineDer
