import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeIncInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLatticeLAdicCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductSchwartzGlue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationGauss
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvAt0.PolEv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Gen

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem at_symm (M : Model σ X W) (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    At (evI F) (M.co.e.symm (fun i => liftA (a i), fun i => liftA (b i))) := by
  intro c hc
  rw [← map_smul]
  have : c • ((fun i => liftA (a i), fun i => liftA (b i)) : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) = 0 := by
    ext i <;> simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] <;>
      exact smul_liftA hc _
  rw [this, map_zero]

theorem arc_liftA {κ : Type} (a : κ → mixedEmbedding.mixedSpace F) : arc (fun i => liftA (a i)) = a := by
  funext i; exact evI_liftA (a i)

theorem actsD_iff_dOp {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ
  have e : D u f = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
    ext x
    rw [(hD u hu f).2 x, dOp_apply]
    rfl
  have h1 : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
    (GlobalTheory.T.archActionReadings_compatible F _ f (D u f) (D u f)).1 _ (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
      (hD u hu f).1
  rw [← e]
  exact ⟨fun h2 => (GlobalTheory.T.archActionReadings_compatible F _ f f₁ (D u f)).2.2.1 _ h2 h1, fun h2 => h2 ▸ h1⟩

theorem isGauss_iff {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (g : SInf F (Fin n × Fin d)) : M.IsGauss ψ τ g ↔ GaussD M τ g := by
  refine exists_congr fun ε => forall₂_congr fun u u' => forall₃_congr fun hu hu' _ => ⟨fun H => ?_, fun H f f' hf hf' => ?_⟩
  · exact H _ _ ((actsD_iff_dOp hψ M u hu _ _).2 rfl) ((actsD_iff_dOp hψ M u' hu' _ _).2 rfl)
  · rw [(actsD_iff_dOp hψ M u hu _ _).1 hf, (actsD_iff_dOp hψ M u' hu' _ _).1 hf']
    exact H

theorem pol_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    M.Pol ψ τ = sInf {N | (∀ f₀, GaussD M τ f₀ → f₀ ∈ N) ∧
      ∀ (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F), ∀ f ∈ N, dOp a b f ∈ N} := by
  unfold Model.Pol
  congr 1
  ext N
  simp only [Set.mem_setOf_eq]
  refine and_congr (forall_congr' fun f₀ => imp_congr_left (isGauss_iff hψ M τ f₀)) ⟨fun H a b f hf => ?_, fun H u hu f hf f₁ h1 => ?_⟩
  · have hu := at_symm M a b
    refine H _ hu f hf _ ((actsD_iff_dOp hψ M _ hu _ _).2 ?_)
    rw [LinearEquiv.apply_symm_apply, arc_liftA, arc_liftA]
  · rw [(actsD_iff_dOp hψ M u hu _ _).1 h1]
    exact H _ _ f hf

theorem dOp_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ) :
    dOp a b f ∈ M.Pol ψ τ := by
  rw [pol_eq hψ] at hf ⊢
  exact Submodule.mem_sInf.2 fun N hN => hN.2 a b f (Submodule.mem_sInf.1 hf N hN)

theorem gauss_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {f : SInf F (Fin n × Fin d)} (hf : GaussD M τ f) : f ∈ M.Pol ψ τ := by
  rw [pol_eq hψ]
  exact Submodule.mem_sInf.2 fun N hN => hN.1 f hf

end Gen

end GlobalTheory.ThK.EvAt0.PolEv
