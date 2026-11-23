import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.LineRealAd

theorem continuous_mixedSpace_symm (K : Type) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩).symm

variable {D : D7}

theorem infPart_smul (a : AF D.host.F) (x : AE D) :
    infPart D (a • x) = (a.1 ⊗ₜ[D.host.F] (1 : D.host.E)) * infPart D x := by
  rw [Algebra.smul_def, map_mul]
  rfl

theorem finPart_smul (a : AF D.host.F) (x : AE D) :
    finPart D (a • x) = (a.2 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D x := by
  rw [Algebra.smul_def, map_mul]
  rfl

theorem theta_realAd {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (t : ℝ) :
    θ ρ ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t).1 ⊗ₜ[D.host.F] (1 : D.host.E)) = t := by
  let g : ℝ →+* ℂ := (θ ρ).comp ((Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (B := D.host.E)).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm.toRingHom.comp (algebraMap ℝ _)))
  have hg : Continuous g :=
    (hθ ρ).2.comp ((continuous_mixedSpace_symm _).comp (continuous_algebraMap ℝ _))
  have h : g (t • (1 : ℝ)) = t • g 1 := map_real_smul g.toAddMonoidHom hg t 1
  rw [smul_eq_mul, mul_one, map_one, Complex.real_smul, mul_one] at h
  exact h

end GlobalTheory.LineRealAd

namespace GlobalTheory.LineRealAd

theorem lineAt_realAd_smul : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ),
    (∀ t : ℝ, lineAt θ τ z t = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • lineAt θ τ z 1) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (lineAt θ τ z 1) := by
  classical
  intro D θ hθ m n τ z
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hfin : ∀ t i j, finPart D (lineAt θ τ z t i j) = 0 := fun t i j => congrFun (congrFun (hL.2.1 t) i) j
  have hcomp : ∀ t τ' i j, θ τ' (infPart D (lineAt θ τ z t i j)) =
      (if τ' = τ then (t : ℂ) • z else 0) i j := fun t τ' i j => congrFun (congrFun (hL.2.2 t τ') i) j
  refine ⟨fun t => ?_, fun u hu => ?_⟩
  · funext i j
    refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ' => ?_)
    · show finPart D (lineAt θ τ z t i j - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • lineAt θ τ z 1 i j) = 0
      rw [RingHom.map_sub, finPart_smul, hfin, hfin, mul_zero, sub_zero]
    · show θ τ' (infPart D (lineAt θ τ z t i j - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • lineAt θ τ z 1 i j)) = 0
      rw [RingHom.map_sub, infPart_smul, RingHom.map_sub, RingHom.map_mul, theta_realAd hθ, hcomp, hcomp]
      split_ifs <;> simp
  · funext i j
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).map_eq_zero_iff.1 hu
    refine hσ.ext _ ?_ fun τ' => ?_
    · show finPart D (u • lineAt θ τ z 1 i j) = 0
      rw [finPart_smul, hfin, mul_zero]
    · show θ τ' (infPart D (u • lineAt θ τ z 1 i j)) = 0
      rw [infPart_smul, hu1, TensorProduct.zero_tmul, zero_mul, map_zero]

end GlobalTheory.LineRealAd
