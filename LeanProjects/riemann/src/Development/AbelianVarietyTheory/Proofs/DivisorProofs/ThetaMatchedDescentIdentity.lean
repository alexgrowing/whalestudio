import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairThetaUniformBoundFamilyStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Filter Topology

noncomputable section
open scoped Classical

namespace GlobalTheory.ThetaDerivFirst

theorem rest_fin {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ) {φ : (κ → Af F) → ℂ}
    (hφ : φ ∈ SB (κ → Af F)) : Rest (evI F) ⇑f (fun x : κ → AF F => φ fun i => (x i).2) := by
  refine ⟨fun x z hz => congrArg φ (funext fun i => ?_), Submodule.subset_span ⟨f, φ, hφ, rfl⟩⟩
  have hu : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd (congrFun (hz _ hu) i)
  show (x i).2 + (z i).2 = (x i).2
  rw [one_mul] at h2
  rw [h2, add_zero]

theorem hasDerivAt_theta_line : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V', ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Φ₁ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), (∀ x, HasDerivAt (fun t : ℝ => om' (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J) (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), HasDerivAt (fun t : ℝ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (g * γ (Multiplicative.ofAdd t)) h) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ₁ g h) 0 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ _ hd g h
  have hT := hM.triple
  have hsch := GlobalTheory.KDecayProof.so_le_schA hT.geo.hM' B.τ₁ (Submodule.mem_inf.1 hΦ).2
  obtain ⟨n, c, s, hs⟩ := Submodule.mem_span_set'.1 hsch
  choose f0 φ hφ hfe using fun i => (s i).2
  choose u u₁ hu hu₁ using fun i : Fin n => GlobalTheory.T.weil_line_good_model_polynomial hP.base G.M' B.ψ _ _ om' hT.base.std hT.geo.hM' hT.weil' γ hγ
    (c i • f0 i) _ (rest_fin (c i • f0 i) (hφ i))
  have hΦe : Φ = ∑ i, pureA F (c i • f0 i) (φ i) := by
    rw [← hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfe i]
    funext x
    simp [pureA, mul_assoc]
  have horb : ∀ t : ℝ, om' (γ (Multiplicative.ofAdd t), 1) Φ = ∑ i, pureA F (u i t) (φ i) := by
    intro t
    rw [hΦe, map_sum]
    exact Finset.sum_congr rfl fun i _ => hu i t
  have hΦ₁ : Φ₁ = ∑ i, pureA F (u₁ i) (φ i) := by
    funext x
    set y : Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F :=
      fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1
    set z : Fin a' × Fin (a + a') → Af F := fun j => (x j).2
    have hder : ∀ i, HasDerivAt (fun t : ℝ => u i t y) (u₁ i y) 0 := by
      intro i
      rw [hasDerivAt_iff_tendsto_slope]
      let ev : SInf F (Fin a' × Fin (a + a')) →L[ℂ] ℂ := (BoundedContinuousFunction.evalCLM ℂ y).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ)
      have h1 := (ev.continuous.tendsto (u₁ i)).comp (hu₁ i)
      have e2 : ev (u₁ i) = u₁ i y := rfl
      rw [e2] at h1
      refine h1.congr' (Eventually.of_forall fun t => ?_)
      simp [ev, slope_def_module]
    have hsum : HasDerivAt (fun t : ℝ => ∑ i, u i t y * φ i z) (∑ i, u₁ i y * φ i z) 0 :=
      HasDerivAt.fun_sum fun i _ => (hder i).mul_const _
    have e1 : (fun t : ℝ => om' (γ (Multiplicative.ofAdd t), 1) Φ x) = fun t => ∑ i, u i t y * φ i z := by
      funext t
      rw [horb, Finset.sum_apply]
      rfl
    have h3 := hd x
    rw [e1] at h3
    rw [h3.unique hsum, Finset.sum_apply]
    rfl
  have key : ∀ k, theta om' Φ (g * k) h = theta om' (om' (k, 1) Φ) g h := by
    intro k
    unfold theta
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have h4 := GlobalTheory.T.pair_theta_uniform_bound_family hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (GlobalTheory.KDecayProof.isPair_small hT) n φ (fun t i => u i t) u₁
    hφ hu₁ g h
  rw [← hΦ₁] at h4
  simpa only [key, horb] using h4

end GlobalTheory.ThetaDerivFirst
