import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeSlice

variable {F : Type} [Field F] [NumberField F]

theorem exists_schwartz_slice {κ : Type} [Fintype κ] {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (x : κ → AF F) :
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ t, f t = Φ (x + GlobalTheory.ThetaTransform.embR t) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, -, rfl⟩ := h
    let a : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1
    refine ⟨g (fun i => (x i).2) • SchwartzMap.compSubConstCLM ℂ (-a) f, fun t => ?_⟩
    simp only [SchwartzMap.smul_apply, SchwartzMap.compSubConstCLM_apply, smul_eq_mul, pureA]
    have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + GlobalTheory.ThetaTransform.embR t) i).1) = t - -a := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i)) =
        t i - -a i
      rw [map_add, RingEquiv.apply_symm_apply, sub_neg_eq_add, add_comm]
    have h2 : (fun i => ((x + GlobalTheory.ThetaTransform.embR t) i).2) = fun i => (x i).2 := by
      funext i
      show (x i).2 + 0 = (x i).2
      exact add_zero _
    rw [h1, h2, mul_comm]
  | zero => exact ⟨0, fun t => by simp⟩
  | add Φ Ψ _ _ hΦ hΨ =>
    obtain ⟨f, hf⟩ := hΦ
    obtain ⟨g, hg⟩ := hΨ
    exact ⟨f + g, fun t => by simp [hf, hg]⟩
  | smul c Φ _ hΦ =>
    obtain ⟨f, hf⟩ := hΦ
    exact ⟨c • f, fun t => by simp [hf]⟩

end GlobalTheory.ConeSlice

namespace GlobalTheory.ConeSlice

theorem integrand_slice_schwartz : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : Fin b × Fin (b + a') → AF F,
      ∀ (k : K) (l : (AE F E)ˣ), ∃ f : SInf F (Fin b × Fin (b + a')), ∀ t, f t = (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) (x + GlobalTheory.ThetaTransform.embR t) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' _ e hE K μK μ _ _ _ X om om' om₁ om₁' hT _ Ψ hΨ x k l
  have h1 : om (k.1, 1) Ψ ∈ schA F _ := (IsUWeilPair.isUSplitting hT.weil).pres (k.1, 1) Ψ hΨ
  have h2 : G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ) ∈ schA F _ :=
    GlobalTheory.ConeMeasV.schr_mem_schA hT.base.std _ h1
  obtain ⟨g, hg⟩ := exists_schwartz_slice (hE.maps _ h2) x
  refine ⟨((X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) • g, fun t => ?_⟩
  rw [SchwartzMap.smul_apply, smul_eq_mul, hg, mul_comm, mul_assoc]

end GlobalTheory.ConeSlice
