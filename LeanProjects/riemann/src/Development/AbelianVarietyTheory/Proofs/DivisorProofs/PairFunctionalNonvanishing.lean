import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankDeficientSchwartzAverageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairLinearBarVectorStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKSoKill

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

open Classical in

theorem pure_update_zero (v : Pl F) (f : SInf F κ) (φ : ∀ w : Pl F, (κ → Fv F w) → ℂ)
    (hfin : ∀ x : κ → AF F, (Function.mulSupport fun w => φ w fun i => evFin F w (x i)).Finite) :
    pure f (Function.update φ v 0) = 0 := by
  funext x
  rw [GlobalTheory.ThK.LocalOps.pure_split v f φ (Function.update φ v 0) x (hfin x)
    (fun w hw => Function.update_of_ne hw _ _), Function.update_self, Pi.zero_apply, zero_mul, Pi.zero_apply]

open Classical in

theorem pure_update_sum (v : Pl F) (f : SInf F κ) (φ : ∀ w : Pl F, (κ → Fv F w) → ℂ)
    (hfin : ∀ x : κ → AF F, (Function.mulSupport fun w => φ w fun i => evFin F w (x i)).Finite)
    {N : ℕ} (a : Fin N → ℂ) (g : Fin N → (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v (∑ m, a m • g m)) = ∑ m, a m • pure f (Function.update φ v (g m)) := by
  funext x
  rw [GlobalTheory.ThK.LocalOps.pure_split v f φ _ x (hfin x) (fun w hw => Function.update_of_ne hw _ _),
    Function.update_self, Finset.sum_apply, Finset.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := GlobalTheory.ThK.LocalOps.pure_split v f φ (Function.update φ v (g m)) x (hfin x)
    (fun w hw => Function.update_of_ne hw _ _)
  rw [Function.update_self] at h
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h, mul_assoc]

end GlobalTheory.ThKSoKill

namespace GlobalTheory.ThKSoKill

theorem at_vecMulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (v : Pl F) (c : Fin n → AE F E) (z : Fin d → AE F E) (hz : At (evFin F v) z) :
    At (evFin F v) (Matrix.vecMulVec c z) := by
  intro u hu
  ext i j
  have h := congrFun (hz u hu) j
  simp only [Pi.smul_apply, Pi.zero_apply] at h
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  rw [← mul_smul_comm, h, mul_zero]

open Classical in

theorem so_kill : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (c : Fin n → AE F E),
    (fun k => piW B.τ₁ (c k)) ≠ 0 →
    (∀ z : Fin d → AE F E, At (evFin F B.v₁) z → (∀ l, piW (B.τ₁.comp σ) (z l) = 0) →
      ∀ Ψ ∈ schA F (Fin n × Fin d), Λ (M.co.rho B.ψ (Matrix.vecMulVec c z) Ψ) = Λ Ψ) →
    ∀ Φ ∈ M.So B.ψ B.τ₁, Λ Φ = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Λ c hc hinv Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero => exact map_zero Λ
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]
  | mem x hx =>
    obtain ⟨f, φ, hSB, hcof, ⟨hSB1, ι, hι, hrank⟩, rfl⟩ := hx
    have hstd := (hcof.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    have hfin := fun x => GlobalTheory.PureFactor.mulSupport_finite φ hstd x
    have hpure := GlobalTheory.ConeMeasV.pure_mem_schA hP.good f φ hSB hcof
    obtain ⟨N, a, w, ha1, hkill⟩ := GlobalTheory.T.rank_deficient_schwartz_average F B.v₁ (GlobalTheory.LatVac.psiAt B.ψ B.v₁)
      (GlobalTheory.SchrSB.continuous_psiAt B.ψ hP.base.std.1 B.v₁) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hP.base.std B.v₁)
      n d (fun k => piW B.τ₁ (c k)) hc (ι (φ B.v₁)) (hι.bij.mapsTo hSB1) hrank
    have hmult := fun m => GlobalTheory.T.pair_linear_bar_vector F E σ B n d X W M χX χW om r s r' s' hP c ι hι (w m)
    choose z hzat hzpi hzmul using hmult
    have hAE := GlobalTheory.ThK.LocalOps.actsEx hKP.base
    have hex : ∀ m, ∃ φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F B.v₁) ∧
        Acts (evFin F B.v₁) (M.co.rho B.ψ (Matrix.vecMulVec c (z m))) (φ B.v₁) φ₁ := fun m =>
      ((hAE F E σ B n d X W M χX χW om r s r' s' hP B.v₁).2.1 _ (at_vecMulVec B.v₁ c (z m) (hzat m)) _ hSB1).exists
    choose φ₁ hφ₁SB hφ₁ using hex

    have hsumSB : ∑ m, a m • φ₁ m ∈ SB (Fin n × Fin d → Fv F B.v₁) :=
      Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hφ₁SB m)
    have hsum0 : ∑ m, a m • φ₁ m = 0 := by
      refine hι.bij.injOn hsumSB (Submodule.zero_mem _) ?_
      rw [map_zero, map_sum]
      funext Y
      rw [Finset.sum_apply, Pi.zero_apply]
      have hY := hkill Y
      rw [Finset.sum_mul] at hY
      rw [← hY]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul, Pi.smul_apply, smul_eq_mul, hzmul m (φ B.v₁) hSB1 (φ₁ m) (hφ₁SB m) (hφ₁ m) Y,
        GlobalTheory.LatVac.psiAt_apply, mul_assoc]

    have hact : ∀ m, M.co.rho B.ψ (Matrix.vecMulVec c (z m)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pure f (Function.update φ B.v₁ (φ₁ m)) :=
      fun m => GlobalTheory.ThK.LocalOps.acts_pure B.v₁ _ f φ (φ₁ m) hpure hfin (hφ₁ m)
    calc Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = ∑ m, a m • Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by rw [← Finset.sum_smul, ha1, one_smul]
      _ = ∑ m, a m • Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ B.v₁ (φ₁ m))) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← hact m, hinv (z m) (hzat m) (hzpi m) _ hpure]
      _ = Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ B.v₁ (∑ m, a m • φ₁ m))) := by
          rw [pure_update_sum B.v₁ f φ hfin a φ₁, map_sum]
          simp only [map_smul]
      _ = 0 := by rw [hsum0, pure_update_zero B.v₁ f φ hfin, map_zero]

end GlobalTheory.ThKSoKill
