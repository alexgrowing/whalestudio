import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct

namespace GlobalTheory.RealLineInU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_eq_zero_finite_part_zero (u : AF F) (hu : u.1 = 0) (z : AF F ⊗[F] E) (hz : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z = 0) : u • z = 0 := by
  have key : ∀ z : AF F ⊗[F] E, u • z = (LinearMap.rTensor E ((LinearMap.inr F (Ainf F) (Af F)) ∘ₗ LinearMap.mulLeft F u.2)) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero]; rfl
    | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]; rfl
    | tmul a x =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      congr 1
      refine Prod.ext ?_ rfl
      show u.1 * a.1 = 0
      rw [hu, zero_mul]
  rw [key, hz, map_zero]; rfl

end GlobalTheory.RealLineInU

open GlobalTheory.RealLineInU in

theorem GlobalTheory.RealLineInU.exists_mem_lines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x), IsCMExt F E σ → ∀ {d : ℕ} (W : Spc F E d) (c : E) (hc : c ≠ 0)
    (γ : ℝ → GAd σ (c • W.J.map σ)), IsRealLine σ (c • W.J.map σ) γ →
    ∃ γL ∈ Lines σ W, ∀ t : ℝ, (toGAd hσ W.J hc).symm (γ t) = γL (Multiplicative.ofAdd t) := by
  intro F E _ _ _ _ _ σ hσ hCM d W c hc γ hγ
  have hadd := isRealLine_add F E σ hCM d _ γ hγ
  have hcont := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ hCM d _ γ hγ
  have h0 : γ 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := γ 0) (by rw [mul_one]; exact h.symm)
  let e := toGAd hσ W.J hc
  let γL : Multiplicative ℝ →* UA σ W.J :=
    { toFun := fun t => e.symm (γ (Multiplicative.toAdd t))
      map_one' := by
        show e.symm (γ 0) = 1
        rw [h0, map_one]
      map_mul' := fun s t => by
        show e.symm (γ (Multiplicative.toAdd s + Multiplicative.toAdd t)) = _
        rw [hadd, map_mul] }
  refine ⟨γL, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · have he : Continuous e.symm := Continuous.subtype_mk continuous_subtype_val _
    exact he.comp (hcont.comp continuous_toAdd)
  · obtain ⟨w, τ, Z, -, hy⟩ := hγ
    obtain ⟨y, hyt, -⟩ := hy (Multiplicative.toAdd t)
    have hinf : γ (Multiplicative.toAdd t) ∈ infPts σ (c • W.J.map σ) := by
      rw [mem_infPts, hyt]; exact projFin_embArch _ _ w y
    have hent : ∀ i j, (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))
        ((HA.mat (AF F) σ (c • W.J.map σ) (γ (Multiplicative.toAdd t))).1 i j) =
          (1 : Matrix (Fin d) (Fin d) (Af F ⊗[F] E)) i j := fun i j =>
      congrArg (fun k : GL (Fin d) (Af F ⊗[F] E) => k.1 i j) (MonoidHom.mem_ker.1 hinf)
    intro u hu
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    ext i j
    rw [Matrix.smul_apply, Matrix.zero_apply]
    apply smul_eq_zero_finite_part_zero u hu1
    change (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))
        ((HA.mat (AF F) σ (c • W.J.map σ) (γ (Multiplicative.toAdd t))).1 i j - (1 : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) i j) = 0
    rw [map_sub, hent, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
