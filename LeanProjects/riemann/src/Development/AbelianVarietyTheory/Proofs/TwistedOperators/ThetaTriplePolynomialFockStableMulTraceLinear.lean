import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.PolMul

open GlobalTheory.HeisDeriv GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def liftInf (z : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z)

theorem evI_liftInf (z : mixedEmbedding.mixedSpace F) : evI F (liftInf F z) = z := by
  simp [evI, liftInf]

theorem mul_liftInf_eq_zero {a : AF F} (ha : evI F a = 0) (z : mixedEmbedding.mixedSpace F) :
    a * liftInf F z = 0 := by
  have h1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact ha)
  refine Prod.ext ?_ ?_
  · show a.1 * ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) = 0
    rw [h1, zero_mul]
  · show a.2 * 0 = 0
    rw [mul_zero]

theorem actsD_mult {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (y : Fin n × Fin d → AF F) (hu : M.co.e u = (0, y))
    (f : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f (SchwartzMap.smulLeftCLM ℂ (⇑(mult F y)) f) := by
  intro r _ x

  have he : ∀ t : ℝ, M.co.e (realAd F t • u) = (0, realAd F t • y) := by
    intro t
    rw [LinearEquiv.map_smul, hu]
    refine Prod.ext ?_ ?_ <;> simp
  set a : AF F := x ⬝ᵥ y with ha
  set K : ℂ := tens (evI F) (⇑f) r x with hK
  set c : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) with hc

  have hT : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) (⇑f) r) x = ψ (realAd F t * a) * K := by
    intro t
    simp only [Model.heisLine, Darboux.rho, he t, schr, zero_dotProduct, mul_zero, add_zero, dotProduct_smul,
      smul_eq_mul, ha, hK]

  have hAt : ∀ t : ℝ, At (evI F) (realAd F t * a) := by
    intro t v hv
    rw [smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero hv, zero_mul]
  have hψt : ∀ t : ℝ, ψ (realAd F t * a) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((t * c : ℝ)) : ℂ)) := by
    intro t
    rw [hψ.2.2 _ (hAt t), evI_mul, evI_realAd, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hfun : (fun t : ℝ => M.heisLine ψ u t (tens (evI F) (⇑f) r) x) =
      fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * (((t * c : ℝ)) : ℂ)) * K := by
    funext t
    rw [hT t, hψt t]
  have h0 : HasDerivAt (fun t : ℝ => ((t * c : ℝ) : ℂ)) ((1 * c : ℝ) : ℂ) 0 :=
    ((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp
  have h2 := ((h0.const_mul (-(2 * Real.pi * Complex.I))).cexp).mul_const K

  have htr : trForm F y (fun i => evI F (x i)) = c := by
    rw [trForm_apply, hc, ha, dotProduct, evI_sum]
    simp only [evI_mul]
  rw [hfun]
  refine h2.congr_deriv ?_
  simp only [tens, hK, SchwartzMap.smulLeftCLM_apply_apply (mult F y).hasTemperateGrowth, mult_apply, htr, zero_mul,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, smul_eq_mul]
  ring

theorem model_mul {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (F := F) E w)
    (q : Fin n × Fin d → mixedEmbedding.mixedSpace F) (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol ψ τ) :
    ∃ f₁ ∈ M.Pol ψ τ, ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q : ℂ) * f x := by

  set y : Fin n × Fin d → AF F := fun i => liftInf F (q i) with hy
  set u := M.co.e.symm (0, y) with hu
  have hue : M.co.e u = (0, y) := by simp [hu]
  have hat : At (evI F) u := by
    intro v hv
    rw [← LinearEquiv.map_eq_zero_iff M.co.e, LinearEquiv.map_smul, hue]
    refine Prod.ext ?_ ?_
    · simp
    · funext i
      simp [hy, mul_liftInf_eq_zero hv]
  have hmem : SchwartzMap.smulLeftCLM ℂ (⇑(mult F y)) f ∈ M.Pol ψ τ := by
    rw [Model.Pol, Submodule.mem_sInf] at hf ⊢
    intro N hN
    exact hN.2 u hat f (hf N hN) _ (actsD_mult M ψ hψ u y hue f)
  have hne : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨(-(2 * Real.pi * Complex.I))⁻¹ • SchwartzMap.smulLeftCLM ℂ (⇑(mult F y)) f,
    Submodule.smul_mem _ _ hmem, fun x => ?_⟩
  have htr : trForm F y x = GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q := by
    rw [trForm_apply, GlobalTheory.GaussLine.pairInf_apply]
    simp only [hy, evI_liftInf]
  rw [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply (mult F y).hasTemperateGrowth, mult_apply, htr,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end GlobalTheory.PolMul

theorem GlobalTheory.PolMul.pol_mul_pairInf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (q : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F),
    ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a')) x q : ℂ) * f x := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT q f hf
  exact GlobalTheory.PolMul.model_mul G.M B.ψ hT.base.std B.emb q f hf

end
