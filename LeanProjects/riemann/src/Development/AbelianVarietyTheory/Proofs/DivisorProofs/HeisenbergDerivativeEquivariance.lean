import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay

theorem schr_finset_sum {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) {ι : Type} (s : Finset ι) (φ : ι → (κ → R) → ℂ) :
    schr ψ w (∑ k ∈ s, φ k) = ∑ k ∈ s, schr ψ w (φ k) := by
  funext x
  simp only [schr, Finset.sum_apply, Finset.mul_sum]

theorem actAB_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E} (p : UA σ JX × UA σ JW) (a : AF F)
    (u : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) p (a • u) = a • actAB (cA σ) p u := by
  simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.ThetaDecay

open GlobalTheory.ThetaDecay in

theorem GlobalTheory.ThetaDecay.dH_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArch (M.co.e u) → dH B.ψ (M.co.e (actAB (cA σ) p u)) (om p Φ) = om p (dH B.ψ (M.co.e u) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ p u hu
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hψ
  have hAt : At (evI F) u := by
    intro a ha
    apply M.co.e.injective
    rw [map_smul, map_zero]
    exact Prod.ext (funext fun i => (hu i).1 a ha) (funext fun i => (hu i).2 a ha)
  obtain ⟨m, c, q, hq⟩ := Submodule.mem_span_set'.mp hΦ
  choose f g hg hfg using fun i => (q i).2
  set f' : Fin m → SInf F (Fin n × Fin d) := fun i => c i • f i with hf'
  have hΦe : Φ = ∑ i, pureA F (f' i) (g i) := by
    rw [← hq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfg i]
    funext x
    simp [f', pureA, mul_assoc]
  have hrho : ∀ (t : ℝ) (Ψ : (Fin n × Fin d → AF F) → ℂ),
      M.co.rho B.ψ (realAd F t • u) Ψ = schr B.ψ (realAd F t • M.co.e u) Ψ := by
    intro t Ψ
    rw [Darboux.rho, map_smul]

  have hdΦ : dH B.ψ (M.co.e u) Φ = ∑ i, pureA F (D u (f' i)) (g i) := by
    funext y
    have h : ∀ i, HasDerivAt (fun t : ℝ => schr B.ψ (realAd F t • M.co.e u) (pureA F (f' i) (g i)) y)
        (pureA F (D u (f' i)) (g i) y) 0 := by
      intro i
      have := (hD u hAt (f' i)).1 (g i) (hg i) (GlobalTheory.ExpAct.evalAt y) (GlobalTheory.ExpAct.evalAt_mem_adm F _ y)
      simpa only [GlobalTheory.ExpAct.evalAt, LinearMap.proj_apply, hrho] using this
    have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h i
    have e : (fun t : ℝ => schr B.ψ (realAd F t • M.co.e u) Φ y) =
        fun t => ∑ i, schr B.ψ (realAd F t • M.co.e u) (pureA F (f' i) (g i)) y := by
      funext t
      rw [hΦe, schr_finset_sum, Finset.sum_apply]
    rw [dH, e, hs.deriv, Finset.sum_apply]
  funext x
  set l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := GlobalTheory.ExpAct.evalAt x ∘ₗ om p with hl
  have hladm : l ∈ (adeleClass F).adm (Fin n × Fin d) := hS.adm p _ (GlobalTheory.ExpAct.evalAt_mem_adm F _ x)
  have h : ∀ i, HasDerivAt (fun t : ℝ => l (M.co.rho B.ψ (realAd F t • u) (pureA F (f' i) (g i))))
      (l (pureA F (D u (f' i)) (g i))) 0 := fun i => (hD u hAt (f' i)).1 (g i) (hg i) l hladm
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h i
  have e : (fun t : ℝ => schr B.ψ (realAd F t • M.co.e (actAB (cA σ) p u)) (om p Φ) x) =
      fun t => ∑ i, l (M.co.rho B.ψ (realAd F t • u) (pureA F (f' i) (g i))) := by
    funext t
    have e1 : ∑ i, l (M.co.rho B.ψ (realAd F t • u) (pureA F (f' i) (g i))) = l (M.co.rho B.ψ (realAd F t • u) Φ) := by
      rw [← map_sum, hΦe, Darboux.rho, schr_finset_sum]
    rw [e1, hl, LinearMap.comp_apply, hS.impl p _ Φ hΦ, actAB_smul, Darboux.rho, map_smul]
    rfl
  rw [dH, e, hs.deriv, ← map_sum, hdΦ, hl, LinearMap.comp_apply]
  rfl
