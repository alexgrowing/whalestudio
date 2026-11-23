import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJStandardLEngine
import GroundTheory.AutomorphicForms.GL2.GJStandardLDual
import GroundTheory.AutomorphicForms.GL2.GJStandardLFourier

open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

section Dual

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
  {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

theorem archComp_inv (g : AdelicGLn.AdelicGL K n) : archComp K n g⁻¹ = (archComp K n g)⁻¹ :=
  map_inv (archComp K n) g

theorem localComp_inv (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) :
    localComp n v g⁻¹ = (localComp n v g)⁻¹ :=
  map_inv (localComp n v) g

theorem inv_factorization {f : AdelicGLn.AdelicGL K n → ℂ}
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (hf : ∀ g, f g = fi (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)
        (localComp n v g)) (g : AdelicGLn.AdelicGL K n) :
    f g⁻¹ = (fun x ↦ fi x⁻¹) (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K)
        (Representation.dual (π v)) (ℓ v) (Module.Dual.eval ℂ (V v) (ξ v)) (localComp n v g) := by
  rw [hf, archComp_inv]
  simp_rw [localComp_inv]
  rfl

end Dual

section Pair

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem integrable_zetaIntegrand_coeff (hn : 2 ≤ n) (μ : Measure (Reduction.normOneGL K n))
    [μ.IsHaarMeasure] (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ AutomorphicForm.cuspForms K n)
    (h₂ : φ₂ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      φ₁ (Reduction.centralSection K n t * x) = φ₁ x) :
    ∀ Ψ ∈ GJMatrix.matrixSchwartzBruhat K n, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (GJGlobal.zetaIntegrand Ψ (GJGlobal.matrixCoeff μ φ₁ φ₂) s) ν := by
  intro Ψ hΨ
  obtain ⟨σ₀, Λ, Λ', _, _, hZ, _, _⟩ := GJGlobal.globalZeta_entire_functionalEquation hn μ ν h₁ h₂ hA hΨ
  exact ⟨σ₀, fun s hs ↦ (hZ s hs).1⟩

theorem adelicMatrixFourier_four {Ψ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΨ : Ψ ∈ GJMatrix.matrixSchwartzBruhat K n) :
    GJMatrix.adelicMatrixFourier K (GJMatrix.adelicMatrixFourier K (GJMatrix.adelicMatrixFourier K
      (GJMatrix.adelicMatrixFourier K Ψ))) = Ψ := by
  have h2 := GJMatrix.adelicMatrixFourier_mem (GJMatrix.adelicMatrixFourier_mem hΨ)
  rw [GJMatrix.adelicMatrixFourier_adelicMatrixFourier h2, GJMatrix.adelicMatrixFourier_adelicMatrixFourier hΨ]
  funext x
  simp

theorem integrable_zetaIntegrand_coeff_inv (hn : 2 ≤ n) (μ : Measure (Reduction.normOneGL K n))
    [μ.IsHaarMeasure] (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ AutomorphicForm.cuspForms K n)
    (h₂ : φ₂ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      φ₁ (Reduction.centralSection K n t * x) = φ₁ x) :
    ∀ Ψ ∈ GJMatrix.matrixSchwartzBruhat K n, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (GJGlobal.zetaIntegrand Ψ (fun g ↦ GJGlobal.matrixCoeff μ φ₁ φ₂ g⁻¹) s) ν := by
  intro Ψ hΨ
  have h3 := GJMatrix.adelicMatrixFourier_mem (GJMatrix.adelicMatrixFourier_mem
    (GJMatrix.adelicMatrixFourier_mem hΨ))
  obtain ⟨σ₀, Λ, Λ', _, _, _, hZ', _⟩ := GJGlobal.globalZeta_entire_functionalEquation hn μ ν h₁ h₂ hA h3
  refine ⟨σ₀, fun s hs ↦ ?_⟩
  have := (hZ' s hs).1
  rwa [adelicMatrixFourier_four hΨ] at this

end Pair

section Unramified

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def dualPartialL (S : Finset (HeightOneSpectrum (𝓞 K))) {V : HeightOneSpectrum (𝓞 K) → Type*}
    [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
    LFunction (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (contragredient (π v)) s

theorem exists_unramified (hn : 2 ≤ n) (μ : Measure (Reduction.normOneGL K n))
    [μ.IsHaarMeasure] {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ AutomorphicForm.cuspForms K n)
    (h₂ : φ₂ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      φ₁ (Reduction.centralSection K n t * x) = φ₁ x)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (hξ : ∀ v, ξ v ∈ smoothVectors (π v))
    (hℓs : ∀ v : HeightOneSpectrum (𝓞 K), ℓ v ∈ smoothVectors (Representation.dual (π v)))
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (hℓK : ∀ v ∉ S, ℓ v ∈ fixedVectors (Representation.dual (π v)) (integralGL (v.adicCompletion K) n))
    (hirr : ∀ v ∉ S, (π v).IsIrreducible) (hadm : ∀ v ∉ S, IsAdmissible (π v))
    (z : HeightOneSpectrum (𝓞 K) → Fin n → ℂˣ)
    (hz : ∀ v ∉ S, Spherical.IsSatakeParameter (F := v.adicCompletion K) (π v) (localHaar n v) (z v))
    (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (hf : ∀ g, GJGlobal.matrixCoeff μ φ₁ φ₂ g = fi (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)
        (localComp n v g))
    (hf0 : ∃ g, GJGlobal.matrixCoeff μ φ₁ φ₂ g ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      (∀ v ∉ S, zetaIntegral (localHaar n v) (integralIndicator (v.adicCompletion K) n)
          (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s =
        LFunction (F := v.adicCompletion K) (π v) s) ∧
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
        LFunction (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (π v) s) (partialL S π s) ∧
      (∀ v ∉ S, zetaIntegral (localHaar n v) (integralIndicator (v.adicCompletion K) n)
          (fun g ↦ Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g⁻¹) s =
        LFunction (F := v.adicCompletion K) (contragredient (π v)) s) ∧
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
        LFunction (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (contragredient (π v)) s)
        (dualPartialL S π s) ∧
      (∀ v ∉ S, (∀ i, ‖(z v i : ℂ) * qs (v.adicCompletion K) s‖ < 1) ∧
        ∀ t : ℂ, LFunction (F := v.adicCompletion K) (π v) t =
          ∏ i, (1 - (z v i : ℂ) * qs (v.adicCompletion K) t)⁻¹) ∧
      (∀ v ∉ S, ∃ z' : Fin n → ℂˣ, (∀ i, ‖(z' i : ℂ) * qs (v.adicCompletion K) s‖ < 1) ∧
        ∀ t : ℂ, LFunction (F := v.adicCompletion K) (contragredient (π v)) t =
          ∏ i, (1 - (z' i : ℂ) * qs (v.adicCompletion K) t)⁻¹) := by
  have hn0 : 0 < n := by omega
  have : NeZero n := ⟨by omega⟩
  set ν : Measure (AdelicGLn.AdelicGL K n) := Measure.haar
  have hfc : Continuous (GJGlobal.matrixCoeff μ φ₁ φ₂) := continuous_globalMatrixCoeff hn0 μ h₁ h₂ hA
  obtain ⟨σp, hp⟩ := exists_sphericalIntegrable ν hfc (integrable_zetaIntegrand_coeff hn μ ν h₁ h₂ hA)
    S π ξ ℓ hξ hsph fi hf hf0
  obtain ⟨g₀, hg₀⟩ := hf0
  obtain ⟨σd, hd⟩ := exists_sphericalIntegrable ν (hfc.comp continuous_inv)
    (integrable_zetaIntegrand_coeff_inv hn μ ν h₁ h₂ hA) S (fun v ↦ Representation.dual (π v)) ℓ
    (fun v ↦ Module.Dual.eval ℂ (V v) (ξ v)) hℓs (fun v hv ↦ ⟨hℓK v hv, (hsph v hv).2⟩)
    (fun x ↦ fi x⁻¹) (inv_factorization π ξ ℓ fi hf) ⟨g₀⁻¹, by simpa using hg₀⟩
  refine ⟨max σp σd, fun s hs ↦ ?_⟩
  obtain ⟨hpi, hpm⟩ := hp s (lt_of_le_of_lt (le_max_left _ _) hs)
  obtain ⟨hdi, hdm⟩ := hd s (lt_of_le_of_lt (le_max_right _ _) hs)
  have hZp : ∀ v ∉ S, zetaIntegral (localHaar n v) (integralIndicator (v.adicCompletion K) n)
      (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s =
        LFunction (F := v.adicCompletion K) (π v) s := by
    intro v hv
    have := hirr v hv
    obtain ⟨-, heq⟩ := zetaIntegral_sphericalCoeff_of_integrable (localHaar n v) (hz v hv)
      (hsph v hv).1 (hsph v hv).2 (hpi v hv)
    have hK : fixedVectors (π v) (integralGL (v.adicCompletion K) n) ≠ ⊥ := by
      intro h
      have hmem := (hsph v hv).1
      rw [h, Submodule.mem_bot] at hmem
      have := (hsph v hv).2
      rw [hmem, map_zero] at this
      exact zero_ne_one this
    rw [heq, measureReal_def, localHaar_integralGL, ENNReal.toReal_one, Complex.ofReal_one, one_mul,
      LFunction_eq_prod_of_isSatakeParameter (hadm v hv) hK (localHaar n v) (hz v hv) s]
  have hZd : ∀ v ∉ S, zetaIntegral (localHaar n v) (integralIndicator (v.adicCompletion K) n)
      (fun g ↦ Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g⁻¹) s =
        LFunction (F := v.adicCompletion K) (contragredient (π v)) s := by
    intro v hv
    have := hirr v hv
    rw [zetaIntegral_inv_sphericalCoeff_of_integrable (π v) (hadm v hv) (localHaar n v) (hℓK v hv)
      (hsph v hv).2 (hdi v hv), measureReal_def, localHaar_integralGL, ENNReal.toReal_one,
      Complex.ofReal_one, one_mul]
  have hbp : ∀ v ∉ S, (∀ i, ‖(z v i : ℂ) * qs (v.adicCompletion K) s‖ < 1) ∧
      ∀ t : ℂ, LFunction (F := v.adicCompletion K) (π v) t =
        ∏ i, (1 - (z v i : ℂ) * qs (v.adicCompletion K) t)⁻¹ := by
    intro v hv
    have := hirr v hv
    obtain ⟨hw, -⟩ := zetaIntegral_sphericalCoeff_of_integrable (localHaar n v) (hz v hv)
      (hsph v hv).1 (hsph v hv).2 (hpi v hv)
    have hK : fixedVectors (π v) (integralGL (v.adicCompletion K) n) ≠ ⊥ := by
      intro h
      have hmem := (hsph v hv).1
      rw [h, Submodule.mem_bot] at hmem
      have := (hsph v hv).2
      rw [hmem, map_zero] at this
      exact zero_ne_one this
    exact ⟨hw, fun t ↦ LFunction_eq_prod_of_isSatakeParameter (hadm v hv) hK (localHaar n v) (hz v hv) t⟩
  have hbd : ∀ v ∉ S, ∃ z' : Fin n → ℂˣ, (∀ i, ‖(z' i : ℂ) * qs (v.adicCompletion K) s‖ < 1) ∧
      ∀ t : ℂ, LFunction (F := v.adicCompletion K) (contragredient (π v)) t =
        ∏ i, (1 - (z' i : ℂ) * qs (v.adicCompletion K) t)⁻¹ := by
    intro v hv
    have := hirr v hv
    obtain ⟨z', -, hw, hL, -⟩ := zetaIntegral_inv_sphericalCoeff_of_integrable' (π v) (hadm v hv)
      (localHaar n v) (hℓK v hv) (hsph v hv).2 (hdi v hv)
    exact ⟨z', hw, hL⟩
  refine ⟨hZp, ?_, hZd, ?_, hbp, hbd⟩
  · have h := hpm.hasProd
    have heq : (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦ zetaIntegral (localHaar n (v : HeightOneSpectrum (𝓞 K)))
        (integralIndicator ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) n)
        (Parabolic.matrixCoeff (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (π v) (ξ v) (ℓ v)) s) =
        fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
          LFunction (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (π v) s :=
      funext fun v ↦ hZp v.1 v.2
    rw [heq] at h
    exact h
  · have h := hdm.hasProd
    have heq : (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦ zetaIntegral (localHaar n (v : HeightOneSpectrum (𝓞 K)))
        (integralIndicator ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) n)
        (Parabolic.matrixCoeff (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K)
          (Representation.dual (π v)) (ℓ v) (Module.Dual.eval ℂ (V v) (ξ v))) s) =
        fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
          LFunction (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (contragredient (π v)) s :=
      funext fun v ↦ hZd v.1 v.2
    rw [heq] at h
    exact h

end Unramified

section Converges

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

end Converges

section Helpers

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem zetaIntegrand_smul (c : ℂ) (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ)
    (f : AdelicGLn.AdelicGL K n → ℂ) (s : ℂ) :
    GJGlobal.zetaIntegrand (c • Φ) f s = fun g ↦ c * GJGlobal.zetaIntegrand Φ f s g := by
  funext g
  simp only [GJGlobal.zetaIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem factor_nonvanishing {f : AdelicGLn.AdelicGL K n → ℂ} (hfc : Continuous f)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v))
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (hf : ∀ g, f g = fi (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)
        (localComp n v g))
    {g₀ : AdelicGLn.AdelicGL K n} (hg₀ : f g₀ ≠ 0) :
    Continuous fi ∧ fi (archComp K n g₀) ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀) ≠ 0 := by
  set c₀ := ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀) with hc₀
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀)).Finite := by
    refine ((finite_setOf_not_mem g₀).union S.finite_toSet).subset fun v hv ↦ ?_
    by_contra hc
    simp only [mem_union, Finset.mem_coe, not_or] at hc
    have hK : localComp n v g₀ ∈ integralGL (v.adicCompletion K) n := by
      by_contra h
      exact hc.1 h
    apply hv
    show ℓ v (π v (localComp n v g₀) (ξ v)) = 1
    rw [(hsph v hc.2).1 _ hK, (hsph v hc.2).2]
  rw [hf g₀] at hg₀
  have hfi0 : fi (archComp K n g₀) ≠ 0 := left_ne_zero_of_mul hg₀
  have hc₀0 : c₀ ≠ 0 := right_ne_zero_of_mul hg₀
  refine ⟨?_, hfi0, fun v h ↦ hc₀0 (finprod_eq_zero _ v h hsupp)⟩
  have key : ∀ x, fi x = f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) / c₀ := by
    intro x
    have : f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) = fi x * c₀ := by
      rw [hf, archComp_prodEquiv_symm]
      simp_rw [localComp_prodEquiv_symm]
      rfl
    rw [this, mul_div_cancel_right₀ _ hc₀0]
  have hc : Continuous fun x ↦ f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) / c₀ :=
    (hfc.comp ((AdelicGLn.prodEquiv K n).symm.continuous.comp
      (continuous_id.prodMk continuous_const))).div_const c₀
  exact hc.congr fun x ↦ (key x).symm

end Helpers

section Arch

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

end Arch

section NonVanishing

theorem ne_zero_of_hasProd_inv_prod {ι : Type*} {m : ℕ} {L : ι → ℂ} {P : ℂ} (hP : HasProd L P)
    (w : ι → Fin m → ℂ) (hL : ∀ v, L v = ∏ i, (1 - w v i)⁻¹) {b : ι → ℝ} (hb : Summable b)
    (hw : ∀ v i, ‖w v i‖ ≤ b v) (hw1 : ∀ v i, ‖w v i‖ < 1) : P ≠ 0 := by
  set a : ι → ℂ := fun v ↦ ∏ i, (1 + -w v i) - 1 with ha
  have hbnd : ∀ v, ‖a v‖ ≤ Real.exp (∑ i, ‖w v i‖) - 1 := fun v ↦ by
    have := Finset.norm_prod_one_add_sub_one_le Finset.univ (fun i ↦ -w v i)
    simpa [norm_neg] using this
  have hsum : Summable a := by
    refine Summable.of_norm_bounded_eventually ((hb.mul_left (m : ℝ)).mul_left 2) ?_
    have hev : ∀ᶠ v in Filter.cofinite, (m : ℝ) * b v ≤ 1 := by
      have : Tendsto (fun v ↦ (m : ℝ) * b v) Filter.cofinite (𝓝 0) := by
        simpa using hb.tendsto_cofinite_zero.const_mul (m : ℝ)
      exact this.eventually (ge_mem_nhds one_pos)
    filter_upwards [hev] with v hv
    have hS : ∑ i, ‖w v i‖ ≤ m * b v := by
      calc ∑ i, ‖w v i‖ ≤ ∑ _i : Fin m, b v := Finset.sum_le_sum fun i _ ↦ hw v i
        _ = m * b v := by simp
    have hS0 : 0 ≤ ∑ i, ‖w v i‖ := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
    calc ‖a v‖ ≤ Real.exp (∑ i, ‖w v i‖) - 1 := hbnd v
      _ ≤ |Real.exp (∑ i, ‖w v i‖) - 1| := le_abs_self _
      _ ≤ 2 * |∑ i, ‖w v i‖| := Real.abs_exp_sub_one_le (by rw [abs_of_nonneg hS0]; linarith)
      _ ≤ 2 * ((m : ℝ) * b v) := by rw [abs_of_nonneg hS0]; linarith
  have hM' : HasProd (fun v ↦ ∏ i, (1 - w v i)) (∏' v, (1 + a v)) := by
    have := (Complex.multipliable_one_add_of_summable hsum).hasProd
    convert this using 1
    funext v
    simp [ha, sub_eq_add_neg]
  have hne : ∀ v i, (1 - w v i) ≠ 0 := fun v i h ↦ by
    have h1 : w v i = 1 := by linear_combination -h
    have := hw1 v i
    rw [h1, norm_one] at this
    exact lt_irrefl _ this
  have h1 := hP.mul hM'
  have h2 : (fun v ↦ L v * ∏ i, (1 - w v i)) = fun _ ↦ (1 : ℂ) := by
    funext v
    rw [hL v, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ ↦ inv_mul_cancel₀ (hne v i)
  rw [h2] at h1
  intro hP0
  have := h1.unique hasProd_one
  rw [hP0, zero_mul] at this
  exact zero_ne_one this

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem summable_residueCard_inv_sq (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
      ((LocalField.residueCard ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) : ℝ) ^ (2 : ℝ))⁻¹ := by
  have h := GroundTheory.Global.summable_absNorm_rpow_inv (K := K) (σ := 2) (by norm_num)
  have hinj : Function.Injective fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
      (v : HeightOneSpectrum (𝓞 K)).asIdeal :=
    fun a b h ↦ Subtype.ext (HeightOneSpectrum.ext h)
  refine (h.comp_injective hinj).congr fun v ↦ ?_
  simp only [Function.comp_apply, GroundTheory.Global.residueCard_adicCompletion]

theorem norm_mul_qs_le {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (c : ℂ) {s₀ t : ℂ} (h : ‖c * qs F s₀‖ < 1) (ht : s₀.re + 2 ≤ t.re) :
    ‖c * qs F t‖ ≤ ((LocalField.residueCard F : ℝ) ^ (2 : ℝ))⁻¹ := by
  set q : ℝ := (LocalField.residueCard F : ℝ) with hq
  have hq1 : 1 < q := by
    rw [hq]
    exact_mod_cast LocalField.one_lt_residueCard (K := F)
  have hq0 : 0 < q := by linarith
  have hnorm : ∀ u : ℂ, ‖qs F u‖ = q ^ (-u.re) := fun u ↦ by
    rw [qs, show ((LocalField.residueCard F : ℕ) : ℂ) = ((q : ℝ) : ℂ) by rw [hq]; push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
  rw [norm_mul, hnorm] at h ⊢
  have hsplit : q ^ (-t.re) = q ^ (-s₀.re) * q ^ (-(t.re - s₀.re)) := by
    rw [← Real.rpow_add hq0]
    ring_nf
  have hle : q ^ (-(t.re - s₀.re)) ≤ q ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
  rw [hsplit, ← mul_assoc, Real.rpow_neg hq0.le 2] at *
  calc ‖c‖ * q ^ (-s₀.re) * q ^ (-(t.re - s₀.re)) ≤ 1 * (q ^ (2 : ℝ))⁻¹ := by
        refine mul_le_mul h.le hle (by positivity) zero_le_one
    _ = (q ^ (2 : ℝ))⁻¹ := one_mul _

theorem residueCard_inv_sq_lt_one (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : ((LocalField.residueCard F : ℝ) ^ (2 : ℝ))⁻¹ < 1 := by
  have hq1 : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard (K := F)
  exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hq1 two_pos)

end NonVanishing

section FE

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem tensor_hyps_fourier {S : Finset (HeightOneSpectrum (𝓞 K))} (hRS : ramifiedPlaces K ⊆ S)
    {Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ}
    (hS : ∀ v ∈ S, IsSchwartzBruhat (Φ v))
    (h0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n) :
    (∀ v ∈ S, IsSchwartzBruhat (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v))) ∧
      ∀ v ∉ S, GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v) =
        integralIndicator (v.adicCompletion K) n := by
  obtain ⟨h1, h2⟩ := localMatrixFourier_tensor_hyps S Φ hS h0
  refine ⟨fun v hv ↦ h1 v (Finset.mem_union_left _ hv), fun v hv ↦ h2 v ?_⟩
  rw [Finset.mem_union, not_or]
  exact ⟨hv, fun h ↦ hv (hRS h)⟩

end FE

end GJStandardL

end

end GroundTheory.Automorphic
