import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StIsotropicRank
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ShortIsotropic
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField
open scoped Matrix

namespace IsotropicRank

theorem hermForm_span_eq_zero {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {N : ℕ}
    (H : Matrix (Fin N) (Fin N) Em) (S : Set (Fin N → Em)) (hS : ∀ v ∈ S, ∀ w ∈ S, hermForm Em H v w = 0) :
    ∀ x ∈ Submodule.span Em S, ∀ y ∈ Submodule.span Em S, hermForm Em H x y = 0 := by
  have h1 : ∀ v ∈ S, ∀ y ∈ Submodule.span Em S, hermForm Em H v y = 0 := by
    intro v hv y hy
    induction hy using Submodule.span_induction with
    | mem w hw => exact hS v hv w hw
    | zero => exact ShortIsotropic.hermForm_zero_right H v
    | add y y' _ _ h h' => rw [ShortIsotropic.hermForm_add_right, h, h', add_zero]
    | smul c y _ h => rw [ShortIsotropic.hermForm_smul_right, h, mul_zero]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem v hv => exact h1 v hv y hy
  | zero => exact ShortIsotropic.hermForm_zero_left H y
  | add x x' _ _ h h' => rw [ShortIsotropic.hermForm_add_left, h, h', add_zero]
  | smul c x _ h => rw [ShortIsotropic.hermForm_smul_left, h, mul_zero]

theorem nonempty_cmType {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}
    (A : HermDatum Em Ψ N j) : Nonempty Ψ := by
  obtain ⟨σ⟩ : Nonempty (Em →+* ℂ) := inferInstance
  by_cases h : ∃ τ, A.emb τ = σ
  · exact ⟨h.choose⟩
  · obtain ⟨τ, _⟩ := not_not.mp (mt (A.cmType σ).mpr h)
    exact ⟨τ⟩

theorem mulVec_map_injective {K L : Type*} [Field K] [Field L] {n r : ℕ} (σ : K →+* L)
    (M : Matrix (Fin n) (Fin r) K) (hM : Function.Injective M.mulVec) : Function.Injective (M.map σ).mulVec := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin M)
    (LinearMap.ker_eq_bot.mpr hM)
  have hL : LinearMap.toMatrix' g * M = 1 := by
    have hM' : LinearMap.toMatrix' (Matrix.mulVecLin M) = M := by
      rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    rw [← hM', ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hLσ : (LinearMap.toMatrix' g).map σ * M.map σ = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro c d hcd
  have h := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hcd
  simpa only [Matrix.mulVec_mulVec, hLσ, Matrix.one_mulVec] using h

theorem proof : IsotropicRank.Statement := by
  intro Em _ _ _ Ψ _ N j A S hS
  obtain ⟨τ⟩ := nonempty_cmType A
  obtain ⟨P, hPu, hP⟩ := A.signature τ
  set U := Submodule.span Em S
  set r := Module.finrank Em U
  let b := Module.finBasis Em U
  let M : Matrix (Fin N) (Fin r) Em := Matrix.of fun i a => (b a : Fin N → Em) i
  have hMv : ∀ c, M *ᵥ c = ∑ a, c a • (b a : Fin N → Em) := by
    intro c
    ext i
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hli : LinearIndependent Em fun a => (b a : Fin N → Em) :=
    b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hM : Function.Injective M.mulVec := by
    intro c d hcd
    have h0 : ∑ a, (c - d) a • (b a : Fin N → Em) = 0 := by
      rw [← hMv, Matrix.mulVec_sub]
      exact sub_eq_zero.mpr hcd
    funext a
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 a)
  have hz : ∀ a a', hermForm Em A.H (b a) (b a') = 0 := fun a a' =>
    hermForm_span_eq_zero A.H S hS _ (b a).2 _ (b a').2
  set Mτ := M.map (A.emb τ)
  set Hτ := A.H.map (A.emb τ)
  have hG : Mτᴴ * Hτ * Mτ = 0 := by
    ext a a'
    have h := ShortIsotropic.emb_hermForm (A.emb τ) A.H (b a) (b a')
    rw [hz a a', map_zero] at h
    rw [Matrix.zero_apply, h]
    simp only [Mτ, Hτ, M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply,
      dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hq : ∀ c, star (Mτ *ᵥ c) ⬝ᵥ (Hτ *ᵥ (Mτ *ᵥ c)) = 0 := by
    intro c
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hG, Matrix.zero_mulVec, dotProduct_zero]
  let g : Fin (N - j) → Fin N := fun k => ⟨j + k, by omega⟩
  let f : (Fin r → ℂ) →ₗ[ℂ] (Fin (N - j) → ℂ) := LinearMap.funLeft ℂ ℂ g ∘ₗ Matrix.mulVecLin (P⁻¹ * Mτ)
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun c hc => ?_
    set y := P⁻¹ *ᵥ (Mτ *ᵥ c)
    have hy0 : ∀ a : Fin N, j ≤ (a : ℕ) → y a = 0 := by
      intro a ha
      have h := congrFun hc ⟨a - j, by omega⟩
      simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, Matrix.mulVecLin_apply,
        ← Matrix.mulVec_mulVec, Pi.zero_apply] at h
      have hg : g ⟨a - j, by omega⟩ = a := Fin.ext (by simp only [g]; omega)
      rwa [hg] at h
    have hw := ShortIsotropic.form_witt hP (Mτ *ᵥ c) (Mτ *ᵥ c)
    rw [hq c] at hw
    have hsum : ∑ a, Complex.normSq (y a) = 0 := by
      have h := congrArg Complex.re hw.symm
      simp only [signMat, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.re_sum,
        Complex.zero_re] at h
      rw [← h]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : (a : ℕ) < j
      · simp only [ha, if_true, one_mul, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
          Complex.normSq_apply]
        ring
      · have h0 : ((P⁻¹ * Mτ) *ᵥ c) a = 0 := by
          rw [← Matrix.mulVec_mulVec]
          exact hy0 a (by omega)
        have h1 : y a = 0 := hy0 a (by omega)
        simp [ha, h0, h1]
    have hy : y = 0 := by
      funext a
      have h := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => Complex.normSq_nonneg (y a)).mp hsum a
        (Finset.mem_univ a)
      exact Complex.normSq_eq_zero.mp h
    have hMc : Mτ *ᵥ c = 0 := by
      have : Mτ *ᵥ c = P *ᵥ y := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
      rw [this, hy, Matrix.mulVec_zero]
    exact mulVec_map_injective (A.emb τ) M hM (hMc.trans (Matrix.mulVec_zero Mτ).symm)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fin_fun] using this

end IsotropicRank

end GroundTheory.Heights₂.Heights.NineStatements
