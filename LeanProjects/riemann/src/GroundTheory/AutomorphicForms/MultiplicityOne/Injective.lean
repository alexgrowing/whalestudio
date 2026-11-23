import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open AutomorphicForm FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem partialCoeff_succ_eq_zero {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hc : Continuous ϕ)
    (hl : IsLeftInvariant ϕ) (hcusp : IsCuspidal ϕ) {V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hV : ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g) {k : ℕ} (hk0 : 0 < k) (hk : k < n)
    (h0 : ∀ g, partialCoeff ϕ k g = 0) (g : AdelicGLn.AdelicGL K n) :
    partialCoeff ϕ (k + 1) g = 0 := by
  classical
  obtain ⟨δ, hδ, hδV⟩ := exists_integer_colGL_mem (n := n) k V (AdelicGLn.prodEquiv K n g).2
  have hδK : (algebraMap (𝓞 K) K δ) ≠ 0 := by
    simpa using (RingOfIntegers.coe_ne_zero_iff).2 hδ
  set u : Kˣ := Units.mk0 _ hδK
  set D := AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹))
  have hconj : ∀ w : Fin k → 𝔸[K], colGL k w * D =
      D * colGL k (fun i => algebraMap K 𝔸[K] u * w i) := by
    intro w
    simp only [D]
    rw [diagonal_blockGL, colGL_mul_blockGL hk, mulVec_map_inv, ← map_inv, inv_inv, coe_scalarGL,
      matVec_scalar]
  have hfin : ∀ (x : Fin k → 𝔸[K]) (z : Fin k → FiniteAdeleRing (𝓞 K) K),
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        partialCoeff ϕ (k + 1) (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) * (D * g)) =
          partialCoeff ϕ (k + 1) (colGL k x * (D * g)) := by
    intro x z hz
    have e1 : (fun i => algebraMap K 𝔸[K] (u : K) * GroundTheory.Global.finiteAdeleInr (z i)) =
        fun i => GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K)
          (algebraMap (𝓞 K) K δ) * z i) := by
      funext i; rw [GroundTheory.Global.algebraMap_mul_finiteAdeleInr]; rfl
    rw [colGL_add, mul_assoc (colGL k x),
      ← mul_assoc (colGL k fun i => GroundTheory.Global.finiteAdeleInr (z i)), hconj, e1,
      colGL_finiteAdeleInr, mul_assoc D, finEmb_mul_eq, ← mul_assoc,
      ← mul_assoc, partialCoeff_mul_finEmb hV _ _ (hδV z hz), mul_assoc]
  set F : (Fin k → 𝔸[K]) → ℂ := fun x => partialCoeff ϕ (k + 1) (colGL k x * (D * g))
  have hFc : Continuous F :=
    (continuous_partialCoeff hc _).comp ((continuous_colGL k).mul continuous_const)
  have hper : ∀ ξ ∈ vecLattice K (Fin k), ∀ x, F (ξ + x) = F x := by
    intro ξ hξ x
    obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
    simp only [F]
    rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL hl hk]
  have hip : IsIntegralPeriodic F := ⟨hFc, hper, fun x z hz => hfin x z hz⟩
  have hcoeff : ∀ ξ : Fin k → K, vecCoeff F ξ = 0 := by
    intro ξ
    by_cases hξ : ξ = 0
    · rw [hξ]
      exact vecCoeff_zero_of_isCuspidal hc hl hcusp hk0 hk (D * g)
    · have h1 := partialCoeff_diagonal_blockGL_eq_vecCoeff hl hk (rowCompletion ξ) (D * g)
      rw [vecMul_rowCompletion hξ] at h1
      rw [← h1]
      exact h0 _
  have hsum : Summable (vecCoeff F) := by
    have : vecCoeff F = 0 := funext hcoeff
    rw [this]
    exact summable_zero
  have H := hip.hasSum_vecCoeff hsum 0
  simp only [hcoeff, zero_mul] at H
  have hF0 : F 0 = 0 := (hasSum_zero.unique H).symm
  have hDg : partialCoeff ϕ (k + 1) (D * g) = 0 := by
    simpa [F, colGL_zero] using hF0
  rw [← partialCoeff_succ_diagonal_blockGL hl hk (scalarGL k u⁻¹) g]
  exact hDg

theorem eq_zero_of_whittaker_eq_zero {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hc : Continuous ϕ)
    (hl : IsLeftInvariant ϕ) (hcusp : IsCuspidal ϕ)
    (hV : ∃ V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n),
      ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g)
    (hW : ∀ g, whittaker ϕ g = 0) : ϕ = 0 := by
  obtain ⟨V, hV⟩ := hV
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    funext g
    rw [← partialCoeff_self ϕ, ← whittaker_eq_partialCoeff_zero hc g]
    exact hW g
  · have key : ∀ k, 0 < k → k ≤ n → ∀ g, partialCoeff ϕ k g = 0 := by
      intro k
      induction k with
      | zero => intro h; exact absurd h (lt_irrefl 0)
      | succ m ih =>
        intro _ hm g
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · rw [← whittaker_eq_partialCoeff hc hn g]
          exact hW g
        · exact partialCoeff_succ_eq_zero hc hl hcusp hV hm0 (by omega) (ih hm0 (by omega)) g
    funext g
    rw [← partialCoeff_self ϕ]
    exact key n hn le_rfl g

end MultiplicityOne

end

end GroundTheory.Automorphic
