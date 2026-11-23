import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

open GroundTheory.Automorphic.FourierWhittaker in

private theorem isY_blockGL {K : Type} [Field K] {n k : ℕ} (hk : k < n) (γ : GL (Fin k) K) :
    IsY (n - 1) (blockGL hk.le γ : GL (Fin n) K).val := by
  intro i hi
  have hik : ¬ i.val < k := by omega
  refine ⟨?_, fun j hj => ?_⟩
  · rw [coe_blockGL, blockMat_apply, dif_neg hik, if_pos rfl]
  · rw [coe_blockGL, blockMat_apply, dif_neg hik, if_neg hj.ne']

open GroundTheory.Automorphic.FourierWhittaker in
open scoped NumberField.AdeleRing in

private theorem step {K : Type} [Field K] [NumberField K] {n : ℕ} {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    (hc : Continuous ϕ) (hl : IsLeftInvariant ϕ) (hcusp : AutomorphicForm.IsCuspidal ϕ)
    {V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hV : ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g) {k : ℕ} (hk0 : 0 < k) (hk : k < n)
    (g : AdelicGLn.AdelicGL K n)
    (h0 : ∀ γ : GL (Fin k) K, partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le γ) * g) = 0) :
    partialCoeff ϕ (k + 1) g = 0 := by
  classical
  obtain ⟨δ, hδ, hδV⟩ := exists_integer_colGL_mem (n := n) k V (AdelicGLn.prodEquiv K n g).2
  have hδK : (algebraMap (𝓞 K) K δ) ≠ 0 := by
    simpa using (RingOfIntegers.coe_ne_zero_iff).2 hδ
  set u : Kˣ := Units.mk0 _ hδK
  set D := AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) with hD
  have hconj : ∀ w : Fin k → 𝔸[K], colGL k w * D =
      D * colGL k (fun i => algebraMap K 𝔸[K] u * w i) := by
    intro w
    simp only [D]
    rw [diagonal_blockGL, colGL_mul_blockGL hk, mulVec_map_inv, ← map_inv, inv_inv, coe_scalarGL,
      matVec_scalar]
  set F : (Fin k → 𝔸[K]) → ℂ := fun x => partialCoeff ϕ (k + 1) (colGL k x * (D * g))
  have hip : IsIntegralPeriodic F := by
    refine ⟨(continuous_partialCoeff hc _).comp ((continuous_colGL k).mul continuous_const),
      fun ξ hξ x => ?_, fun x z hz => ?_⟩
    · obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
      simp only [F]
      rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL hl hk]
    · have e1 : (fun i => algebraMap K 𝔸[K] (u : K) * GroundTheory.Global.finiteAdeleInr (z i)) =
          fun i => GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K)
            (algebraMap (𝓞 K) K δ) * z i) := by
        funext i; rw [GroundTheory.Global.algebraMap_mul_finiteAdeleInr]; rfl
      change partialCoeff ϕ (k + 1)
          (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) * (D * g)) =
        partialCoeff ϕ (k + 1) (colGL k x * (D * g))
      rw [colGL_add, mul_assoc (colGL k x),
        ← mul_assoc (colGL k fun i => GroundTheory.Global.finiteAdeleInr (z i)), hconj, e1,
        colGL_finiteAdeleInr, mul_assoc D, finEmb_mul_eq, ← mul_assoc,
        ← mul_assoc, partialCoeff_mul_finEmb hV _ _ (hδV z hz), mul_assoc]
  have hcoeff : vecCoeff F = 0 := by
    funext ξ
    by_cases hξ : ξ = 0
    · rw [hξ]
      exact vecCoeff_zero_of_isCuspidal hc hl hcusp hk0 hk (D * g)
    · have h1 := partialCoeff_diagonal_blockGL_eq_vecCoeff hl hk (rowCompletion ξ) (D * g)
      rw [vecMul_rowCompletion hξ] at h1
      refine h1.symm.trans ?_
      rw [hD, ← mul_assoc, ← map_mul, ← map_mul]
      exact h0 _
  have H := hip.hasSum_vecCoeff (hcoeff ▸ summable_zero) 0
  simp only [hcoeff, Pi.zero_apply, zero_mul] at H
  have hF0 : F 0 = 0 := (hasSum_zero.unique H).symm
  rw [← partialCoeff_succ_diagonal_blockGL hl hk (scalarGL k u⁻¹) g]
  change partialCoeff ϕ (k + 1) (D * g) = 0
  simpa [F, colGL_zero] using hF0

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.Smo.injP :
    UpperTheory.V.Af.Smo.InjP := by
  intro E _ _ n hn f hf X hX hW
  obtain ⟨V, hV⟩ := hf.level
  rw [← Fb.finEmb_eq] at hV
  have key : ∀ k, k < n → ∀ g ∈ X, partialCoeff f (k + 1) g = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ g hg
      exact (whittaker_eq_partialCoeff hf.cont hn g).symm.trans (hW g hg)
    | succ m ih =>
      intro hm g hg
      exact step hf.cont hf.left hf.cusp hV (Nat.succ_pos m) hm g fun γ =>
        ih (by omega) _ (hX _ (isY_blockGL hm γ) g hg)
  intro g hg
  have := key (n - 1) (by omega) g hg
  rwa [Nat.sub_add_cancel hn, partialCoeff_self] at this
