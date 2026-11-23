import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleMultiHomogGrad
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def toFn (P : Ideal (MRing ι)) : MRing ι →+* FnField P :=
  (algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ker_toFn (P : Ideal (MRing ι)) : RingHom.ker (toFn P) = P := by
  rw [toFn, RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _), Ideal.mk_ker]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem evalAt_genPt (P : Ideal (MRing ι)) (f : MRing ι) : evalAt (genPt P) f = toFn P f := by
  rw [evalAt, eval_map]
  have h : eval₂Hom (Int.castRingHom (FnField P)) (genPt P) = toFn P :=
    MvPolynomial.ringHom_ext (fun z => by simp) (fun p => by simp [genPt, toFn])
  exact RingHom.congr_fun h f

def genMap (P : Ideal (MRing ι)) {N1 : ℕ} {S : Type} [Fintype S] (v : S → Fin N1 → FnField P) :
    MRing (PBlk ι N1) →+* MvPolynomial S (FnField P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (genPt P ⟨k, i⟩)
    | ⟨.inr _, j⟩ => ∑ s, C (v s j) * X s

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ker_genMap_le (P : Ideal (MRing ι)) {N1 : ℕ} {S S' : Type} [Fintype S] [Fintype S']
    (v : S → Fin N1 → FnField P) (v' : S' → Fin N1 → FnField P)
    (h : ∀ s', v' s' ∈ Submodule.span (FnField P) (Set.range v)) :
    RingHom.ker (genMap P v) ≤ RingHom.ker (genMap P v') := by
  choose G hG using fun s' => (Submodule.mem_span_range_iff_exists_fun (FnField P)).mp (h s')
  let σ : MvPolynomial S (FnField P) →+* MvPolynomial S' (FnField P) :=
    (aeval fun s => ∑ s', C (G s' s) * X s' : MvPolynomial S (FnField P) →ₐ[FnField P] _).toRingHom
  have key : genMap P v' = σ.comp (genMap P v) := by
    refine MvPolynomial.ringHom_ext (fun z => by simp) ?_
    rintro ⟨k | u, i⟩
    · simp [genMap, σ]
    · change Fin N1 at i
      simp only [genMap, RingHom.coe_comp, Function.comp_apply, eval₂Hom_X', map_sum, map_mul, σ,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, aeval_X, algebraMap_eq]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s' _ => ?_
      have hGi := congrFun (hG s') i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hGi
      rw [← hGi, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_mul]
      ring
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  rw [key, RingHom.comp_apply, hf, map_zero]

omit [∀ k, Fintype (ι k)] in

theorem exists_homog_span [DecidableEq K] (P : Ideal (MRing ι)) [P.IsPrime]
    (hP : ∀ f ∈ P, ∀ b, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f ∈ P)
    {t N1 n : ℕ} (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (hc : ∀ r j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (c r j) m)
    (B : Fin n → Fin N1 → FnField P)
    (hB : ∀ a, B a ∈ LinearMap.ker (Matrix.mulVecLin (Matrix.of fun r j => evalAt (genPt P) (c r j)))) :
    ∃ (S : Type) (_ : Fintype S) (V : S → Fin N1 → MRing ι) (γ : S → K → ℕ),
      (∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s)) ∧
      (∀ s, (fun j => toFn P (V s j)) ∈
        LinearMap.ker (Matrix.mulVecLin (Matrix.of fun r j => evalAt (genPt P) (c r j)))) ∧
      ∀ a, B a ∈ Submodule.span (FnField P) (Set.range fun s j => toFn P (V s j)) := by
  classical
  set w := NumbersDVR.blockWeight ι
  choose δ hδ using fun a => IsLocalization.exist_integer_multiples (nonZeroDivisors (MRing ι ⧸ P))
    (Finset.univ : Finset (Fin N1)) (B a)
  have hlift : ∀ a j, ∃ L : MRing ι, toFn P L = (δ a : MRing ι ⧸ P) • B a j := by
    intro a j
    obtain ⟨r, hr⟩ := hδ a j (Finset.mem_univ j)
    obtain ⟨L, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact ⟨L, hr⟩
  choose L hL using hlift
  have hL' : ∀ a j, toFn P (L a j) = algebraMap (MRing ι ⧸ P) (FnField P) (δ a) * B a j :=
    fun a j => by rw [hL a j]; exact Algebra.smul_def (δ a : MRing ι ⧸ P) (B a j)
  have hrow : ∀ a r, ∑ j, c r j * L a j ∈ P := by
    intro a r
    have h0 : ∑ j, evalAt (genPt P) (c r j) * B a j = 0 := by
      have := congrFun (LinearMap.mem_ker.mp (hB a)) r
      simpa [Matrix.mulVec, dotProduct] using this
    rw [← ker_toFn P, RingHom.mem_ker, map_sum]
    simp only [map_mul, hL', ← evalAt_genPt]
    rw [show ∑ j, evalAt (genPt P) (c r j) * (algebraMap (MRing ι ⧸ P) (FnField P) (δ a) * B a j) =
        algebraMap (MRing ι ⧸ P) (FnField P) (δ a) * ∑ j, evalAt (genPt P) (c r j) * B a j by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring]
    rw [h0, mul_zero]
  let D : Finset (K → ℕ) := Finset.univ.biUnion fun aj : Fin n × Fin N1 =>
    (L aj.1 aj.2).support.image (Finsupp.weight w)
  have hsum : ∀ a j, ∑ γ ∈ D, weightedHomogeneousComponent w γ (L a j) = L a j := by
    intro a j
    conv_rhs => rw [← sum_weightedHomogeneousComponent w (L a j)]
    refine (finsum_eq_sum_of_support_subset _ fun γ hγ => ?_).symm
    rw [Function.mem_support] at hγ
    by_contra hD
    refine hγ (weightedHomogeneousComponent_eq_zero' γ (L a j) fun d hd hdγ => hD ?_)
    exact Finset.mem_biUnion.mpr ⟨(a, j), Finset.mem_univ _, Finset.mem_image.mpr ⟨d, hd, hdγ⟩⟩
  refine ⟨Fin n × D, inferInstance, fun s j => weightedHomogeneousComponent w s.2 (L s.1 j), fun s => s.2,
    fun s j => weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_, ?_⟩
  · intro s
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext r
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, evalAt_genPt, ← map_mul,
      ← map_sum]
    rw [← RingHom.mem_ker, ker_toFn]
    rw [show ∑ j, c r j * weightedHomogeneousComponent w s.2 (L s.1 j) =
        weightedHomogeneousComponent w (s.2 + m) (∑ j, c r j * L s.1 j) by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => (weightedHomogeneousComponent_mul_of_left (hc r j) _ _).symm]
    exact hP _ (hrow s.1 r) _
  · intro a
    have hδ0 : algebraMap (MRing ι ⧸ P) (FnField P) (δ a) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (δ a).2
    have hBa : B a = (algebraMap (MRing ι ⧸ P) (FnField P) (δ a))⁻¹ •
        ∑ γ : D, fun j => toFn P (weightedHomogeneousComponent w γ (L a j)) := by
      funext j
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← map_sum]
      rw [Finset.sum_coe_sort D (fun γ => weightedHomogeneousComponent w γ (L a j)), hsum, hL',
        ← mul_assoc, inv_mul_cancel₀ hδ0, one_mul]
    rw [hBa]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun γ _ => Submodule.subset_span ⟨(a, γ), rfl⟩)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
