import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameImplicitGraph
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HasStrictFDerivAtEval
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

namespace FrameImplicitGraph

variable {n : ℕ}

def polyDeriv (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
  ∑ l, eval (fun i => x i) (pderiv l p) • EuclideanSpace.proj l

theorem polyDeriv_apply (p : MvPolynomial (Fin n) ℂ) (x v : EuclideanSpace ℂ (Fin n)) :
    polyDeriv p x v = ∑ l, eval (fun i => x i) (pderiv l p) * v l := by
  simp [polyDeriv]

theorem hasStrictFDerivAt_eval (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    HasStrictFDerivAt (fun y : EuclideanSpace ℂ (Fin n) => eval (fun i => y i) p) (polyDeriv p x) x :=
  _root_.UpperTheory.Reformulated.B.Qi29.hasStrictFDerivAt_eval p x

def projCLM (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) :=
  ContinuousLinearMap.pi fun i : I => innerSL ℂ (b i)

def phi (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    (I → ℂ) × ({j // j ∉ I} → ℂ) :=
  (frameProj b I x, fun k => eval (fun i => x i) (f k))

def phiDeriv (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ) :=
  (projCLM b I).prod (ContinuousLinearMap.pi fun k => polyDeriv (f k) x)

theorem hasStrictFDerivAt_phi (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    HasStrictFDerivAt (phi b I f) (phiDeriv b I f x) x :=
  (projCLM b I).hasStrictFDerivAt.prodMk (hasStrictFDerivAt_pi.2 fun k => hasStrictFDerivAt_eval (f k) x)

theorem phiDeriv_injective (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n))
    (hx : eval (fun i => x i) (frameJacobianDet b I f) ≠ 0) :
    Function.Injective (phiDeriv b I f x) := by
  refine (injective_iff_map_eq_zero (phiDeriv b I f x)).2 fun v hv => ?_
  set c : Fin n → ℂ := fun j => inner ℂ (b j) v with hc
  have h1 : ∀ i ∈ I, c i = 0 := fun i hi => by
    have := congrFun (congrArg Prod.fst hv) ⟨i, hi⟩
    simpa [phiDeriv, projCLM, c] using this
  have hvl : ∀ l, v l = ∑ j, c j * b j l := fun l => by
    have := congrArg (fun y : EuclideanSpace ℂ (Fin n) => y l) (b.sum_repr' v)
    simpa [c, smul_eq_mul] using this.symm
  have h2 : ∀ k, ∑ j, c j * eval (fun i => x i) (frameDeriv b j (f k)) = 0 := fun k => by
    have := congrFun (congrArg Prod.snd hv) k
    simp only [phiDeriv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply, polyDeriv_apply,
      Prod.snd_zero, Pi.zero_apply] at this
    rw [← this]
    simp only [frameDeriv, map_sum, map_mul, eval_C, hvl, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  let M : Matrix {j // j ∉ I} {j // j ∉ I} ℂ := Matrix.of fun k j => eval (fun i => x i) (frameDeriv b j (f k))
  have hM : M.det ≠ 0 := by
    have : eval (fun i => x i) (frameJacobianDet b I f) = M.det := by
      rw [frameJacobianDet, RingHom.map_det]
      rfl
    rwa [← this]
  have hMc : M.mulVec (fun j => c j) = 0 := by
    funext k
    rw [Pi.zero_apply, ← h2 k, ← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ I)]
    simp [M, Matrix.mulVec, dotProduct, h1, mul_comm]
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hM hMc
  have hc0 : ∀ j, c j = 0 := fun j => by
    by_cases hj : j ∈ I
    · exact h1 j hj
    · exact congrFun h3 ⟨j, hj⟩
  have hv' : v = ∑ j, c j • b j := (b.sum_repr' v).symm
  rw [hv']
  simp [hc0]

theorem finrank_eq (I : Finset (Fin n)) :
    Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Module.finrank ℂ ((I → ℂ) × ({j // j ∉ I} → ℂ)) := by
  have h1 : Fintype.card {j // j ∉ I} = n - I.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    simp
  have h2 : I.card ≤ n := by simpa using I.card_le_univ
  simp only [finrank_euclideanSpace, Fintype.card_fin, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    h1, Fintype.card_coe]
  omega

theorem phiDeriv_equiv (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n))
    (hx : eval (fun i => x i) (frameJacobianDet b I f) ≠ 0) :
    ∃ e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ),
      (e : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ)) = phiDeriv b I f x := by
  refine ⟨(LinearMap.linearEquivOfInjective (phiDeriv b I f x : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] _)
    (phiDeriv_injective b I f x hx) (finrank_eq I)).toContinuousLinearEquiv, ?_⟩
  ext v
  all_goals simp [LinearMap.linearEquivOfInjective_apply]

theorem continuous_eval (p : MvPolynomial (Fin n) ℂ) :
    Continuous fun y : EuclideanSpace ℂ (Fin n) => eval (fun i => y i) p :=
  continuous_iff_continuousAt.2 fun x => (hasStrictFDerivAt_eval p x).continuousAt

theorem proof : FrameImplicitGraph.Statement := by
  intro n b I f z hz hdet U hU hzU
  obtain ⟨e0, he0⟩ := phiDeriv_equiv b I f z hdet
  have hs : HasStrictFDerivAt (phi b I f)
      (e0 : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ)) z :=
    he0 ▸ hasStrictFDerivAt_phi b I f z
  let e := hs.toOpenPartialHomeomorph (phi b I f)
  have hecoe : (e : EuclideanSpace ℂ (Fin n) → (I → ℂ) × ({j // j ∉ I} → ℂ)) = phi b I f := rfl
  let W := {x : EuclideanSpace ℂ (Fin n) | eval (fun i => x i) (frameJacobianDet b I f) ≠ 0}
  have hW : IsOpen W := isOpen_ne_fun (continuous_eval _) continuous_const
  let V := e.source ∩ U ∩ W
  have hV : IsOpen V := (e.open_source.inter hU).inter hW
  let ι : (I → ℂ) → (I → ℂ) × ({j // j ∉ I} → ℂ) := fun w => (w, 0)
  have hι : Continuous ι := continuous_id.prodMk continuous_const
  refine ⟨ι ⁻¹' (e.target ∩ e.symm ⁻¹' V), V, fun w => e.symm (ι w),
    (e.continuousOn_symm.isOpen_inter_preimage e.open_target hV).preimage hι, hV,
    ⟨⟨hs.mem_toOpenPartialHomeomorph_source, hzU⟩, hdet⟩, fun x hx => hx.1.2, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨ex, hex⟩ := phiDeriv_equiv b I f _ hw.2.2
    have hd : HasFDerivAt e (ex : EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ))
        (e.symm (ι w)) := by
      rw [hecoe, hex]
      exact (hasStrictFDerivAt_phi b I f _).hasFDerivAt
    have hιd : HasFDerivAt ι ((ContinuousLinearMap.id ℂ (I → ℂ)).prod 0) w :=
      (hasFDerivAt_id w).prodMk (hasFDerivAt_const 0 w)
    exact ((e.hasFDerivAt_symm hw.1 hd).comp w hιd).differentiableAt.differentiableWithinAt
  · intro w hw
    have := congrArg Prod.fst (e.right_inv hw.1)
    rw [hecoe] at this
    exact this
  · ext x
    constructor
    · rintro ⟨hx0, hxV⟩
      have hex : e x = ι (frameProj b I x) := by
        rw [hecoe]
        exact Prod.ext rfl (funext hx0)
      refine ⟨frameProj b I x, ⟨?_, ?_⟩, ?_⟩
      · rw [← hex]; exact e.map_source hxV.1.1
      · show e.symm (ι (frameProj b I x)) ∈ V
        rw [← hex, e.left_inv hxV.1.1]; exact hxV
      · show e.symm (ι (frameProj b I x)) = x
        rw [← hex, e.left_inv hxV.1.1]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨fun k => ?_, hw.2⟩
      have := congrArg (fun p => p.2 k) (e.right_inv hw.1)
      rw [hecoe] at this
      exact this

end FrameImplicitGraph

end

end GroundTheory.Heights₂.Heights
