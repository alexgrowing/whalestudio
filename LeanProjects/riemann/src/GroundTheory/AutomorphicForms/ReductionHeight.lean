import Mathlib
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

section Euclid

variable {E : Type*} [NormedField E] {n : ℕ}

def euclidNorm (y : Fin n → E) : ℝ := √(∑ i, ‖y i‖ ^ 2)

theorem euclidNorm_nonneg (y : Fin n → E) : 0 ≤ euclidNorm y := Real.sqrt_nonneg _

theorem norm_le_euclidNorm (y : Fin n → E) (i : Fin n) : ‖y i‖ ≤ euclidNorm y := by
  rw [euclidNorm]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem euclidNorm_smul (c : E) (y : Fin n → E) : euclidNorm (c • y) = ‖c‖ * euclidNorm y := by
  simp only [euclidNorm, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem euclidNorm_le_sqrt_mul (y : Fin n → E) : euclidNorm y ≤ √n * ‖y‖ := by
  rw [euclidNorm, ← Real.sqrt_sq (norm_nonneg y), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin n, ‖y‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm y i) 2
    _ = n * ‖y‖ ^ 2 := by simp

theorem norm_le_euclidNorm_pi (y : Fin n → E) : ‖y‖ ≤ euclidNorm y :=
  (pi_norm_le_iff_of_nonneg (euclidNorm_nonneg y)).2 fun i => norm_le_euclidNorm y i

theorem euclidNorm_pos {y : Fin n → E} (hy : y ≠ 0) : 0 < euclidNorm y :=
  lt_of_lt_of_le (norm_pos_iff.2 hy) (norm_le_euclidNorm_pi y)

theorem continuous_euclidNorm : Continuous (euclidNorm : (Fin n → E) → ℝ) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    (continuous_norm.comp (continuous_apply i)).pow 2)

end Euclid

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def infComp (w : InfinitePlace K) (y : Fin n → 𝔸[K]) : Fin n → w.Completion := fun i => (y i).1 w

def finComp (v : HeightOneSpectrum (𝓞 K)) (y : Fin n → 𝔸[K]) : Fin n → v.adicCompletion K :=
  fun i => (y i).2 v

def infAt (w : InfinitePlace K) (g : AdelicGLn.AdelicGL K n) : GL (Fin n) w.Completion :=
  (AdelicGLn.restrictedProductEquiv K n g).1 w

def finAt (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) :
    GL (Fin n) (v.adicCompletion K) :=
  (AdelicGLn.restrictedProductEquiv K n g).2 v

@[simp] theorem infAt_apply (w : InfinitePlace K) (g : AdelicGLn.AdelicGL K n) (a b : Fin n) :
    infAt w g a b = (g a b).1 w := rfl

@[simp] theorem finAt_apply (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) (a b : Fin n) :
    finAt v g a b = (g a b).2 v := rfl

theorem infAt_mul (w : InfinitePlace K) (g h : AdelicGLn.AdelicGL K n) :
    infAt w (g * h) = infAt w g * infAt w h := by
  simp [infAt, map_mul]

theorem finAt_mul (v : HeightOneSpectrum (𝓞 K)) (g h : AdelicGLn.AdelicGL K n) :
    finAt v (g * h) = finAt v g * finAt v h := by
  simp [finAt, map_mul]

def infEval (w : InfinitePlace K) : 𝔸[K] →+* w.Completion :=
  (Pi.evalRingHom _ w).comp (RingHom.fst _ _)

def finEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →+* v.adicCompletion K :=
  (RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)

@[simp] theorem infEval_apply (w : InfinitePlace K) (a : 𝔸[K]) : infEval w a = a.1 w := rfl

@[simp] theorem finEval_apply (v : HeightOneSpectrum (𝓞 K)) (a : 𝔸[K]) : finEval v a = a.2 v := rfl

theorem infComp_vecMul (w : InfinitePlace K) (y : Fin n → 𝔸[K]) (M : Matrix (Fin n) (Fin n) 𝔸[K]) :
    infComp w (y ᵥ* M) = infComp w y ᵥ* (M.map (infEval w)) := by
  ext j
  simp only [infComp, vecMul, dotProduct, Matrix.map_apply]
  rw [← infEval_apply, map_sum]
  simp [map_mul]

theorem finComp_vecMul (v : HeightOneSpectrum (𝓞 K)) (y : Fin n → 𝔸[K])
    (M : Matrix (Fin n) (Fin n) 𝔸[K]) :
    finComp v (y ᵥ* M) = finComp v y ᵥ* (M.map (finEval v)) := by
  ext j
  simp only [finComp, vecMul, dotProduct, Matrix.map_apply]
  rw [← finEval_apply, map_sum]
  simp [map_mul]

theorem infComp_vecMul_GL (w : InfinitePlace K) (y : Fin n → 𝔸[K]) (g : AdelicGLn.AdelicGL K n) :
    infComp w (y ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) =
      infComp w y ᵥ* (infAt w g : Matrix (Fin n) (Fin n) w.Completion) := by
  rw [infComp_vecMul]
  rfl

theorem finComp_vecMul_GL (v : HeightOneSpectrum (𝓞 K)) (y : Fin n → 𝔸[K])
    (g : AdelicGLn.AdelicGL K n) :
    finComp v (y ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) =
      finComp v y ᵥ* (finAt v g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) := by
  rw [finComp_vecMul]
  rfl

def adelicNorm (y : Fin n → 𝔸[K]) : ℝ :=
  (∏ w : InfinitePlace K, euclidNorm (infComp w y) ^ w.mult) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖finComp v y‖

def HasFiniteContent (y : Fin n → 𝔸[K]) : Prop :=
  ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖finComp v y‖ = 1

theorem HasFiniteContent.finite_mulSupport {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖finComp v y‖).Finite :=
  Filter.eventually_cofinite.1 hy

theorem adelicNorm_nonneg (y : Fin n → 𝔸[K]) : 0 ≤ adelicNorm y :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (euclidNorm_nonneg _) _)
    (finprod_nonneg fun _ => norm_nonneg _)

theorem finComp_smul (v : HeightOneSpectrum (𝓞 K)) (s : 𝔸[K]) (y : Fin n → 𝔸[K]) :
    finComp v (s • y) = s.2 v • finComp v y := rfl

theorem infComp_smul (w : InfinitePlace K) (s : 𝔸[K]) (y : Fin n → 𝔸[K]) :
    infComp w (s • y) = s.1 w • infComp w y := rfl

theorem HasFiniteContent.smul {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (s : GroundTheory.Global.IdeleGroup K) : HasFiniteContent ((s : 𝔸[K]) • y) := by
  filter_upwards [hy, GroundTheory.Global.IdeleGroup.eventually_norm_eq_one s] with v h1 h2
  rw [finComp_smul, norm_smul, h1, h2, mul_one]

theorem adelicNorm_smul {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (s : GroundTheory.Global.IdeleGroup K) :
    adelicNorm ((s : 𝔸[K]) • y) = (GroundTheory.Global.IdeleGroup.ideleModule K s : ℝ) * adelicNorm y := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, adelicNorm, adelicNorm]
  simp only [infComp_smul, euclidNorm_smul, mul_pow, Finset.prod_mul_distrib, finComp_smul,
    norm_smul]
  rw [finprod_mul_distrib (GroundTheory.Global.IdeleGroup.finite_mulSupport_norm s) hy.finite_mulSupport]
  ring

section LocalIntegral

variable (v : HeightOneSpectrum (𝓞 K))

theorem norm_le_one_of_mem {x : v.adicCompletion K} (hx : x ∈ v.adicCompletionIntegers K) :
    ‖x‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 hx)

theorem norm_vecMul_le_of_integral {M : Matrix (Fin n) (Fin n) (v.adicCompletion K)}
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers K) (z : Fin n → v.adicCompletion K) :
    ‖z ᵥ* M‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun j => ?_
  simp only [vecMul, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg z) fun i _ => ?_
  rw [norm_mul]
  calc ‖z i‖ * ‖M i j‖ ≤ ‖z i‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_le_one_of_mem v (hM i j)) (norm_nonneg _)
    _ ≤ ‖z‖ := by rw [mul_one]; exact norm_le_pi_norm z i

theorem norm_vecMul_integralGL {k : GL (Fin n) (v.adicCompletion K)}
    (hk : k ∈ GLnLocal.integralGL (v.adicCompletion K) n) (z : Fin n → v.adicCompletion K) :
    ‖z ᵥ* (k : Matrix (Fin n) (Fin n) (v.adicCompletion K))‖ = ‖z‖ := by
  rw [GLnLocal.mem_integralGL_iff] at hk
  simp only [GroundTheory.Global.mem_valuationInteger_iff] at hk
  refine le_antisymm (norm_vecMul_le_of_integral v hk.1 z) ?_
  have h := norm_vecMul_le_of_integral v hk.2 (z ᵥ* (k : Matrix (Fin n) (Fin n) (v.adicCompletion K)))
  rwa [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one] at h

end LocalIntegral

theorem HasFiniteContent.vecMul {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (g : AdelicGLn.AdelicGL K n) :
    HasFiniteContent (y ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  filter_upwards [hy, AdelicGLn.eventually_mem_integralGL K n g] with v h1 h2
  rw [finComp_vecMul_GL, finAt, norm_vecMul_integralGL v h2, h1]

def ratVec (x : Fin n → K) : Fin n → 𝔸[K] := fun i => algebraMap K 𝔸[K] (x i)

theorem finComp_ratVec (v : HeightOneSpectrum (𝓞 K)) (x : Fin n → K) (i : Fin n) :
    finComp v (ratVec x) i = (x i : v.adicCompletion K) := rfl

theorem infComp_ratVec (w : InfinitePlace K) (x : Fin n → K) (i : Fin n) :
    infComp w (ratVec x) i = (x i : w.Completion) := rfl

theorem ratVec_smul (c : K) (x : Fin n → K) :
    ratVec (c • x) = algebraMap K 𝔸[K] c • ratVec x := by
  ext i
  simp [ratVec, map_mul]

theorem ratVec_vecMul (x : Fin n → K) (M : Matrix (Fin n) (Fin n) K) :
    ratVec (x ᵥ* M) = ratVec x ᵥ* M.map (algebraMap K 𝔸[K]) := by
  ext j
  simp [ratVec, vecMul, dotProduct, map_sum, map_mul]

theorem eventually_norm_le_one (k : K) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(k : v.adicCompletion K)‖ ≤ 1 := by
  filter_upwards [(algebraMap K 𝔸[K] k).2.2] with v hv
  exact norm_le_one_of_mem v hv

theorem eventually_norm_eq_one {k : K} (hk : k ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(k : v.adicCompletion K)‖ = 1 := by
  filter_upwards [GroundTheory.Global.IdeleGroup.eventually_norm_eq_one
    (GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 k hk))] with v hv
  exact hv

theorem hasFiniteContent_ratVec {x : Fin n → K} (hx : x ≠ 0) : HasFiniteContent (ratVec x) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx
  filter_upwards [eventually_all.2 fun i => eventually_norm_le_one (x i),
    eventually_norm_eq_one hi₀] with v h1 h2
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => h1 i) ?_
  rw [← h2]
  exact norm_le_pi_norm (finComp v (ratVec x)) i₀

theorem prod_norm_mul_finprod_norm {c : K} (hc : c ≠ 0) :
    (∏ w : InfinitePlace K, ‖(c : w.Completion)‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(c : v.adicCompletion K)‖ = 1 := by
  have h := GroundTheory.Global.IdeleGroup.ideleModule_diagonal (Units.mk0 c hc)
  rw [Subtype.ext_iff, GroundTheory.Global.IdeleGroup.ideleModule_eq] at h
  exact h

theorem one_le_adelicNorm_ratVec {x : Fin n → K} (hx : x ≠ 0) : 1 ≤ adelicNorm (ratVec x) := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx
  rw [← prod_norm_mul_finprod_norm hi₀, adelicNorm]
  have hfin := (hasFiniteContent_ratVec hx).finite_mulSupport
  have hfin' : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      ‖(x i₀ : v.adicCompletion K)‖).Finite :=
    Filter.eventually_cofinite.1 (eventually_norm_eq_one hi₀)
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _)
    (Finset.prod_nonneg fun _ _ => pow_nonneg (euclidNorm_nonneg _) _)
  · exact Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _) fun w _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_euclidNorm (infComp w (ratVec x)) i₀) _
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin'.toFinset ∪ hfin.toFinset)
      (fun v hv => Finset.mem_coe.2 (Finset.mem_union_left _ (hfin'.mem_toFinset.2 hv))),
      finprod_eq_prod_of_mulSupport_subset _ (s := hfin'.toFinset ∪ hfin.toFinset)
      (fun v hv => Finset.mem_coe.2 (Finset.mem_union_right _ (hfin.mem_toFinset.2 hv)))]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ =>
      norm_le_pi_norm (finComp v (ratVec x)) i₀

theorem adelicNorm_smul_rat {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y) {c : K} (hc : c ≠ 0) :
    adelicNorm (algebraMap K 𝔸[K] c • y) = adelicNorm y := by
  have h := adelicNorm_smul hy (GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 c hc))
  rwa [GroundTheory.Global.IdeleGroup.ideleModule_diagonal, GroundTheory.Global.IdeleGroup.coe_diagonal,
    Units.val_mk0, Positive.val_one, one_mul] at h

def height (g : AdelicGLn.AdelicGL K n) (x : Fin n → K) : ℝ :=
  adelicNorm (ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]))

theorem hasFiniteContent_height (g : AdelicGLn.AdelicGL K n) {x : Fin n → K} (hx : x ≠ 0) :
    HasFiniteContent (ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) :=
  (hasFiniteContent_ratVec hx).vecMul g

theorem height_nonneg (g : AdelicGLn.AdelicGL K n) (x : Fin n → K) : 0 ≤ height g x :=
  adelicNorm_nonneg _

theorem height_smul (g : AdelicGLn.AdelicGL K n) {x : Fin n → K} (hx : x ≠ 0) {c : K}
    (hc : c ≠ 0) : height g (c • x) = height g x := by
  rw [height, ratVec_smul, smul_vecMul, adelicNorm_smul_rat (hasFiniteContent_height g hx) hc,
    height]

theorem height_diagonal_mul (γ : GL (Fin n) K) (g : AdelicGLn.AdelicGL K n) (x : Fin n → K) :
    height (AdelicGLn.diagonal K n γ * g) x = height g (x ᵥ* (γ : Matrix (Fin n) (Fin n) K)) := by
  rw [height, height, Units.val_mul, ← vecMul_vecMul, ratVec_vecMul]
  rfl

theorem one_le_height_one {x : Fin n → K} (hx : x ≠ 0) : 1 ≤ height 1 x := by
  rw [height, Units.val_one, vecMul_one]
  exact one_le_adelicNorm_ratVec hx

end Reduction

end

end GroundTheory.Automorphic
