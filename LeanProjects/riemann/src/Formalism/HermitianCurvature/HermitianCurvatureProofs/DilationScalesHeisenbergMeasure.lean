import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace B2x7

variable {k r' : ℕ}

def dgR (k r : ℕ) (t : ℝ) (i : Fin (2 * r + k + 1)) : ℝ :=
  if i.val < r then t ^ (r - i.val) else if i.val ≤ r + k then 1 else (t ^ (i.val - (r + k)))⁻¹

lemma aDil_eq (k r : ℕ) (t : ℝ) : aDil k r t = Matrix.diagonal fun i => ((dgR k r t i : ℝ) : ℂ) := by
  unfold aDil dgR
  congr 1
  funext i
  split_ifs <;> simp

lemma dgR_mul_inv (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) : dgR k r t i * dgR k r t⁻¹ i = 1 := by
  unfold dgR
  by_cases h1 : i.val < r
  · simp only [h1, if_true]
    rw [← mul_pow, mul_inv_cancel₀ ht]; simp
  · by_cases h2 : i.val ≤ r + k
    · simp [h1, h2]
    · simp only [h1, h2, if_false]
      rw [← mul_inv, ← mul_pow, mul_inv_cancel₀ ht]; simp

lemma dgR_shift (t : ℝ) (i : Fin (2 * (1 + r') + k + 1)) (hi : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1) :
    dgR k (1 + r') t i = dgR k r' t ⟨i.val - 1, by omega⟩ := by
  unfold dgR
  dsimp only
  by_cases h1 : i.val < 1 + r'
  · rw [if_pos h1, if_pos (show i.val - 1 < r' by omega)]
    have : 1 + r' - i.val = r' - (i.val - 1) := by omega
    rw [this]
  · rw [if_neg h1, if_neg (show ¬ (i.val - 1 < r') by omega)]
    by_cases h2 : i.val ≤ 1 + r' + k
    · rw [if_pos h2, if_pos (show i.val - 1 ≤ r' + k by omega)]
    · rw [if_neg h2, if_neg (show ¬ (i.val - 1 ≤ r' + k) by omega)]
      have : i.val - (1 + r' + k) = i.val - 1 - (r' + k) := by omega
      rw [this]

lemma dgR_rev (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) : dgR k r t i * dgR k r t (Fin.rev i) = 1 := by
  unfold dgR
  have hr : (Fin.rev i).val = 2 * r + k - i.val := by rw [Fin.val_rev]; omega
  have hi := i.isLt
  rw [hr]
  by_cases h1 : i.val < r
  · rw [if_pos h1, if_neg (show ¬ (2 * r + k - i.val < r) by omega), if_neg (show ¬ (2 * r + k - i.val ≤ r + k) by omega)]
    have : 2 * r + k - i.val - (r + k) = r - i.val := by omega
    rw [this]
    exact mul_inv_cancel₀ (pow_ne_zero _ ht)
  · rw [if_neg h1]
    by_cases h2 : i.val ≤ r + k
    · rw [if_pos h2, if_neg (show ¬ (2 * r + k - i.val < r) by omega), if_pos (show 2 * r + k - i.val ≤ r + k by omega)]
      simp
    · rw [if_neg h2, if_pos (show 2 * r + k - i.val < r by omega)]
      have : r - (2 * r + k - i.val) = i.val - (r + k) := by omega
      rw [this]
      exact inv_mul_cancel₀ (pow_ne_zero _ ht)

lemma prod_dgR_sq (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (∏ i, dgR k r t i) ^ 2 = 1 := by
  have h : ∏ i, dgR k r t (Fin.rev i) = ∏ i, dgR k r t i :=
    Equiv.prod_comp Fin.revPerm (dgR k r t)
  rw [sq]
  nth_rewrite 2 [← h]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => dgR_rev k r t ht i

lemma aDil_mul_inv (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : aDil k r t * (aDil k r t)⁻¹ = 1 := by
  rw [B2.aDil_inv _ _ _ ht, aDil_eq, aDil_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, dgR_mul_inv _ _ _ ht]; simp

lemma aDil_inv_mul (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (aDil k r t)⁻¹ * aDil k r t = 1 := by
  rw [B2.aDil_inv _ _ _ ht, aDil_eq, aDil_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, mul_comm, dgR_mul_inv _ _ _ ht]; simp

lemma herm_UH {ι : Type*} [Fintype ι] [DecidableEq ι] {H g : Matrix ι ι ℂ} (hg : g ∈ UH H) (x w : ι → ℂ) :
    herm H (g *ᵥ x) (g *ᵥ w) = herm H x w := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

lemma herm_smul_left {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (x w : ι → ℂ) :
    herm H (c • x) w = c * herm H x w := by
  unfold herm
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma herm_smul_right {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (x w : ι → ℂ) :
    herm H x (c • w) = conj c * herm H x w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]; rfl

lemma herm_sum {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u v : Fin m → ℂ) :
    ∑ j, herm H (bvec j) v * u j = herm H u v := by
  simp only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma heisAct (v u : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    heisG k r' v b *ᵥ u = u - herm (Hpk k (1 + r')) u v • e0 k r' + herm (Hpk k (1 + r')) u (e0 k r') • (v + b • e0 k r') := by
  ext i
  simp only [heisG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  have h1 : ∀ (w φ : Fin (2 * (1 + r') + k + 1) → ℂ), (Matrix.vecMulVec w φ *ᵥ u) i = (∑ j, φ j * u j) * w i := by
    intro w φ
    simp only [mulVec, dotProduct, vecMulVec_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h1, h1, herm_sum, herm_sum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

lemma heisG_comm (g : Mat k (1 + r')) (hg : g ∈ GV k (1 + r')) (c : ℝ) (hc : g *ᵥ e0 k r' = (c : ℂ) • e0 k r')
    (v : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    g * heisG k r' v b = heisG k r' ((c : ℂ) • (g *ᵥ v)) ((c : ℂ) ^ 2 * b) * g := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro u
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, heisAct, heisAct]
  have h1 : herm (Hpk k (1 + r')) (g *ᵥ u) ((c : ℂ) • (g *ᵥ v)) = (c : ℂ) * herm (Hpk k (1 + r')) u v := by
    rw [herm_smul_right, herm_UH hg, Complex.conj_ofReal]
  have h2 : (c : ℂ) * herm (Hpk k (1 + r')) (g *ᵥ u) (e0 k r') = herm (Hpk k (1 + r')) u (e0 k r') := by
    rw [← herm_UH hg u (e0 k r'), hc, herm_smul_right, Complex.conj_ofReal]
  rw [h1, ← h2, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul, hc]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma dilation_base_vector (t : ℝ) : aDil k (1 + r') t *ᵥ e0 k r' = ((t ^ (1 + r') : ℝ) : ℂ) • e0 k r' := by
  rw [aDil_eq]
  ext i
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  unfold e0 bvec
  by_cases h : i = eI k (1 + r') (a0 r')
  · subst h
    simp [dgR, eI, a0]
  · simp [h]

lemma aDil_lift (t : ℝ) (y : Fin (2 * r' + k + 1) → ℂ) :
    aDil k (1 + r') t *ᵥ liftVec k 1 r' y = liftVec k 1 r' (aDil k r' t *ᵥ y) := by
  rw [aDil_eq, aDil_eq]
  ext i
  rw [Matrix.mulVec_diagonal]
  unfold liftVec
  by_cases hi : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hi, dif_pos hi, Matrix.mulVec_diagonal, dgR_shift t i hi]
  · rw [dif_neg hi, dif_neg hi, mul_zero]

lemma liftVec_smul (c : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' (c • y) = c • liftVec k 1 r' y := by
  ext i
  rw [Pi.smul_apply]
  unfold liftVec
  by_cases hi : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hi, dif_pos hi, Pi.smul_apply]
  · rw [dif_neg hi, dif_neg hi, smul_zero]

lemma hb_dil (t : ℝ) (ht : t ≠ 0) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' (((t ^ (1 + r') : ℝ) : ℂ) • (aDil k r' t *ᵥ y)) (t ^ (2 * (1 + r')) * s) =
      ((t ^ (1 + r') : ℝ) : ℂ) ^ 2 * hb k r' y s := by
  unfold hb
  rw [herm_smul_left, herm_smul_right, herm_UH (dilation_mem_group k r' t ht), Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Complex.re_ofReal_mul, pow_mul' t 2 (1 + r')]
  push_cast
  ring

end B2x7

open B2x7

theorem dilation_conjugates_heisenberg : Formalism.FourierDecayAlt.B2.DilHeis := by
  intro k r' t ht x
  unfold heis0
  rw [heisG_comm _ (dilation_mem_group k (1 + r') t ht) _ (dilation_base_vector t), Matrix.mul_assoc, aDil_mul_inv _ _ _ ht, Matrix.mul_one,
    aDil_lift, ← liftVec_smul, hb_dil t ht]

theorem dilation_levi_conjugation : Formalism.FourierDecayAlt.B2.DilLev := by
  intro k r' t ht g
  rw [B2.aDil_inv _ _ _ ht, B2.aDil_inv _ _ _ ht]
  simp only [aDil_eq]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold ιLev
  by_cases hi : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hi, dif_pos hi]
    by_cases hj : 1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1
    · rw [dif_pos hj, dif_pos hj, Matrix.mul_diagonal, Matrix.diagonal_mul, dgR_shift t i hi, dgR_shift t⁻¹ j hj]
    · rw [dif_neg hj, dif_neg hj]; simp
  · rw [dif_neg hi, dif_neg hi]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, mul_one, ← Complex.ofReal_mul, dgR_mul_inv _ _ _ ht, Complex.ofReal_one]
    · rw [if_neg h]; simp

theorem modular_exponent_recursion : Formalism.FourierDecayAlt.B2.KapRec := by
  intro k r'
  unfold kap
  rw [Fin.sum_univ_add]
  simp only [Fin.sum_univ_one]
  congr 1
  · simp [Mdim]; ring_nf
  · apply Finset.sum_congr rfl
    intro a _
    have := a.isLt
    simp only [Mdim, Fin.natAdd]
    have h1 : 1 + r' - (1 + a.val) = r' - a.val := by omega
    simp only [h1]

namespace B2x7

variable {k r' : ℕ}

lemma conjM_cont {k r : ℕ} (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  unfold conjM
  exact ((continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

lemma liftVec_cont : Continuous (fun y : Fin (2 * r' + k + 1) → ℂ => liftVec k 1 r' y) := by
  apply continuous_pi
  intro p
  unfold liftVec
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [dif_pos hp]; exact continuous_apply _
  · simp only [dif_neg hp]; exact continuous_const

lemma herm_cont {ι X : Type*} [Fintype ι] [TopologicalSpace X] (H : Matrix ι ι ℂ) {f g : X → ι → ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => herm H (f x) (g x) := by
  unfold herm
  exact hg.star.dotProduct (continuous_const.matrix_mulVec hf)

lemma hb_cont : Continuous (fun x : HPar k r' => hb k r' x.1 x.2) := by
  unfold hb
  have h := herm_cont (Hpk k r') (continuous_fst (X := Fin (2 * r' + k + 1) → ℂ) (Y := ℝ)) continuous_fst
  exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp h).neg.div_const 2)).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

def heisF (k r' : ℕ) : HPar k r' → Mt k (1 + r') := fun x => heis0 k r' x

lemma μHeis_eq (k r' : ℕ) : μHeis k r' = (volume : Measure (HPar k r')).map (heisF k r') := rfl

lemma heisF_cont : Continuous (heisF k r') := by
  have hv : Continuous (fun x : HPar k r' => liftVec k 1 r' x.1) := liftVec_cont.comp continuous_fst
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  show Continuous fun x : HPar k r' => heis0 k r' x i j
  simp only [heis0, heisG, Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact (continuous_const.sub (continuous_const.mul (herm_cont _ continuous_const hv))).add
    ((((continuous_apply i).comp hv).add (hb_cont.mul continuous_const)).mul continuous_const)

def dilL (k r' : ℕ) (t : ℝ) : HPar k r' →ₗ[ℝ] HPar k r' :=
  LinearMap.prodMap
    (LinearMap.pi fun i => ((t ^ (1 + r') * dgR k r' t i) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i))
    ((t ^ (2 * (1 + r'))) • LinearMap.id)

lemma haarHPar (k r' : ℕ) : (volume : Measure (HPar k r')).IsAddHaarMeasure := by
  have h1 : (volume : Measure (Fin (2 * r' + k + 1) → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; infer_instance
  rw [Measure.volume_eq_prod]; infer_instance

lemma dilL_apply (t : ℝ) (x : HPar k r') :
    dilL k r' t x = (((t ^ (1 + r') : ℝ) : ℂ) • (aDil k r' t *ᵥ x.1), t ^ (2 * (1 + r')) * x.2) := by
  refine Prod.ext (funext fun i => ?_) rfl
  rw [aDil_eq]
  show (t ^ (1 + r') * dgR k r' t i) • x.1 i =
    (((t ^ (1 + r') : ℝ) : ℂ) • ((Matrix.diagonal fun i => ((dgR k r' t i : ℝ) : ℂ)) *ᵥ x.1)) i
  rw [Pi.smul_apply, Matrix.mulVec_diagonal, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

lemma det_dilL (t : ℝ) (ht : t ≠ 0) : LinearMap.det (dilL k r' t) = t ^ (2 * (2 * r' + k + 2) * (1 + r')) := by
  unfold dilL
  rw [LinearMap.det_prodMap, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, Module.finrank_self, mul_one, pow_one]
  rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow,
    prod_dgR_sq _ _ _ ht, mul_one, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  ring

end B2x7

theorem dilation_scales_heisenberg_measure : Formalism.FourierDecayAlt.B2.DilHeisMeas := by
  intro k r' t ht
  have ht0 : t ≠ 0 := ht.ne'
  have hL : Measurable (dilL k r' t) := (LinearMap.continuous_of_finiteDimensional _).measurable
  have hH : Measurable (heisF k r') := heisF_cont.measurable
  have hC : Measurable (conjM (aDil k (1 + r') t) : Mt k (1 + r') → Mt k (1 + r')) := (conjM_cont _).measurable
  have hcomp : conjM (aDil k (1 + r') t) ∘ heisF k r' = heisF k r' ∘ dilL k r' t := by
    funext x
    show aDil k (1 + r') t * heis0 k r' x * (aDil k (1 + r') t)⁻¹ = heis0 k r' (dilL k r' t x)
    rw [dilation_conjugates_heisenberg k r' t ht0 x, dilL_apply]
  have := haarHPar k r'
  have hdet : LinearMap.det (dilL k r' t) ≠ 0 := by rw [det_dilL t ht0]; exact pow_ne_zero _ ht0
  rw [μHeis_eq, Measure.map_map hC hH, hcomp, ← Measure.map_map hH hL, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, Measure.map_smul,
    det_dilL t ht0, abs_of_pos (inv_pos.mpr (pow_pos ht _))]

namespace B2x7

variable {k r' : ℕ}

lemma sigmaFinite_of_haar {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

lemma aDil_zero (k : ℕ) (t : ℝ) : aDil k 0 t = 1 := by
  rw [aDil_eq, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h : i.val ≤ 0 + k := by have := i.isLt; omega
  unfold dgR
  rw [if_neg (Nat.not_lt_zero _), if_pos h, Complex.ofReal_one]

lemma conjM_one (k r : ℕ) : (conjM (1 : Mat k r) : Mt k r → Mt k r) = id := by
  funext x
  unfold conjM
  rw [inv_one, Matrix.mul_one, Matrix.one_mul]
  rfl

lemma mulM_cont {k r : ℕ} : Continuous (mulM : Mt k r × Mt k r → Mt k r) := by
  unfold mulM
  exact (continuous_fst (X := Mat k r) (Y := Mat k r)).matrix_mul continuous_snd

lemma levM_cont : Continuous (levM k r') := by
  apply continuous_pi; intro p
  apply continuous_pi; intro q
  show Continuous fun x : Mt k r' => ιLev k 1 r' (Matrix.of x) p q
  unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [dif_pos hp]
    by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
    · simp only [dif_pos hq]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [dif_neg hq]; exact continuous_const
  · simp only [dif_neg hp]; exact continuous_const

lemma conjM_mulM {k r : ℕ} (a : Mat k r) (ha : a⁻¹ * a = 1) :
    (conjM a : Mt k r → Mt k r) ∘ mulM = mulM ∘ Prod.map (conjM a) (conjM a) := by
  funext p
  show a * (Matrix.of p.1 * Matrix.of p.2) * a⁻¹ = (a * Matrix.of p.1 * a⁻¹) * (a * Matrix.of p.2 * a⁻¹)
  have : (a * Matrix.of p.1 * a⁻¹) * (a * Matrix.of p.2 * a⁻¹) = a * Matrix.of p.1 * (a⁻¹ * a) * Matrix.of p.2 * a⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [this, ha]
  simp only [Matrix.mul_assoc, Matrix.mul_one]

lemma dil_step (μ' : Measure (Mt k r')) [SigmaFinite μ'] (t : ℝ) (ht : 0 < t)
    (h' : μ'.map (conjM (aDil k r' t)) = ENNReal.ofReal ((t ^ kap k r')⁻¹) • μ') :
    (((μHeis k r').prod (μ'.map (levM k r'))).map mulM).map (conjM (aDil k (1 + r') t)) =
      ENNReal.ofReal ((t ^ kap k (1 + r'))⁻¹) • ((μHeis k r').prod (μ'.map (levM k r'))).map mulM := by
  have ht0 : t ≠ 0 := ht.ne'
  have hC : Measurable (conjM (aDil k (1 + r') t) : Mt k (1 + r') → Mt k (1 + r')) := (conjM_cont _).measurable
  have hC' : Measurable (conjM (aDil k r' t) : Mt k r' → Mt k r') := (conjM_cont _).measurable
  have hM : Measurable (mulM : Mt k (1 + r') × Mt k (1 + r') → Mt k (1 + r')) := mulM_cont.measurable
  have hL : Measurable (levM k r') := levM_cont.measurable
  have hlev : (conjM (aDil k (1 + r') t) : Mt k (1 + r') → Mt k (1 + r')) ∘ levM k r' = levM k r' ∘ conjM (aDil k r' t) := by
    funext x
    exact dilation_levi_conjugation k r' t ht0 (Matrix.of x)
  have h2 : (μ'.map (levM k r')).map (conjM (aDil k (1 + r') t)) =
      ENNReal.ofReal ((t ^ kap k r')⁻¹) • μ'.map (levM k r') := by
    rw [Measure.map_map hC hL, hlev, ← Measure.map_map hL hC', h', Measure.map_smul]
  have : SFinite (μHeis k r') := by rw [μHeis_eq]; infer_instance
  rw [Measure.map_map hC hM, conjM_mulM _ (aDil_inv_mul _ _ _ ht0), ← Measure.map_map hM (hC.prodMap hC),
    ← Measure.map_prod_map _ _ hC hC, dilation_scales_heisenberg_measure k r' t ht, h2, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, Measure.map_smul, ← ENNReal.ofReal_mul (by positivity), ← mul_inv, ← pow_add, ← modular_exponent_recursion k r']

theorem dilJacRaw_of (hU : HaarUnique) (hN : ClosedN) (hR : NRecHaar) (hE : HaarNExists) : DilJacRaw := by
  intro k r
  induction r with
  | zero =>
    intro μN _ t _
    rw [aDil_zero, conjM_one, Measure.map_id]
    simp [kap]
  | succ r' ih =>
    rw [Nat.add_comm r' 1]
    intro μN hμ t ht
    obtain ⟨μ', hμ'⟩ := hE k r'
    have := sigmaFinite_of_haar hμ'
    obtain ⟨c, hc⟩ := hU k (1 + r') (Nset k (1 + r')) _ μN (hN k (1 + r')) (hR k r' μ' hμ') hμ.conc hμ.left hμ.finite_compact
    rw [hc, Measure.map_smul, dil_step μ' t ht (ih μ' hμ' t ht), smul_comm]

theorem dilJacAll_of (h : DilJacRaw) : DilJacAll := fun k r _ _ _ _ _ _ D t ht => h k r D.μN D.haarN t ht

theorem assembleDilJac : AssembleDilJac := fun hU hN hR _ hE _ _ _ =>
  ⟨dilJacRaw_of hU hN hR hE, dilJacAll_of (dilJacRaw_of hU hN hR hE)⟩

end B2x7

theorem dilation_jacobian_unipotent : Formalism.FourierDecayAlt.B2.DilJacRaw :=
  B2x7.dilJacRaw_of haar_measure_unique_up_to_scalar unipotent_radical_closed unipotent_haar_recursion unipotent_haar_exists

theorem dilation_jacobian_every_setting : Formalism.FourierDecayAlt.B2.DilJacAll := B2x7.dilJacAll_of dilation_jacobian_unipotent

end Formalism.FourierDecayAlt.P
