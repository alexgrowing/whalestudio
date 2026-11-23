import Mathlib
import Formalism.LocalToGlobal.Columns.StandardDeltaIntegralCoeffs
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms

section FockN

def fockN {σ : Type} (f : MvPolynomial σ ℂ) : ℝ := ∑ m ∈ f.support, ‖coeff m f‖ ^ 2 * (mfact m : ℝ)

theorem fockF_self {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f = (fockN f : ℂ) := by
  unfold Formalism.REAL.fockF fockN
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.star_def, RCLike.mul_conj]
  simp [Formalism.L2.DIV.mfact]

theorem fockN_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ fockN f :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem fockN_pos {σ : Type} (f : MvPolynomial σ ℂ) (hf : f ≠ 0) : 0 < fockN f := by
  have hne : f.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h0 => hf (MvPolynomial.support_eq_empty.mp h0)
  obtain ⟨m, hm⟩ := hne
  unfold fockN
  refine Finset.sum_pos' (fun i _ => by positivity) ⟨m, hm, ?_⟩
  have h1 : coeff m f ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have h2 : (0 : ℝ) < (mfact m : ℝ) := by
    have : 0 < mfact m := Finset.prod_pos fun k _ => Nat.factorial_pos _
    exact_mod_cast this
  exact mul_pos (pow_pos (norm_pos_iff.mpr h1) 2) h2

theorem fockN_sum_le {σ : Type} (f : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)) :
    ∑ m ∈ S, ‖coeff m f‖ ^ 2 * (mfact m : ℝ) ≤ fockN f := by
  classical
  unfold fockN
  rw [← Finset.sum_filter_of_ne (p := fun m => m ∈ f.support)]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => (Finset.mem_filter.mp hm).2)
      (fun _ _ _ => by positivity)
  · intro m _ hne
    rw [MvPolynomial.mem_support_iff]
    intro h0
    apply hne
    simp [h0]

variable {ι : Type} [Fintype ι] {n : ℕ}

def extremalFockNormProduct (lam : ι → DomWeight n) : ℝ := ∏ τ, fockN (extremal ℂ n (lam τ))

theorem extR_pos (lam : ι → DomWeight n) : 0 < extremalFockNormProduct lam :=
  Finset.prod_pos fun _ _ => fockN_pos _ (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _)

theorem nfL_self (lam : ι → DomWeight n) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfL lam P P = ((fockN P / extremalFockNormProduct lam : ℝ) : ℂ) := by
  rw [nfL_apply, nfAll, fockF_self]
  simp only [fockF_self, extremalFockNormProduct]
  push_cast
  rfl

end FockN

section FinalTheorems

variable (K : Type) [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

theorem tensor_pairing_pos_def (v : InfinitePlace K) :
    (Matrix.of fun i j => v.embedding (pairK lam (fun _ => 1) (bVV K lam i) (bVV K lam j))).PosDef :=
  pairPos K ι n lam _ v.embedding fun _ => by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.PosDef.one

theorem tensor_pairing_gram_eq (v : InfinitePlace K) (i j : VVIdx lam) :
    v.embedding (pairK lam (fun _ => 1) (bVV K lam i) (bVV K lam j)) =
      nfL lam (map v.embedding (bVVfun K lam i)) (map v.embedding (bVVfun K lam j)) := by
  rw [pairK_apply, bVV_coe, bVV_coe, map_pairP v.embedding lam (fun _ => 1) (fun _ => 1) (fun _ => by simp) _ _ ?_, nfL_apply]
  · simp only [Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one, one_zpow, Finset.prod_const_one, one_mul, blockAct_one,
      AlgHom.id_apply]
  · intro m
    obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
    rw [hQ, coeff_map]
    simp

theorem embedding_map_basis_repr (v : InfinitePlace K) (x : VV K lam) :
    map v.embedding x.1 = ∑ i, v.embedding ((bVV K lam).repr x i) • map v.embedding (bVVfun K lam i) := by
  conv_lhs => rw [← (bVV K lam).sum_repr x]
  rw [Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, bVV_coe, bc_map_smul]

theorem metric_eq_normalised_fock (v : InfinitePlace K) (x y : VV K lam) :
    formAt (bVV K lam) (pairK lam fun _ => 1) v x y = nfL lam (map v.embedding x.1) (map v.embedding y.1) := by
  rw [embedding_map_basis_repr K lam v x, embedding_map_basis_repr K lam v y]
  simp only [formAt, tensor_pairing_gram_eq, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem source_norm_fock_ratio (M : ι → Submodule (𝓞 K) (Fin n → K)) (v : InfinitePlace K) (x : VV K lam) :
    normAt (tenH K lam M).b (tenH K lam M).X v x ^ 2 = fockN (map v.embedding x.1) / extremalFockNormProduct lam := by
  have hs := formH_spec (bVV K lam) (pairK lam fun _ => 1) (tensor_pairing_pos_def K lam) (delK lam M)
  have h1 := hs.2.1 v x x
  rw [metric_eq_normalised_fock, nfL_self] at h1
  have h2 := Formalism.L2.GlobalTheoryTheory.HLatOps.majAt_self (tenH K lam M).b (tenH K lam M).X v x
  exact_mod_cast h2.symm.trans h1

end FinalTheorems

section Tgt

variable (K : Type) [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

def monW (m : MonI lam) : ℝ := (mfact m.1 : ℝ) / extremalFockNormProduct lam

theorem mfact_pos {σ : Type} (m : σ →₀ ℕ) : 0 < mfact m := Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem monW_pos (m : MonI lam) : 0 < monW lam m := by
  unfold monW
  exact div_pos (Nat.cast_pos.mpr (mfact_pos _)) (extR_pos lam)

def monD : Matrix (MonI lam) (MonI lam) ℂ := Matrix.diagonal fun m => ((Real.sqrt (monW lam m) : ℝ) : ℂ)

theorem monD_det : IsUnit (monD lam).det := by
  rw [monD, Matrix.det_diagonal, isUnit_iff_ne_zero]
  refine Finset.prod_ne_zero_iff.2 fun m _ => ?_
  exact_mod_cast (Real.sqrt_pos.2 (monW_pos lam m)).ne'

@[reducible] def monH (L : Submodule (𝓞 K) (MonI lam → K)) : HLat K where
  V := MonI lam → K
  ι := MonI lam
  b := Pi.basisFun K (MonI lam)
  X := fun _ => (monD lam)⁻¹
  L := L

theorem monH_frameOK (L : Submodule (𝓞 K) (MonI lam → K)) : FrameOK (monH K lam L) := fun _ =>
  Matrix.isUnit_nonsing_inv_det _ (monD_det lam)

theorem monH_fcoord (v : InfinitePlace K) (x : MonI lam → K) (m : MonI lam) :
    fcoord (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v x m = ((Real.sqrt (monW lam m) : ℝ) : ℂ) * v.embedding (x m) := by
  rw [fcoord, Matrix.nonsing_inv_nonsing_inv _ (monD_det lam)]
  simp [monD, Matrix.mulVec_diagonal, vecAt]

theorem monH_norm (v : InfinitePlace K) (x : MonI lam → K) :
    normAt (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v x ^ 2 = ∑ m, monW lam m * ‖v.embedding (x m)‖ ^ 2 := by
  unfold normAt cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [monH_fcoord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (monW_pos lam m).le]

theorem monH_maj (v : InfinitePlace K) (x y : MonI lam → K) :
    majAt (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v x y =
      ∑ m, star (((Real.sqrt (monW lam m) : ℝ) : ℂ) * v.embedding (x m)) * (((Real.sqrt (monW lam m) : ℝ) : ℂ) * v.embedding (y m)) := by
  unfold majAt
  simp only [monH_fcoord]

theorem monH_orth (v : InfinitePlace K) (m m' : MonI lam) (h : m ≠ m') :
    majAt (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v (Pi.single m 1) (Pi.single m' 1) = 0 := by
  rw [monH_maj]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = m
  · subst hk
    simp [h]
  · simp [Pi.single_apply, hk]

theorem monH_norm_single (v : InfinitePlace K) (m : MonI lam) :
    normAt (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v (Pi.single m 1) ^ 2 = monW lam m := by
  rw [monH_norm, Finset.sum_eq_single m]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h; exact absurd (Finset.mem_univ _) h

end Tgt

section Norm

def hsN {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ a, ∑ b, ‖U a b‖ ^ 2

theorem hsN_nonneg {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN U :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

def FockSubNorm : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (U : ι → Matrix (Fin n) (Fin n) ℂ) (d : ι → ℕ) (F : MvPolynomial (ι × Fin n × Fin n) ℂ),
    (∀ m, coeff m F ≠ 0 → ∀ τ, ∑ a, ∑ s, m (τ, a, s) = d τ) →
    fockN (Formalism.GradedWeylDivisibility.blockAct ℂ U F) ≤ (∏ τ, hsN (U τ) ^ d τ) * fockN F

variable (K : Type) [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

def dW (lam : DomWeight n) : ℕ := ∑ s, lam.natW s

def gN (g : ι → GL (Fin n) K) (v : InfinitePlace K) (τ : ι) : ℝ :=
  hsN (((g τ : Matrix (Fin n) (Fin n) K)ᵀ).map v.embedding)

theorem coefficient_map_norm_bound (hS : FockSubNorm) (g : ι → GL (Fin n) K) (M : ι → Submodule (𝓞 K) (Fin n → K)) (v : InfinitePlace K)
    (x : VV K lam) :
    normAt (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v (cfMap lam g x) ^ 2 ≤
      (∏ τ, gN K g v τ ^ dW (lam τ)) * normAt (tenH K lam M).b (tenH K lam M).X v x ^ 2 := by
  rw [monH_norm, source_norm_fock_ratio]
  set G : MvPolynomial (ι × Fin n × Fin n) ℂ := map v.embedding (trAct g x.1) with hG
  have e1 : ∑ m, monW lam m * ‖v.embedding (cfMap lam g x m)‖ ^ 2 =
      (∑ m : MonI lam, ‖coeff m.1 G‖ ^ 2 * (mfact m.1 : ℝ)) / extremalFockNormProduct lam := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hG, coeff_map, cfMap_apply, monW]
    ring
  have e2 : ∑ m : MonI lam, ‖coeff m.1 G‖ ^ 2 * (mfact m.1 : ℝ) ≤ fockN G := by
    have := fockN_sum_le G ((Finset.univ : Finset (MonI lam)).map ⟨fun m : MonI lam => m.1, fun a b h => Subtype.ext h⟩)
    rwa [Finset.sum_map] at this
  have e3 : G = Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((g τ : Matrix (Fin n) (Fin n) K)ᵀ).map v.embedding) (map v.embedding x.1) :=
    map_blockAct v.embedding _ x.1
  have e4 : fockN G ≤ (∏ τ, gN K g v τ ^ dW (lam τ)) * fockN (map v.embedding x.1) := by
    rw [e3]
    refine hS ι n _ (fun τ => dW (lam τ)) _ fun m hm τ => ?_
    rw [coeff_map] at hm
    have hm' := coefficient_space_support K lam x.2 m (fun h => hm (by rw [h, map_zero]))
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => hm' τ s
  rw [e1, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (e2.trans e4) (extR_pos lam).le

variable [IsTotallyComplex K]

theorem coefficient_map_height_bound (hS : FockSubNorm) (g : ι → GL (Fin n) K) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hne : cfMap lam g ≠ 0)
    (hpos : ∀ v τ, 0 < gN K g v τ) :
    htMap (tenH K lam M).b (tenH K lam M).X (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) (cfMap lam g) ≤
      ∑ τ, (dW (lam τ) : ℝ) * ((1 / (nPl K : ℝ)) * ∑ v, Real.log (gN K g v τ)) := by
  have hX : ∀ v, IsUnit ((tenH K lam M).X v).det :=
    (formH_spec (bVV K lam) (pairK lam fun _ => 1) (tensor_pairing_pos_def K lam) (delK lam M)).1
  have hX' : ∀ v : InfinitePlace K, IsUnit ((monD lam)⁻¹).det := fun _ => Matrix.isUnit_nonsing_inv_det _ (monD_det lam)
  have hP : ∀ v, 0 < ∏ τ, gN K g v τ ^ dW (lam τ) := fun v => Finset.prod_pos fun τ _ => pow_pos (hpos v τ) _
  have h1 : ∀ v, opNormAt (tenH K lam M).b (tenH K lam M).X (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v (cfMap lam g) ≤
      Real.sqrt (∏ τ, gN K g v τ ^ dW (lam τ)) := by
    intro v
    refine Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points _ _ _ _ hX _ v _ (Real.sqrt_nonneg _) fun x => ?_
    refine (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt (hP v).le]
    exact coefficient_map_norm_bound K lam hS g M v x
  have h2 : ∀ v, Real.log (opNormAt (tenH K lam M).b (tenH K lam M).X (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v
      (cfMap lam g) ^ 2) ≤ ∑ τ, (dW (lam τ) : ℝ) * Real.log (gN K g v τ) := by
    intro v
    have h0 := Formalism.HN.PlaceOperatorNorms.opNormAt_pos (tenH K lam M).b (tenH K lam M).X (Pi.basisFun K (MonI lam))
      (fun _ => (monD lam)⁻¹) hX hX' v (cfMap lam g) hne
    have h3 : opNormAt (tenH K lam M).b (tenH K lam M).X (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v (cfMap lam g) ^ 2 ≤
        ∏ τ, gN K g v τ ^ dW (lam τ) := by
      rw [← Real.sq_sqrt (hP v).le]
      exact pow_le_pow_left₀ h0.le (h1 v) 2
    refine (Real.log_le_log (by positivity) h3).trans (le_of_eq ?_)
    rw [Real.log_prod (fun τ _ => (pow_pos (hpos v τ) _).ne')]
    exact Finset.sum_congr rfl fun τ _ => Real.log_pow _ _
  unfold htMap
  have hf : (0 : ℝ) ≤ 1 / (nPl K : ℝ) := by positivity
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => h2 v) hf).trans (le_of_eq ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.mul_sum]
  ring

end Norm

end Formalism.L2.Col
