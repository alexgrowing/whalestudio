import Mathlib
import Formalism.LocalToGlobal.KernelLattices.JetFieldLeKR
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.ExtEmbEquivComp
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions

theorem mem_rangeIF {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (z : ℂ) : z ∈ rangeIF σ ↔ ∃ k : K, σ k = z := by
  unfold rangeIF
  rw [AlgHom.mem_fieldRange]
  rfl

theorem withK_embC {X : Fields} (A : Amb X) (M : IntermediateField ℚ ℂ) [NumberField M] [StarRing M] (hM : ∀ τ x, X.embC A.σ₀ τ x ∈ M) :
    (fieldsWithK X M fun τ => (X.embC A.σ₀ τ).codRestrict M (hM τ)).embC (A.withK M hM).σ₀ = X.embC A.σ₀ := by
  funext τ
  exact RingHom.ext fun x => rfl

theorem withK_thInd {X : Fields} (A : Amb X) (M : IntermediateField ℚ ℂ) [NumberField M] [StarRing M] (hM : ∀ τ x, X.embC A.σ₀ τ x ∈ M)
    {a b : ℕ} (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b) :
    (A.withK M hM).thInd Sall N N' c x = A.thInd Sall N N' c x := by
  have h := withK_embC A M hM
  unfold Amb.thInd
  rw [h]
  rfl

theorem jets_rational_of_degree_form : JetsRatDegOf := fun _ _ _ _ _ _ _ h N N' c x hr m _ => h N N' c x hr m

theorem evG_id_map {K : Type} [Field K] {ι : Type} [Fintype ι] {a : ℕ} {Y : Type} (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ) (sh : ι → ℤ) (σ : K →+* ℂ)
    (P : DIV.Pol K ι a) : evG fr sh (RingHom.id ℂ) (MvPolynomial.map σ P) = evG fr sh σ P := by
  funext y
  unfold evG
  congr 1
  exact MvPolynomial.eval_map σ _ P

section Local

open MvPolynomial Formalism.L2.DIV

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

theorem aeval_scale_monomial {σ : Type} (u : σ → K) (s : σ →₀ ℕ) (c : K) :
    aeval (fun i => C (u i) * X i : σ → MvPolynomial σ K) (monomial s c) = monomial s (c * s.prod fun i k => u i ^ k) := by
  have h : (s.prod fun i k => (C (u i ^ k) : MvPolynomial σ K)) = C (s.prod fun i k => u i ^ k) := by
    simp [Finsupp.prod, map_prod]
  rw [aeval_monomial]
  simp only [mul_pow, Finsupp.prod_mul, ← C_pow]
  rw [h, monomial_eq, C_mul, algebraMap_eq, mul_assoc]

theorem coeff_scale {σ : Type} (u : σ → K) (R : MvPolynomial σ K) (s : σ →₀ ℕ) :
    coeff s (aeval (fun i => C (u i) * X i : σ → MvPolynomial σ K) R) = coeff s R * s.prod fun i k => u i ^ k := by
  classical
  induction R using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  | add f g hf hg => rw [map_add, coeff_add, coeff_add, hf, hg, add_mul]

open Classical in
theorem degAt_eq (m : DVar ι a b →₀ ℕ) (τ : ι) : degAt m τ = ∑ k : DVar ι a b, if k.1 = τ then m k else 0 := by
  unfold degAt
  rw [Finset.sum_filter]
  refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
  have : m k = 0 := by simpa using hk
  rw [this]; simp

open Classical in

def scU (a b : ℕ) (τ : ι) (x : K) : ((ι × Fin b × Fin b) ⊕ DVar ι a b) → K := Sum.elim (fun _ => 1) (fun k => if k.1 = τ then x else 1)

open Classical in
theorem scale_prod (τ : ι) (x : K) (s : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) :
    (s.prod fun i k => scU a b τ x i ^ k) = x ^ degAt (s.comapDomain Sum.inr Sum.inr_injective.injOn) τ := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fintype.prod_sum_type, degAt_eq, ← Finset.prod_pow_eq_pow_sum]
  simp only [scU, Sum.elim_inl, Sum.elim_inr, one_pow, Finset.prod_const_one, one_mul, Finsupp.comapDomain_apply]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs <;> simp

open Classical in

def bSc (a : ℕ) (τ : ι) (x : K) : ι → Matrix (Fin a) (Fin a) K := fun τ' => Matrix.diagonal fun _ => if τ' = τ then x else 1

open Classical in
theorem isBor_bSc (τ : ι) {x : K} (hx : x ≠ 0) : IsBor (bSc a τ x) := by
  intro τ'
  refine ⟨fun r s h => ?_, fun r => ?_⟩
  · simp [bSc, (ne_of_gt h)]
  · simp only [bSc, Matrix.diagonal_apply_eq]
    split_ifs
    · exact hx
    · exact one_ne_zero

open Classical in
theorem colSub_bSc_X (τ : ι) (x : K) (v : ι × Fin a × Fin a) :
    colSub (bSc a τ x) (X v : Pol K ι a) = C (if v.1 = τ then x else 1) * X v := by
  simp only [colSub, aeval_X, bSc, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single v.2.2]
  · simp
  · intro r _ hr
    simp [hr]
  · simp

open Classical in
theorem subD_colSub_bSc (τ : ι) (x : K) (Q : Pol K ι a) :
    subD K ι a b (colSub (bSc a τ x) Q) = aeval (fun i => C (scU a b τ x i) * X i) (subD K ι a b Q) := by
  have e : (subD K ι a b).comp (colSub (bSc a τ x)) =
      (aeval (fun i => C (scU a b τ x i) * X i) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K →ₐ[K] _).comp (subD K ι a b) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, AlgHom.comp_apply, colSub_bSc_X, map_mul]
    simp only [subD, aeval_X, aeval_C, algebraMap_eq]
    by_cases hb : v.2.2.1 < b
    · simp only [dif_pos hb, map_sum, map_mul, aeval_X, scU, Sum.elim_inl, Sum.elim_inr, C_1, one_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by ring
    · simp only [dif_neg hb, mul_zero, map_zero]
  exact AlgHom.congr_fun e Q

theorem jetLin_congr (J J' : (DVar ι a b →₀ ℕ) → K) (R : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K)
    (h : ∀ s ∈ R.support, J (s.comapDomain Sum.inr Sum.inr_injective.injOn) = J' (s.comapDomain Sum.inr Sum.inr_injective.injOn)) :
    jetLin J R = jetLin J' R := by
  rw [R.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [jetLin_monomial, jetLin_monomial, h s hs]

theorem deg_of_wt [Infinite K] {ν : ι → Fin a → ℕ} {Q : Pol K ι a} (hQ : Q ∈ WtPol K ν)
    (s : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (hs : s ∈ (subD K ι a b Q).support) (τ : ι) :
    degAt (s.comapDomain Sum.inr Sum.inr_injective.injOn) τ = ∑ r, ν τ r := by
  classical
  apply pow_inj_of_infinite (K := K)
  intro x hx
  have h1 := hQ (bSc a τ x) (isBor_bSc τ hx)
  have h2 := subD_colSub_bSc (b := b) τ x Q
  rw [h1, map_smul] at h2
  have h3 := congrArg (coeff s) h2
  rw [coeff_scale, scale_prod, coeff_smul, smul_eq_mul, mul_comm] at h3
  have hc : coeff s (subD K ι a b Q) ≠ 0 := mem_support_iff.1 hs
  have h4 := mul_left_cancel₀ hc h3
  rw [← h4]
  have h5 : (∏ τ', ∏ r, bSc a τ x τ' r r ^ ν τ' r) = x ^ ∑ r, ν τ r := by
    rw [Finset.prod_eq_single τ]
    · simp [bSc, Finset.prod_pow_eq_pow_sum]
    · intro τ' _ hne
      simp [bSc, hne]
    · simp
  rw [h5]

theorem jet_local_rationality : JetLocal := by
  intro K _ _ ι _ a b lam n J J' h P hP
  have hQ := vv_in_weight K ι a lam n P hP
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  exact jetLin_congr J J' _ fun s hs => h _ fun τ => deg_of_wt hQ s hs τ

end Local

end Formalism.L2.Ker
