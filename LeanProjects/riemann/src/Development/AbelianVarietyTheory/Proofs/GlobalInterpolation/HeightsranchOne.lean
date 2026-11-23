import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Proof.FockBlockMonotone

private theorem mfact_eq_prod_factorial {σ : Type} [Fintype σ] (m : σ →₀ ℕ) :
    Formalism.L2.DIV.mfact m = ∏ k, (m k).factorial := by
  unfold Formalism.L2.DIV.mfact
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro k _ hk
  have : m k = 0 := by simpa using hk
  rw [this, Nat.factorial_zero]

private theorem fockB_monomial_monomial {σ : Type} [DecidableEq σ] (a b : σ →₀ ℕ) :
    Formalism.L2.DIV.fockB (MvPolynomial.monomial a (1 : ℂ)) (MvPolynomial.monomial b 1) =
      if a = b then (Formalism.L2.DIV.mfact a : ℂ) else 0 := by
  unfold Formalism.L2.DIV.fockB
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  by_cases h : a = b
  · subst h; simp
  · have h' : b ≠ a := fun e => h e.symm
    simp [h, h']

private theorem sum_mapDomain_prodMk_apply {ι α : Type} [Fintype ι] (v : ι → (α →₀ ℕ)) (τ : ι) (x : α) :
    (∑ σ, (v σ).mapDomain (Prod.mk σ)) (τ, x) = v τ x := by
  have h := congrArg (fun f : α →₀ ℕ => f x) (Formalism.MainNotions.product_first_zeroth_parts.comap_sum v τ)
  simpa [Finsupp.comapDomain_apply] using h

private theorem fockB_ten_monomial_eq_prod {ι : Type} [Fintype ι] {n : ℕ} (v w : ι → (Fin n × Fin n →₀ ℕ)) :
    Formalism.L2.DIV.fockB (Formalism.MainNotions.product_first_zeroth_parts.ten fun τ => MvPolynomial.monomial (v τ) (1 : ℂ))
      (Formalism.MainNotions.product_first_zeroth_parts.ten fun τ => MvPolynomial.monomial (w τ) (1 : ℂ)) =
      ∏ τ, Formalism.L2.DIV.fockB (MvPolynomial.monomial (v τ) (1 : ℂ)) (MvPolynomial.monomial (w τ) 1) := by
  classical
  rw [Formalism.MainNotions.product_first_zeroth_parts.ten_monomial, Formalism.MainNotions.product_first_zeroth_parts.ten_monomial, fockB_monomial_monomial]
  simp_rw [fockB_monomial_monomial]
  by_cases h : v = w
  · subst h
    simp only [if_true]
    rw [mfact_eq_prod_factorial, Fintype.prod_prod_type]
    simp_rw [mfact_eq_prod_factorial, sum_mapDomain_prodMk_apply]
    push_cast
    rfl
  · have hA : (∑ σ, (v σ).mapDomain (Prod.mk σ)) ≠ ∑ σ, (w σ).mapDomain (Prod.mk σ) := by
      intro hE
      apply h
      funext τ
      ext x
      have := congrArg (fun f : ι × Fin n × Fin n →₀ ℕ => f (τ, x)) hE
      simpa only [sum_mapDomain_prodMk_apply] using this
    obtain ⟨τ, hτ⟩ := Function.ne_iff.mp h
    rw [if_neg hA]
    exact (Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)).symm

private theorem fockB_ten_eq_prod {ι : Type} [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.L2.DIV.fockB (Formalism.MainNotions.product_first_zeroth_parts.ten f) (Formalism.MainNotions.product_first_zeroth_parts.ten g) = ∏ τ, Formalism.L2.DIV.fockB (f τ) (g τ) := by
  have h1 : ∀ (v : ι → (Fin n × Fin n →₀ ℕ)) (g : ι → MvPolynomial (Fin n × Fin n) ℂ),
      Formalism.L2.DIV.fockB (Formalism.MainNotions.product_first_zeroth_parts.ten fun τ => MvPolynomial.monomial (v τ) (1 : ℂ)) (Formalism.MainNotions.product_first_zeroth_parts.ten g) =
        ∏ τ, Formalism.L2.DIV.fockB (MvPolynomial.monomial (v τ) (1 : ℂ)) (g τ) := by
    intro v g
    have key : (Formalism.L2.DIV.fockBL (Formalism.MainNotions.product_first_zeroth_parts.ten fun τ => MvPolynomial.monomial (v τ) (1 : ℂ))).compMultilinearMap
          (Formalism.MainNotions.product_first_zeroth_parts.tenM (ι := ι) n) =
        (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap
          (fun τ => Formalism.L2.DIV.fockBL (MvPolynomial.monomial (v τ) (1 : ℂ))) := by
      refine Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials (Fin n × Fin n) ℂ) fun w => ?_
      simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, Formalism.MainNotions.product_first_zeroth_parts.tenM_apply, Formalism.L2.DIV.fockBL_apply,
        MvPolynomial.coe_basisMonomials]
      exact fockB_ten_monomial_eq_prod v w
    have := congrArg (fun F => F g) key
    simpa only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, Formalism.MainNotions.product_first_zeroth_parts.tenM_apply, Formalism.L2.DIV.fockBL_apply] using this
  have key : ((Formalism.L2.DIV.fockBL (K := ℂ)).flip (Formalism.MainNotions.product_first_zeroth_parts.ten g)).compMultilinearMap
        (Formalism.MainNotions.product_first_zeroth_parts.tenM (ι := ι) n) =
      (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap (fun τ => (Formalism.L2.DIV.fockBL (K := ℂ)).flip (g τ)) := by
    refine Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials (Fin n × Fin n) ℂ) fun v => ?_
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, Formalism.MainNotions.product_first_zeroth_parts.tenM_apply, LinearMap.flip_apply,
      Formalism.L2.DIV.fockBL_apply, MvPolynomial.coe_basisMonomials]
    exact h1 v g
  have := congrArg (fun F => F f) key
  simpa only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Formalism.MainNotions.product_first_zeroth_parts.tenM_apply, LinearMap.flip_apply,
    Formalism.L2.DIV.fockBL_apply] using this

private theorem toUnit_eq_ten_const {N : ℕ} (f : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.L2.Ker.toUnit ℂ N f = Formalism.MainNotions.product_first_zeroth_parts.ten (fun _ : Unit => f) := by
  unfold Formalism.L2.Ker.toUnit Formalism.MainNotions.product_first_zeroth_parts.ten
  rw [MvPolynomial.renameEquiv_apply, Fintype.prod_unique]
  rfl

private theorem fockB_toUnit_toUnit {N : ℕ} (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.L2.DIV.fockB (Formalism.L2.Ker.toUnit ℂ N f) (Formalism.L2.Ker.toUnit ℂ N g) = Formalism.L2.DIV.fockB f g := by
  rw [toUnit_eq_ten_const, toUnit_eq_ten_const, fockB_ten_eq_prod, Fintype.prod_unique]

private theorem ten_smul_eq_prod_smul {ι : Type} [Fintype ι] {n : ℕ} (c : ι → ℂ)
    (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => c τ • f τ) = (∏ τ, c τ) • Formalism.MainNotions.product_first_zeroth_parts.ten f := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ten
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.rename_C, Finset.prod_mul_distrib, map_prod]

private theorem fockB_proj_of_isUnit_gramB {κ : Type} [Fintype κ] {m : ℕ} (lam : κ → DomWeight m)
    (hG : IsUnit (Formalism.L2.Col.Br.gramB (K := ℂ) lam).det) (x : Formalism.L2.DIV.Pol ℂ κ m)
    (j : Formalism.L2.DIV.VVIdx lam) :
    Formalism.L2.DIV.fockB (Formalism.L2.DIV.bVVfun ℂ lam j) (Formalism.L2.Col.Br.projVV lam x : Formalism.L2.DIV.Pol ℂ κ m) =
      Formalism.L2.DIV.fockB (Formalism.L2.DIV.bVVfun ℂ lam j) x := by
  classical
  unfold Formalism.L2.Col.Br.projVV
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    Submodule.coe_sum, Submodule.coe_smul, Formalism.L2.DIV.bVV_coe, Formalism.L2.DIV.fockBL_apply]
  rw [← Formalism.L2.DIV.fockBL_apply]
  simp only [map_sum, map_smul, smul_eq_mul, Formalism.L2.DIV.fockBL_apply]
  have e1 : ∀ i, Formalism.L2.DIV.fockB (Formalism.L2.DIV.bVVfun ℂ lam j) (Formalism.L2.DIV.bVVfun ℂ lam i) =
      Formalism.L2.Col.Br.gramB (K := ℂ) lam j i := fun i => rfl
  simp_rw [e1]
  rw [Finset.sum_comm]
  have e2 : ∀ k, ∑ i, (Formalism.L2.Col.Br.gramB (K := ℂ) lam)⁻¹ i k *
      (Formalism.L2.DIV.fockB (Formalism.L2.DIV.bVVfun ℂ lam k) x * Formalism.L2.Col.Br.gramB (K := ℂ) lam j i) =
      (Formalism.L2.Col.Br.gramB (K := ℂ) lam * (Formalism.L2.Col.Br.gramB (K := ℂ) lam)⁻¹) j k *
        Formalism.L2.DIV.fockB (Formalism.L2.DIV.bVVfun ℂ lam k) x := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [e2, Matrix.mul_nonsing_inv _ hG, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem proj_unique_of_isUnit_gramB {κ : Type} [Fintype κ] {m : ℕ} (lam : κ → DomWeight m)
    (hG : IsUnit (Formalism.L2.Col.Br.gramB (K := ℂ) lam).det) (x v : Formalism.L2.DIV.Pol ℂ κ m)
    (hv : v ∈ Formalism.L2.DIV.VV ℂ lam)
    (h : ∀ j, Formalism.L2.DIV.fockB (Formalism.L2.DIV.bVVfun ℂ lam j) v = Formalism.L2.DIV.fockB (Formalism.L2.DIV.bVVfun ℂ lam j) x) :
    (Formalism.L2.Col.Br.projVV lam x : Formalism.L2.DIV.Pol ℂ κ m) = v := by
  classical
  have hd0 : ∀ j, Formalism.L2.DIV.fockB (Formalism.L2.DIV.bVVfun ℂ lam j)
      ((Formalism.L2.Col.Br.projVV lam x - ⟨v, hv⟩ : Formalism.L2.DIV.VV ℂ lam) : Formalism.L2.DIV.Pol ℂ κ m) = 0 := by
    intro j
    rw [Submodule.coe_sub, ← Formalism.L2.DIV.fockBL_apply, map_sub, Formalism.L2.DIV.fockBL_apply,
      Formalism.L2.DIV.fockBL_apply, fockB_proj_of_isUnit_gramB lam hG x j, Submodule.coe_mk, h j, sub_self]
  have hc : Formalism.L2.Col.Br.gramB (K := ℂ) lam *ᵥ
      ((Formalism.L2.DIV.bVV ℂ lam).repr (Formalism.L2.Col.Br.projVV lam x - ⟨v, hv⟩) : Formalism.L2.DIV.VVIdx lam → ℂ) = 0 := by
    funext j
    have := hd0 j
    rw [← (Formalism.L2.DIV.bVV ℂ lam).sum_repr (Formalism.L2.Col.Br.projVV lam x - ⟨v, hv⟩)] at this
    simp only [Submodule.coe_sum, Submodule.coe_smul, Formalism.L2.DIV.bVV_coe] at this
    rw [← Formalism.L2.DIV.fockBL_apply, map_sum] at this
    simp only [map_smul, smul_eq_mul, Formalism.L2.DIV.fockBL_apply] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    rfl
  have hc0 : ((Formalism.L2.DIV.bVV ℂ lam).repr (Formalism.L2.Col.Br.projVV lam x - ⟨v, hv⟩) :
      Formalism.L2.DIV.VVIdx lam → ℂ) = 0 := by
    have := congrArg (fun w => (Formalism.L2.Col.Br.gramB (K := ℂ) lam)⁻¹ *ᵥ w) hc
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG] using this
  have hd : Formalism.L2.Col.Br.projVV lam x - ⟨v, hv⟩ = 0 := by
    apply (Formalism.L2.DIV.bVV ℂ lam).repr.injective
    rw [map_zero]
    ext i
    exact congrFun hc0 i
  have := congrArg Subtype.val (sub_eq_zero.mp hd)
  simpa using this

private theorem map_conj_ssB {n : ℕ} (ν : Fin n → ℕ) (i : Formalism.GradedWeylDivisibility.ssIdx n n ν) :
    MvPolynomial.map (starRingEnd ℂ) (Formalism.L2.DIV.ssB ℂ ν i) = Formalism.L2.DIV.ssB ℂ ν i := by
  obtain ⟨K, sz, hsz, I, -, -, hb⟩ := ((Formalism.GradedWeylDivisibility.sSBasis ℂ n n ν).choose_spec.2 i).2.2
  unfold Formalism.L2.DIV.ssB
  rw [hb]
  unfold Formalism.GradedWeylDivisibility.bideterminant Formalism.GradedWeylDivisibility.initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.map_X]

private theorem map_conj_bVVfun {κ : Type} [Fintype κ] {m : ℕ} (lam : κ → DomWeight m)
    (i : Formalism.L2.DIV.VVIdx lam) :
    MvPolynomial.map (starRingEnd ℂ) (Formalism.L2.DIV.bVVfun ℂ lam i) = Formalism.L2.DIV.bVVfun ℂ lam i := by
  unfold Formalism.L2.DIV.bVVfun Formalism.L2.DIV.ten
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  unfold Formalism.GradedWeylDivisibility.blockEmb
  rw [MvPolynomial.map_rename, map_conj_ssB]

private theorem fockB_eq_fockS_of_map_conj_eq {σ : Type} (f g : MvPolynomial σ ℂ)
    (hf : MvPolynomial.map (starRingEnd ℂ) f = f) :
    Formalism.L2.DIV.fockB f g = Formalism.L2.DIV.fockS f g := by
  unfold Formalism.L2.DIV.fockB Formalism.L2.DIV.fockS
  refine Finset.sum_congr rfl fun m _ => ?_
  have := congrArg (MvPolynomial.coeff m) hf
  rw [MvPolynomial.coeff_map, starRingEnd_apply] at this
  rw [this]

private theorem eq_zero_of_fockS_self_eq_zero {σ : Type} (w : MvPolynomial σ ℂ) (h : Formalism.L2.DIV.fockS w w = 0) :
    w = 0 := by
  classical
  have hre := congrArg Complex.re h
  unfold Formalism.L2.DIV.fockS at hre
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hterm : ∀ m ∈ w.support, (star (w.coeff m) * w.coeff m * (Formalism.L2.DIV.mfact m : ℂ)).re =
      Complex.normSq (w.coeff m) * (Formalism.L2.DIV.mfact m : ℝ) := by
    intro m _
    have e : star (w.coeff m) * w.coeff m = (Complex.normSq (w.coeff m) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    rw [e, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Finset.sum_congr rfl hterm] at hre
  have hnn : ∀ m ∈ w.support, 0 ≤ Complex.normSq (w.coeff m) * (Formalism.L2.DIV.mfact m : ℝ) :=
    fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at hre
  by_contra hw
  obtain ⟨m, hm⟩ : w.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hw
  have h2 := hre m hm
  rcases mul_eq_zero.mp h2 with h1 | h1
  · exact (MvPolynomial.mem_support_iff.mp hm) (Complex.normSq_eq_zero.mp h1)
  · have hne : (Formalism.L2.DIV.mfact m : ℝ) ≠ 0 := by
      have : Formalism.L2.DIV.mfact m ≠ 0 := by
        unfold Formalism.L2.DIV.mfact
        exact Finset.prod_ne_zero_iff.mpr fun k _ => Nat.factorial_ne_zero _
      exact_mod_cast this
    exact hne h1

private theorem isUnit_gramB {κ : Type} [Fintype κ] {m : ℕ} (lam : κ → DomWeight m) :
    IsUnit (Formalism.L2.Col.Br.gramB (K := ℂ) lam).det := by
  classical
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  have hS : ∀ y : Formalism.L2.DIV.Pol ℂ κ m, Formalism.L2.DIV.fockL (∑ i, v i • Formalism.L2.DIV.bVVfun ℂ lam i) y =
      ∑ i, star (v i) * Formalism.L2.DIV.fockL (Formalism.L2.DIV.bVVfun ℂ lam i) y := by
    intro y
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  have hz : ∀ i, Formalism.L2.DIV.fockL (Formalism.L2.DIV.bVVfun ℂ lam i) (∑ j, v j • Formalism.L2.DIV.bVVfun ℂ lam j) = 0 := by
    intro i
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, Formalism.L2.DIV.fockL_apply]
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← fockB_eq_fockS_of_map_conj_eq _ _ (map_conj_bVVfun lam i), mul_comm]
    rfl
  have hw : (∑ j, v j • Formalism.L2.DIV.bVVfun ℂ lam j) = 0 := by
    apply eq_zero_of_fockS_self_eq_zero
    rw [← Formalism.L2.DIV.fockL_apply, hS]
    simp only [hz, mul_zero, Finset.sum_const_zero]
  funext i
  exact Fintype.linearIndependent_iff.mp (Formalism.L2.DIV.bVVfun_spec ℂ lam).1 v hw i

private theorem toUnit_ssB_eq_bVVfun {n : ℕ} (s : DomWeight n) (a : Formalism.GradedWeylDivisibility.ssIdx n n s.natW) :
    Formalism.L2.Ker.toUnit ℂ n (Formalism.L2.DIV.ssB ℂ s.natW a) =
      Formalism.L2.DIV.bVVfun ℂ (fun _ : Unit => s) (fun _ => a) := by
  rw [toUnit_eq_ten_const]
  rfl

private theorem toUnit_symm_mem_nablaSq_of_mem_VV {n : ℕ} (s : DomWeight n) (P : Formalism.L2.DIV.Pol ℂ Unit n)
    (hP : P ∈ Formalism.L2.DIV.VV ℂ (fun _ : Unit => s)) :
    (Formalism.L2.Ker.toUnit ℂ n).symm P ∈ nablaSq ℂ n s := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have e : (∏ u : Unit, Formalism.GradedWeylDivisibility.blockEmb ℂ u (F u)) = Formalism.L2.Ker.toUnit ℂ n (F ()) := by
      rw [toUnit_eq_ten_const]
      rfl
    rw [e, AlgEquiv.symm_apply_apply]
    exact hF ()
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ a hx

private theorem toUnit_monomial {N : ℕ} (a : Fin N × Fin N →₀ ℕ) :
    Formalism.L2.Ker.toUnit ℂ N (MvPolynomial.monomial a 1) =
      MvPolynomial.monomial (a.mapDomain (Prod.mk ())) 1 := by
  rw [toUnit_eq_ten_const]
  unfold Formalism.MainNotions.product_first_zeroth_parts.ten
  rw [Fintype.prod_unique, MvPolynomial.rename_monomial]

private theorem toUnit_symm_monomial {n : ℕ} (W : Unit × Fin n × Fin n →₀ ℕ) :
    (Formalism.L2.Ker.toUnit ℂ n).symm (MvPolynomial.monomial W 1) =
      MvPolynomial.monomial (W.comapDomain (Prod.mk ()) (Prod.mk_right_injective ()).injOn) 1 := by
  have e : (W.comapDomain (Prod.mk ()) (Prod.mk_right_injective ()).injOn).mapDomain (Prod.mk ()) = W := by
    ext ⟨u, x⟩
    cases u
    rw [Finsupp.mapDomain_apply (Prod.mk_right_injective ()), Finsupp.comapDomain_apply]
  apply (Formalism.L2.Ker.toUnit ℂ n).injective
  rw [AlgEquiv.apply_symm_apply, toUnit_monomial, e]

private theorem coefLast_monomial' {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (M : ι × Fin N × Fin N →₀ ℕ) :
    Formalism.L2.Col.Br.coefLast (K := ℂ) hN (Formalism.L2.Col.Br.bExp hN lam sg) (MvPolynomial.monomial M 1) =
      Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => (Formalism.L2.Ker.toUnit ℂ n).symm
        (Formalism.L2.Col.Br.coefLast hN (Formalism.L2.Col.Br.bExp hN (fun _ : Unit => lam τ) (fun _ : Unit => sg τ))
          (Formalism.L2.Ker.toUnit ℂ N
            (MvPolynomial.monomial (M.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) 1)))) := by
  classical
  have hev : ∀ (τ : ι) (u : Unit) (x : Fin N × Fin N),
      ((M.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn).mapDomain (Prod.mk ())) (u, x) =
        M (τ, x) := by
    intro τ u x
    cases u
    rw [Finsupp.mapDomain_apply (Prod.mk_right_injective ()), Finsupp.comapDomain_apply]
  have hiff : Formalism.L2.Col.Br.IsTop hN (Formalism.L2.Col.Br.bExp hN lam sg) M ↔
      ∀ τ, Formalism.L2.Col.Br.IsTop hN (Formalism.L2.Col.Br.bExp hN (fun _ : Unit => lam τ) (fun _ : Unit => sg τ))
        ((M.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn).mapDomain (Prod.mk ())) := by
    unfold Formalism.L2.Col.Br.IsTop
    simp only [hev]
    constructor
    · rintro ⟨h1, h2⟩ τ
      exact ⟨fun _ s => h1 τ s, fun _ a => h2 τ a⟩
    · intro h
      exact ⟨fun τ s => (h τ).1 () s, fun τ a => (h τ).2 () a⟩
  rw [Formalism.L2.Col.Br.coefLast_monomial]
  simp_rw [toUnit_monomial, Formalism.L2.Col.Br.coefLast_monomial, apply_ite (Formalism.L2.Ker.toUnit ℂ n).symm,
    map_zero, toUnit_symm_monomial]
  by_cases hT : Formalism.L2.Col.Br.IsTop hN (Formalism.L2.Col.Br.bExp hN lam sg) M
  · rw [if_pos hT]
    have hT' := hiff.mp hT
    simp only [hT', if_true]
    rw [Formalism.MainNotions.product_first_zeroth_parts.ten_monomial]
    refine congrArg (fun A => MvPolynomial.monomial A (1 : ℂ)) ?_
    ext ⟨τ, a, s⟩
    rw [sum_mapDomain_prodMk_apply]
    simp only [Finsupp.comapDomain_apply]
    exact (hev τ () _).symm
  · rw [if_neg hT]
    obtain ⟨τ, hτ⟩ := not_forall.mp (mt hiff.mpr hT)
    unfold Formalism.MainNotions.product_first_zeroth_parts.ten
    refine (Finset.prod_eq_zero (Finset.mem_univ τ) ?_).symm
    dsimp only
    rw [if_neg hτ, map_zero]

private theorem ten_brOne_monomial_eq_brStdP {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (M : ι × Fin N × Fin N →₀ ℕ) :
    Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => Formalism.L2.Ker.brOne ℂ hN (lam τ) (sg τ)
              (MvPolynomial.monomial (M.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) 1)) =
      (Br.brStdP hN lam sg (MvPolynomial.monomial M (1 : ℂ)) : Pol ℂ ι n) := by
  have hL : ∀ τ, Formalism.L2.Ker.brOne ℂ hN (lam τ) (sg τ)
        (MvPolynomial.monomial (M.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) 1) =
      Formalism.L2.Col.Br.brConst hN ℂ (fun _ : Unit => lam τ) (fun _ : Unit => sg τ) •
        (Formalism.L2.Ker.toUnit ℂ n).symm
          (Formalism.L2.Col.Br.projVV (fun _ : Unit => sg τ)
            (Formalism.L2.Col.Br.coefLast hN (Formalism.L2.Col.Br.bExp hN (fun _ : Unit => lam τ) (fun _ : Unit => sg τ))
              (Formalism.L2.Ker.toUnit ℂ N
                (MvPolynomial.monomial (M.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) 1))) :
            Formalism.L2.DIV.Pol ℂ Unit n) := by
    intro τ
    simp only [Formalism.L2.Ker.brOne, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
      Submodule.coe_subtype]
    rw [Formalism.L2.Col.Br.brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul, map_smul]
  simp_rw [hL]
  rw [ten_smul_eq_prod_smul, Formalism.L2.Col.Br.brStdP, LinearMap.smul_apply, LinearMap.comp_apply,
    Submodule.coe_smul, coefLast_monomial']
  have hc : (∏ τ, Formalism.L2.Col.Br.brConst hN ℂ (fun _ : Unit => lam τ) (fun _ : Unit => sg τ)) =
      Formalism.L2.Col.Br.brConst hN ℂ lam sg := by
    unfold Formalism.L2.Col.Br.brConst
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Fintype.prod_unique]
  rw [hc]
  congr 1
  symm
  apply proj_unique_of_isUnit_gramB sg (isUnit_gramB sg)
  · show _ ∈ Formalism.GradedWeylDivisibility.tensorLat ℂ ℂ _
    exact Submodule.subset_span ⟨_, fun τ => toUnit_symm_mem_nablaSq_of_mem_VV (sg τ) _ (Submodule.coe_mem _), rfl⟩
  · intro j
    rw [show Formalism.L2.DIV.bVVfun ℂ sg j = Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => Formalism.L2.DIV.ssB ℂ (sg τ).natW (j τ)) from rfl,
      fockB_ten_eq_prod, fockB_ten_eq_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← fockB_toUnit_toUnit, ← fockB_toUnit_toUnit (Formalism.L2.DIV.ssB ℂ (sg τ).natW (j τ)),
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, toUnit_ssB_eq_bVVfun]
    exact fockB_proj_of_isUnit_gramB (fun _ : Unit => sg τ) (isUnit_gramB _) _ (fun _ => j τ)

theorem blk_brOne_eq : ∀ {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (p : Pol ℂ ι N), Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => Formalism.L2.Ker.brOne ℂ hN (lam τ) (sg τ)) p = (Br.brStdP hN lam sg p : Pol ℂ ι n) := by
  intro ι _ N n hN lam sg p
  have hlin : Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(Formalism.L2.Ker.brOne ℂ hN (lam τ) (sg τ))) =
      (Formalism.L2.DIV.VV ℂ sg).subtype ∘ₗ Br.brStdP hN lam sg := by
    refine (MvPolynomial.basisMonomials (ι × Fin N × Fin N) ℂ).ext fun M => ?_
    rw [LinearMap.comp_apply, Submodule.subtype_apply]
    unfold Formalism.MainNotions.product_first_zeroth_parts.blk
    rw [Module.Basis.constr_basis]
    simp only [MvPolynomial.coe_basisMonomials]
    exact ten_brOne_monomial_eq_brStdP hN lam sg M
  exact LinearMap.congr_fun hlin p

end GlobalTheory.Proof.FockBlockMonotone
