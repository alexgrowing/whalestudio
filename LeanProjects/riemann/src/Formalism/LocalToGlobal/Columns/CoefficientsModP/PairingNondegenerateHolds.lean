import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

open MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

open scoped MatrixOrder in

theorem ps_factor {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ T = B * Bᴴ := by
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ T := Matrix.nonneg_iff_posSemidef.2 hT.posSemidef
  refine ⟨CFC.sqrt T, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero]
    intro hz
    have hdet := hT.det_pos
    rw [← CFC.sqrt_mul_sqrt_self T h0, Matrix.det_mul, hz, zero_mul] at hdet
    exact lt_irrefl _ hdet
  · have hsa : (CFC.sqrt T)ᴴ = CFC.sqrt T := (CFC.sqrt_nonneg T).isSelfAdjoint.star_eq
    rw [hsa, CFC.sqrt_mul_sqrt_self T h0]

theorem ps_blockAct_injective {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}
    (B : ι → Matrix (Fin n) (Fin n) K) (hB : ∀ τ, IsUnit (B τ).det) :
    Function.Injective (Formalism.GradedWeylDivisibility.blockAct K (n := n) B) := by
  classical
  let Bi : ι → Matrix (Fin n) (Fin n) K := fun τ => (B τ)⁻¹
  have hcomp : (Formalism.GradedWeylDivisibility.blockAct K (n := n) Bi).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) B) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, a, j⟩
    have hBB : B τ * Bi τ = 1 := Matrix.mul_nonsing_inv _ (hB τ)
    simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    simp only [Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← map_sum]
    have hc : ∀ c : Fin n, ∑ b : Fin n, B τ a b * Bi τ b c = (1 : Matrix (Fin n) (Fin n) K) a c := by
      intro c
      rw [← hBB, Matrix.mul_apply]
    simp only [hc, Matrix.one_apply]
    simp [apply_ite C, ite_mul]
  intro x y hxy
  have := congrArg (Formalism.GradedWeylDivisibility.blockAct K (n := n) Bi) hxy
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp] at this
  simpa using this

theorem ps_fockF_pos {σ : Type} (f : MvPolynomial σ ℂ) (hf : f ≠ 0) : 0 < Formalism.REAL.fockF f f := by
  unfold Formalism.REAL.fockF
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hf
  apply Finset.sum_pos _ hne
  intro m hm
  have hc : f.coeff m ≠ 0 := MvPolynomial.mem_support_iff.1 hm
  have h1 : f.coeff m * star (f.coeff m) = ((Complex.normSq (f.coeff m) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  rw [h1]
  have h2 : (0 : ℝ) < Complex.normSq (f.coeff m) := Complex.normSq_pos.2 hc
  have h3 : (0 : ℝ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
  have e : ((Complex.normSq (f.coeff m) : ℝ) : ℂ) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
      ((Complex.normSq (f.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e]
  exact Complex.zero_lt_real.2 (mul_pos h2 h3)

theorem ps_nfL_pos {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hF : F ≠ 0) : 0 < Formalism.L2.Col.nfL lam F F := by
  rw [Formalism.L2.Col.nfL_apply, Formalism.L2.Forms.nfAll]
  refine div_pos (ps_fockF_pos F hF) (Finset.prod_pos fun τ _ => ?_)
  exact ps_fockF_pos _ (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _)

theorem ps_nfL_symm {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F F' : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    star (Formalism.L2.Col.nfL lam F F') = Formalism.L2.Col.nfL lam F' F := by
  rw [Formalism.L2.Col.nfL_apply, Formalism.L2.Col.nfL_apply, Formalism.L2.Forms.nfAll, Formalism.L2.Forms.nfAll, star_div₀,
    ← Formalism.GradedWeylDivisibility.fockHerm, star_prod]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact (Formalism.GradedWeylDivisibility.fockHerm _ _ _).symm

theorem pairingPositive_holds : PairPos := by
  classical
  intro K _ _ ι _ n lam G φ hG
  choose B hBu hB using fun τ => ps_factor (hG τ).transpose
  set P : VVIdx lam → MvPolynomial (ι × Fin n × Fin n) ℂ :=
    fun i => Formalism.GradedWeylDivisibility.blockAct ℂ B (map φ (bVVfun K lam i)) with hP
  set c : ℂ := ∏ τ, ((G τ).map φ).det ^ (lam τ).detShift with hc
  have hM : ∀ i j, φ (pairK lam G (bVV K lam i) (bVV K lam j)) = c * Formalism.L2.Col.nfL lam (P i) (P j) := by
    intro i j
    rw [pairK_apply, bVV_coe, bVV_coe, Formalism.L2.Col.map_pairP φ lam G B hB _ _ ?_, Formalism.L2.Col.nfL_apply]
    intro m
    obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
    rw [hQ, coeff_map]
    simp
  have hli : LinearIndependent ℂ P := by
    have h1 := Formalism.L2.Col.linearIndependent_map φ (bVVfun K lam) (bVVfun_spec K lam).1
    exact h1.map' (Formalism.GradedWeylDivisibility.blockAct ℂ B).toLinearMap (LinearMap.ker_eq_bot.mpr (ps_blockAct_injective B hBu))
  have hcpos : 0 < c := Finset.prod_pos fun τ _ => zpow_pos (hG τ).det_pos _
  have hcs : star c = c := (IsSelfAdjoint.of_nonneg hcpos.le).star_eq
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, hM, hM, star_mul', hcs, ps_nfL_symm]
  · intro x hx
    have e : star x ⬝ᵥ (Matrix.of fun i j : VVIdx lam => φ (pairK lam G (bVV K lam i) (bVV K lam j))) *ᵥ x =
        c * Formalism.L2.Col.nfL lam (∑ i, x i • P i) (∑ j, x j • P j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, hM, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
        LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    refine mul_pos hcpos (ps_nfL_pos lam _ ?_)
    intro h0
    exact hx (funext fun i => Fintype.linearIndependent_iff.mp hli x h0 i)

theorem ps_fockL_rat {σ : Type} (f g : MvPolynomial σ ℚ) : fockL f g = Formalism.GradedWeylDivisibility.fockQ f g := by
  show Formalism.L2.DIV.fockS f g = Formalism.GradedWeylDivisibility.fockQ f g
  unfold Formalism.L2.DIV.fockS Formalism.GradedWeylDivisibility.fockQ
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_trivial]
  rfl

private lemma fockQ_eq_sum_coeff_mul_factorial {σ : Type} (f g : MvPolynomial σ ℚ) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    Formalism.GradedWeylDivisibility.fockQ f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold Formalism.GradedWeylDivisibility.fockQ
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm]
  ring

theorem ps_gram_det_ne {σ κ : Type} [Fintype κ] [DecidableEq κ] (q : κ → MvPolynomial σ ℚ)
    (hq : LinearIndependent ℚ q) : (Matrix.of fun i j => Formalism.GradedWeylDivisibility.fockQ (q i) (q j)).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set S : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun i => (q i).support with hS
  set w : (σ →₀ ℕ) → ℚ := fun m => ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) with hw
  set p : MvPolynomial σ ℚ := ∑ j, v j • q j with hp
  have hpc : ∀ m, p.coeff m = ∑ j, v j * (q j).coeff m := by
    intro m
    simp [hp, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]
  have hsub : ∀ i, (q i).support ⊆ S := fun i =>
    Finset.subset_biUnion_of_mem (fun j => (q j).support) (Finset.mem_univ i)
  have hwpos : ∀ m, 0 < w m := fun m => by
    simp only [hw]
    exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
  have e1 : ∀ i, ∑ j, Formalism.GradedWeylDivisibility.fockQ (q i) (q j) * v j = 0 := by
    intro i
    have := congrFun hv i
    simpa [Matrix.mulVec, dotProduct] using this
  have hexp : ∀ m, p.coeff m * p.coeff m * w m =
      ∑ i, ∑ j, v i * (q i).coeff m * (v j * (q j).coeff m) * w m := by
    intro m
    rw [hpc, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  have hkey : ∑ m ∈ S, p.coeff m * p.coeff m * w m = 0 := by
    calc ∑ m ∈ S, p.coeff m * p.coeff m * w m
        = ∑ m ∈ S, ∑ i, ∑ j, v i * (q i).coeff m * (v j * (q j).coeff m) * w m :=
          Finset.sum_congr rfl fun m _ => hexp m
      _ = ∑ i, ∑ m ∈ S, ∑ j, v i * (q i).coeff m * (v j * (q j).coeff m) * w m := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ m ∈ S, v i * (q i).coeff m * (v j * (q j).coeff m) * w m :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, v i * ∑ j, Formalism.GradedWeylDivisibility.fockQ (q i) (q j) * v j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [fockQ_eq_sum_coeff_mul_factorial (q i) (q j) S (hsub i), Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [hw]
          ring
      _ = 0 := by simp [e1]
  have hzero : ∀ m ∈ S, p.coeff m = 0 := by
    have hnn : ∀ m ∈ S, 0 ≤ p.coeff m * p.coeff m * w m :=
      fun m _ => mul_nonneg (mul_self_nonneg _) (hwpos m).le
    intro m hm
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hkey m hm
    rcases mul_eq_zero.1 h0 with h | h
    · exact mul_self_eq_zero.1 h
    · exact absurd h (hwpos m).ne'
  have hp0 : p = 0 := by
    ext m
    by_cases hm : m ∈ S
    · simpa using hzero m hm
    · rw [hpc, MvPolynomial.coeff_zero]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj : m ∉ (q j).support := fun h => hm (hsub j h)
      rw [MvPolynomial.notMem_support_iff.1 hj, mul_zero]
  have hv' := (Fintype.linearIndependent_iff.1 hq) v (by rw [← hp]; exact hp0)
  exact hv0 (funext hv')

theorem ps_bVVfun_rat (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (i : VVIdx lam) : ∃ q : MvPolynomial (ι × Fin n × Fin n) ℚ, bVVfun K lam i = map (algebraMap ℚ K) q := by
  obtain ⟨P, hP⟩ := bVVfun_int K lam i
  refine ⟨map (Int.castRingHom ℚ) P, ?_⟩
  rw [hP, map_map]
  have e : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K := RingHom.ext_int _ _
  rw [e]

theorem ps_fock_sep {K : Type} [Field K] [StarRing K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (x : Pol K ι n) (hx : x ∈ VV K lam) (h : ∀ y ∈ VV K lam, fockL x y = 0) : x = 0 := by
  classical
  choose q hq using ps_bVVfun_rat K lam
  have hli : LinearIndependent ℚ q := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg (map (algebraMap ℚ K)) hg
    simp only [map_sum, smul_eq_C_mul, map_mul, map_C, ← hq, map_zero] at h1
    simp only [← smul_eq_C_mul] at h1
    have h2 := Fintype.linearIndependent_iff.mp (bVVfun_spec K lam).1 (fun i => algebraMap ℚ K (g i)) h1 i
    exact (map_eq_zero (algebraMap ℚ K)).mp h2
  have hdet := ps_gram_det_ne q hli
  set Q : Matrix (VVIdx lam) (VVIdx lam) ℚ := Matrix.of fun i j => Formalism.GradedWeylDivisibility.fockQ (q i) (q j) with hQ
  have hdetK : ((algebraMap ℚ K).mapMatrix Q).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact (map_ne_zero (algebraMap ℚ K)).mpr hdet
  set c := (bVV K lam).repr ⟨x, hx⟩ with hc
  have hxc : x = ∑ i, c i • bVVfun K lam i := by
    have h1 := (bVV K lam).sum_repr ⟨x, hx⟩
    have h2 := congrArg (Subtype.val) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe] at h2
    exact h2.symm
  have hv : (fun i => star (c i)) ᵥ* ((algebraMap ℚ K).mapMatrix Q) = 0 := by
    funext j
    have h1 := h (bVVfun K lam j) (by rw [← bVV_coe]; exact (bVV K lam j).2)
    rw [hxc] at h1
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply] at h1
    simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, hQ, Matrix.of_apply, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hq i, hq j, fockL_apply, fockSQ K]
  have hc0 := Matrix.eq_zero_of_vecMul_eq_zero hdetK hv
  rw [hxc]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : star (c i) = 0 := congrFun hc0 i
  rw [star_eq_zero.mp this, zero_smul]

theorem ps_blockAct_mem_VV {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (U : ι → Matrix (Fin n) (Fin n) K) {F : Pol K ι n} (hF : F ∈ VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K U F ∈ VV K lam :=
  (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n U).2 (fun τ => nablaSq K n (lam τ)) (fun τ => nablaSq K n (lam τ))
    (fun _ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ f hf) F hF

theorem pairingNondegenerate_holds : PairNondeg := by
  intro K _ _ _ ι _ n lam G hG
  have hGt : ∀ τ, IsUnit ((G τ)ᵀ).det := fun τ => by rw [Matrix.det_transpose]; exact hG τ
  have hc : gramTw lam G / extNorm K lam ≠ 0 := by
    obtain ⟨r, hr, he⟩ := extNormPos K ι n lam
    refine div_ne_zero ?_ ?_
    · unfold gramTw
      exact Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hG τ).ne_zero
    · rw [he]
      exact (map_ne_zero (algebraMap ℚ K)).mpr hr.ne'
  have e : (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (G τ)ᵀ).comp (Formalism.GradedWeylDivisibility.blockAct K fun τ => ((G τ)ᵀ)⁻¹) =
      AlgHom.id K _ := by
    rw [blockAct_comp, ← blockAct_one]
    congr 1
    funext τ
    exact Matrix.nonsing_inv_mul _ (hGt τ)
  constructor
  · intro x hx
    apply Subtype.ext
    refine ps_fock_sep lam x.1 x.2 fun y hy => ?_
    have h1 := hx ⟨Formalism.GradedWeylDivisibility.blockAct K (fun τ => ((G τ)ᵀ)⁻¹) y, ps_blockAct_mem_VV lam _ hy⟩
    rw [pairK_apply, pairP_apply, ← AlgHom.comp_apply, e] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc
  · intro y hy
    apply Subtype.ext
    have h0 : Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1 = 0 := by
      refine ps_fock_sep lam _ (ps_blockAct_mem_VV lam _ y.2) fun x hx => ?_
      have h1 := hy ⟨x, hx⟩
      rw [pairK_apply, pairP_apply] at h1
      rw [fockL_symm, (mul_eq_zero.mp h1).resolve_left hc, star_zero]
    exact ps_blockAct_injective _ hGt (by rw [h0, Submodule.coe_zero, map_zero])

end Formalism.L2.DIV
