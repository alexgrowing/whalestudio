import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNestedLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

set_option linter.unusedSectionVars false

namespace ChangeOfLattice

section Matrices

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem matAct_mul (A A' : Matrix J J ℚ) (x : J → Ω) : matAct A (matAct A' x) = matAct (A * A') x := by
  funext i
  simp only [matAct, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem matActC_mul (A A' : Matrix J J ℚ) (z : J → ℂ) :
    matActC A (matActC A' z) = matActC (A * A') z := by
  funext i
  simp only [matActC, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem matActC_smul (A : Matrix J J ℚ) (a : ℂ) (z : J → ℂ) : matActC A (a • z) = a • matActC A z := by
  funext i
  simp only [matActC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem matAct_smul_one [DecidableEq J] (q : ℚ) (x : J → Ω) :
    matAct (q • (1 : Matrix J J ℚ)) x = fun i => (q : Ω) * x i := by
  funext i
  simp only [matAct, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

theorem matActC_smul_one [DecidableEq J] (q : ℚ) (z : J → ℂ) :
    matActC (q • (1 : Matrix J J ℚ)) z = (q : ℂ) • z := by
  funext i
  simp only [matActC, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Pi.smul_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

theorem contDiff_matActC {k : WithTop ℕ∞} (A : Matrix J J ℚ) : ContDiff ℝ k (matActC A) := by
  refine contDiff_pi.2 fun i => ?_
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)

theorem matAct_mem_span {A : Matrix J J ℚ} (hA : ∀ i j, ∃ k : ℤ, A i j = k) (x : J → Ω) (i : J) :
    matAct A x i ∈ Submodule.span ℤ (Set.range x) := by
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨k, hk⟩ := hA i j
  rw [hk, Rat.cast_intCast, ← zsmul_eq_mul]
  exact Submodule.smul_mem _ k (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_clear_den (A : Matrix J J ℚ) : ∃ c : ℕ, c ≠ 0 ∧ ∀ i j, ∃ k : ℤ, (c : ℚ) * A i j = k := by
  classical
  refine ⟨∏ i, ∏ j, (A i j).den,
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => (A i j).den_nz, fun i j => ?_⟩
  obtain ⟨t, ht⟩ : (A i j).den ∣ ∏ i, ∏ j, (A i j).den :=
    (Finset.dvd_prod_of_mem (fun j => (A i j).den) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, (A i j).den) (Finset.mem_univ i))
  refine ⟨t * (A i j).num, ?_⟩
  rw [ht]
  push_cast
  rw [mul_comm ((A i j).den : ℚ) t, mul_assoc, Rat.den_mul_eq_num]

theorem isInvMat_of_mul [DecidableEq J] {A A' : Matrix J J ℚ} (h1 : A * A' = 1) (h2 : A' * A = 1) : IsInvMat A :=
  ⟨A', fun v => by simp [Matrix.mulVec_mulVec, h1, h2]⟩

theorem exists_inv_of_isInvMat [DecidableEq J] {A : Matrix J J ℚ} (h : IsInvMat A) :
    ∃ A' : Matrix J J ℚ, A' * A = 1 ∧ A * A' = 1 := by
  obtain ⟨A', hA'⟩ := h
  refine ⟨A', Matrix.toLin'.injective (LinearMap.ext fun v => ?_),
    Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
  · rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, (hA' v).2, Matrix.one_mulVec]
  · rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, (hA' v).1, Matrix.one_mulVec]

end Matrices

section Lattices

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem sec_eq_pow (x : J → Ω) (n : ℕ) : sec ℤ x n = Submodule.span ℤ (Set.range x) ^ n := by
  have e : ⇑(aeval x : MvPolynomial J ℤ →ₐ[ℤ] Ω).toLinearMap '' Set.range (X : J → MvPolynomial J ℤ) =
      Set.range x := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp
  rw [sec, ← homogeneousSubmodule_one_pow, Submodule.map_pow, homogeneousSubmodule_one_eq_span_X,
    Submodule.map_span, e]

theorem sec_mono {x x' : J → Ω}
    (h : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range x')) (n : ℕ) :
    sec ℤ x n ≤ sec ℤ x' n := by
  rw [sec_eq_pow, sec_eq_pow]
  exact pow_le_pow_left' h n

theorem smul_pow_mem {L M : Submodule ℤ Ω} {N : ℤ} (h : ∀ l ∈ L, N • l ∈ M) (n : ℕ) :
    ∀ s ∈ L ^ n, N ^ n • s ∈ M ^ n := by
  induction n with
  | zero =>
    intro s hs
    rw [pow_zero] at hs ⊢
    rwa [pow_zero, one_smul]
  | succ n ih =>
    intro s hs
    rw [pow_succ] at hs ⊢
    refine Submodule.mul_induction_on hs (fun a ha b hb => ?_) (fun u v hu hv => ?_)
    · have e : N ^ (n + 1) • (a * b) = (N ^ n • a) * (N • b) := by
        simp only [zsmul_eq_mul]
        push_cast
        ring
      rw [e]
      exact Submodule.mul_mem_mul (ih a ha) (h b hb)
    · rw [smul_add]
      exact add_mem hu hv

theorem relIndex_ne_zero {H K : Submodule ℤ Ω} (hK : K.FG) {N : ℤ} (hN : N ≠ 0) (h : ∀ k ∈ K, N • k ∈ H) :
    H.toAddSubgroup.relIndex K.toAddSubgroup ≠ 0 := by
  rw [AddSubgroup.relIndex]
  have : AddGroup.FG K.toAddSubgroup :=
    (AddGroup.fg_iff_addSubgroup_fg _).2 ((Submodule.fg_iff_addSubgroup_fg K).1 hK)
  have : Module.Finite ℤ (K.toAddSubgroup ⧸ H.toAddSubgroup.addSubgroupOf K.toAddSubgroup) :=
    Module.Finite.iff_addGroup_fg.2 inferInstance
  have : Finite (K.toAddSubgroup ⧸ H.toAddSubgroup.addSubgroupOf K.toAddSubgroup) := by
    refine Module.finite_of_fg_torsion _ fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H k =>
      refine ⟨⟨N, mem_nonZeroDivisors_of_ne_zero hN⟩, ?_⟩
      show N • (k : K.toAddSubgroup ⧸ H.toAddSubgroup.addSubgroupOf K.toAddSubgroup) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact h k k.2
  exact AddSubgroup.index_ne_zero_of_finite

theorem relIndex_sec_ne_zero {y z : J → Ω} {N : ℤ} (hN : N ≠ 0)
    (h : ∀ i, N • y i ∈ Submodule.span ℤ (Set.range z)) (n : ℕ) :
    (sec ℤ z n).toAddSubgroup.relIndex (sec ℤ y n).toAddSubgroup ≠ 0 := by
  rw [sec_eq_pow, sec_eq_pow]
  refine relIndex_ne_zero ((Submodule.fg_span (Set.finite_range y)).pow n) (pow_ne_zero n hN)
    (smul_pow_mem (fun l hl => ?_) n)
  have hle : Submodule.span ℤ (Set.range y) ≤
      (Submodule.span ℤ (Set.range z)).comap (N • LinearMap.id) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun i => by simpa using h i)
  simpa using hle hl

theorem log_relIndex_cocycle {M L L' : AddSubgroup Ω} (hL : M ≤ L) (hL' : M ≤ L')
    (h1 : M.relIndex L ≠ 0) (h2 : M.relIndex L' ≠ 0) :
    Real.log (L.relIndex L') - Real.log (L'.relIndex L) =
      Real.log (M.relIndex L') - Real.log (M.relIndex L) := by
  have e1 := AddSubgroup.relIndex_mul_relIndex M (L ⊓ L') L' (le_inf hL hL') inf_le_right
  have e2 := AddSubgroup.relIndex_mul_relIndex M (L ⊓ L') L (le_inf hL hL') inf_le_left
  rw [AddSubgroup.inf_relIndex_right] at e1
  rw [AddSubgroup.inf_relIndex_left] at e2
  rw [← e1] at h2 ⊢
  rw [← e2] at h1 ⊢
  have ha : (M.relIndex (L ⊓ L') : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (left_ne_zero_of_mul h2)
  have hb : (L.relIndex L' : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul h2)
  have hb' : (L'.relIndex L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul h1)
  push_cast
  rw [Real.log_mul ha hb, Real.log_mul ha hb']
  ring

theorem coordIdeal_const_mul {c : Ω} (hc : c ≠ 0) (x : J → Ω) :
    coordIdeal ℤ (fun i => c * x i) = coordIdeal ℤ x := by
  have key : ((Polynomial.aeval (Polynomial.C c * Polynomial.X : Polynomial Ω)).restrictScalars ℤ).comp
      (coneMap ℤ x) = coneMap ℤ (fun i => c * x i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [coneMap, Polynomial.C_mul]
    ring
  have back : ∀ p : Polynomial Ω,
      (Polynomial.aeval (Polynomial.C c * Polynomial.X) p).comp (Polynomial.C c⁻¹ * Polynomial.X) = p := by
    intro p
    rw [← Polynomial.comp_eq_aeval, Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_comp, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul,
      Polynomial.comp_X]
  ext f
  show f ∈ RingHom.ker (coneMap ℤ _) ↔ f ∈ RingHom.ker (coneMap ℤ x)
  rw [RingHom.mem_ker, RingHom.mem_ker, ← key, AlgHom.comp_apply, AlgHom.restrictScalars_apply]
  constructor
  · intro h0
    rw [← back (coneMap ℤ x f), h0, Polynomial.zero_comp]
  · intro h0
    rw [h0, map_zero]

theorem linearIndependent_const_mul {c : Ω} (hc : c ≠ 0) {x : J → Ω} (hx : LinearIndependent ℤ x) :
    LinearIndependent ℤ (fun i => c * x i) :=
  hx.map' (LinearMap.mulLeft ℤ c) (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hc))

end Lattices

def pullMetric {J : Type} [Fintype J] (m : ConeMetric ℂ J) (A : Matrix J J ℚ)
    (hA : ∀ z, z ≠ 0 → matActC A z ≠ 0) : ConeMetric ℂ J where
  ρ z := m.ρ (matActC A z)
  pos z hz := m.pos _ (hA z hz)
  smul a z := by rw [matActC_smul, m.smul]

theorem proof (hN : ChangeOfLatticeNested.Statement) : ChangeOfLattice.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hB hm hm'
  classical
  obtain ⟨C, hCB, hBC⟩ := exists_inv_of_isInvMat hB
  obtain ⟨c, hc0, hcC⟩ := exists_clear_den C
  obtain ⟨d, hd0, hdB⟩ := exists_clear_den B
  have hc : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hc0
  have hcΩ : (c : Ω) ≠ 0 := Nat.cast_ne_zero.2 hc0
  set S : Matrix (Ix κ) (Ix κ) ℚ := (c : ℚ) • 1 with hS
  set T : Matrix (Ix κ) (Ix κ) ℚ := (c : ℚ)⁻¹ • 1 with hT
  have hTS : T * S = 1 := by rw [hS, hT, smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hc, one_smul]
  have hST : S * T = 1 := by rw [hS, hT, smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hc, one_smul]
  have hSint : ∀ i j, ∃ k : ℤ, S i j = k := fun i j => by
    by_cases h : i = j
    · exact ⟨c, by simp [hS, h]⟩
    · exact ⟨0, by simp [hS, h]⟩
  have hSCint : ∀ i j, ∃ k : ℤ, (S * C) i j = k := fun i j => by
    simpa [hS, Matrix.smul_mul, Matrix.smul_apply] using hcC i j

  set x₀ := matAct S x with hx₀def
  have hx₀ : x₀ = fun i => (c : Ω) * x i := by
    rw [hx₀def, hS, matAct_smul_one]
    simp
  have hTz : ∀ z, z ≠ 0 → matActC T z ≠ 0 := fun z hz => by
    rw [hT, matActC_smul_one]
    exact smul_ne_zero (by simp [hc0]) hz
  set m₀ := pullMetric m T hTz
  have hm₀ : IsSmoothMetric m₀ := hm.comp (contDiff_matActC T).contDiffOn fun z hz => hTz z hz
  have hX₀ : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x₀) (D + 1) := by rwa [hx₀, coordIdeal_const_mul hcΩ]
  have hx₀li : LinearIndependent ℤ x₀ := by
    rw [hx₀]
    exact linearIndependent_const_mul hcΩ hx
  have eT : matAct T x₀ = x := by rw [hx₀def, matAct_mul, hTS, ChangeOfLatticeNested.matAct_one]
  have eBT : matAct (B * T) x₀ = matAct B x := by rw [hx₀def, matAct_mul, mul_assoc, hTS, mul_one]
  have sp1 : Submodule.span ℤ (Set.range x₀) ≤ Submodule.span ℤ (Set.range x) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun i => matAct_mem_span hSint x i)
  have sp2 : Submodule.span ℤ (Set.range x₀) ≤ Submodule.span ℤ (Set.range (matAct B x)) := by
    have e : x₀ = matAct (S * C) (matAct B x) := by rw [matAct_mul, mul_assoc, hCB, mul_one]
    rw [e]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 fun i => matAct_mem_span hSCint _ i)

  have h1 := hN D Ω κ I x₀ T m₀ m hI hX₀ hx₀li (isInvMat_of_mul hTS hST) hm₀ (fun z => rfl)
    (by rw [eT]; exact sp1)
  have h2 := hN D Ω κ I x₀ (B * T) m₀ m' hI hX₀ hx₀li
    (isInvMat_of_mul (A' := S * C) (by rw [mul_assoc, ← mul_assoc T, hTS, one_mul, hBC])
      (by rw [mul_assoc, ← mul_assoc C, hCB, one_mul, hST]))
    hm₀ (fun z => (by rw [← matActC_mul, hm'] : m'.ρ (matActC (B * T) z) = m.ρ (matActC T z)))
    (by rw [eBT]; exact sp2)
  rw [eT] at h1
  rw [eBT] at h2

  have hcoc : ∀ n : ℕ,
      latLogIndex x (matAct B x) n = latLogIndex x₀ (matAct B x) n - latLogIndex x₀ x n := by
    intro n
    have hM1 := sec_mono sp1 n
    have hM2 := sec_mono sp2 n
    have f1 : (sec ℤ x₀ n).toAddSubgroup.relIndex (sec ℤ x n).toAddSubgroup ≠ 0 := by
      refine relIndex_sec_ne_zero (N := c) (by exact_mod_cast hc0) (fun i => ?_) n
      have e : (c : ℤ) • x i = x₀ i := by
        rw [hx₀, zsmul_eq_mul]
        push_cast
        rfl
      rw [e]
      exact Submodule.subset_span ⟨i, rfl⟩
    have f2 : (sec ℤ x₀ n).toAddSubgroup.relIndex (sec ℤ (matAct B x) n).toAddSubgroup ≠ 0 := by
      refine relIndex_sec_ne_zero (N := c * d) (mul_ne_zero (by exact_mod_cast hc0) (by exact_mod_cast hd0)) (fun i => ?_) n
      have e : ((c : ℤ) * d) • matAct B x i = matAct ((d : ℚ) • B) x₀ i := by
        rw [hx₀, zsmul_eq_mul]
        simp only [matAct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        push_cast
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      exact matAct_mem_span (fun i j => by simpa [Matrix.smul_apply] using hdB i j) x₀ i
    have one1 : (sec ℤ x n).toAddSubgroup.relIndex (sec ℤ x₀ n).toAddSubgroup = 1 :=
      AddSubgroup.relIndex_eq_one.2 fun _ h => hM1 h
    have one2 : (sec ℤ (matAct B x) n).toAddSubgroup.relIndex (sec ℤ x₀ n).toAddSubgroup = 1 :=
      AddSubgroup.relIndex_eq_one.2 fun _ h => hM2 h
    unfold latLogIndex
    rw [log_relIndex_cocycle (fun _ h => hM1 h) (fun _ h => hM2 h) f1 f2, one1, one2]
    simp
  refine (h2.sub h1).congr_left fun n => ?_
  rw [hcoc n]
  ring

end ChangeOfLattice

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
