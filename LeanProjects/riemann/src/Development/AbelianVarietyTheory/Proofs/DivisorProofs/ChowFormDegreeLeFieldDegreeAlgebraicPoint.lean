import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt

namespace GlobalTheory.CompHt.PointUp

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N : ℕ}

open MvPolynomial in
private theorem aeval_det_linear_form_eq_det_map {K Ω ι : Type} [Field K] [Field Ω] [Algebra K Ω] {N d : ℕ}
    (e : Fin N → ι) (M : Fin N → Matrix (Fin d) (Fin d) K) (u : ι → Ω) :
    aeval u (Matrix.of fun l k => ∑ i, X (e i) * C (M i l k)).det =
      (Matrix.of fun l k => ∑ i, u (e i) * algebraMap K Ω (M i l k)).det := by
  rw [AlgHom.map_det]
  congr 1
  ext l k
  simp [RingHom.mapMatrix_apply, Matrix.map_apply]

open MvPolynomial in
private theorem det_linear_form_ne_zero_of_eq_one {K ι : Type} [Field K] {N d : ℕ}
    (e : Fin N → ι) (he : Function.Injective e) (M : Fin N → Matrix (Fin d) (Fin d) K) (j : Fin N)
    (hM : M j = 1) :
    (Matrix.of fun l k => ∑ i, (X (e i) * C (M i l k) : MvPolynomial ι K)).det ≠ 0 := by
  classical
  intro h0
  have h1 := aeval_det_linear_form_eq_det_map (Ω := K) e M (fun v : ι => if v = e j then (1 : K) else 0)
  rw [h0, map_zero] at h1
  have : (Matrix.of fun l k => ∑ i, (if e i = e j then (1 : K) else 0) * algebraMap K K (M i l k) :
      Matrix (Fin d) (Fin d) K) = 1 := by
    ext l k
    simp [he.eq_iff, hM, Matrix.one_apply]
  rw [this, Matrix.det_one] at h1
  exact zero_ne_one h1

open MvPolynomial in
private theorem isHomogeneous_det_linear_form {K ι : Type} [Field K] {N d : ℕ}
    (e : Fin N → ι) (M : Fin N → Matrix (Fin d) (Fin d) K) :
    (Matrix.of fun l k => ∑ i, (X (e i) * C (M i l k) : MvPolynomial ι K)).det.IsHomogeneous d := by
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have hentry : ∀ l k, (∑ i, (X (e i) * C (M i l k) : MvPolynomial ι K)).IsHomogeneous 1 :=
    fun l k => IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using (isHomogeneous_X K (e i)).mul (isHomogeneous_C _ (M i l k))
  have hprod := IsHomogeneous.prod Finset.univ
    (fun l => (Matrix.of fun l k => ∑ i, (X (e i) * C (M i l k) : MvPolynomial ι K)) (σ l) l)
    (fun _ => 1) fun l _ => hentry (σ l) l
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hprod
  rw [Units.smul_def]
  exact zsmul_mem (show _ ∈ homogeneousSubmodule ι K d from hprod) _

open MvPolynomial in
private theorem coord_ne_zero_of_vanishes_on_coneIdeal {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] {N : ℕ} (y z : Fin N → Ω) (j : Fin N) (hy : y j = 1) (hz0 : z ≠ 0)
    (hzI : ∀ g ∈ _root_.GlobalTheory.CompHt.coneIdeal K y, aeval z g = 0) : z j ≠ 0 := by
  intro hzj
  apply hz0
  funext i
  set m := minpoly K (y i)
  set r := m.natDegree
  have hmon : m.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral (y i))
  set h : MvPolynomial (Fin N) K :=
    ∑ k ∈ Finset.range (r + 1), C (m.coeff k) * X i ^ k * X j ^ (r - k) with hh
  have hhom : h.IsHomogeneous r := by
    refine IsHomogeneous.sum _ _ _ fun k hk => ?_
    have hkr : k + (r - k) = r := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    simpa [hkr] using ((isHomogeneous_C _ (m.coeff k)).mul (isHomogeneous_X_pow i k)).mul
      (isHomogeneous_X_pow j (r - k))
  have hyh : aeval y h = 0 := by
    have : aeval y h = Polynomial.aeval (y i) m := by
      rw [Polynomial.aeval_eq_sum_range]
      simp [hh, map_sum, hy, Algebra.smul_def]
      rfl
    rw [this, minpoly.aeval]
  have hzh := hzI h ((_root_.GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous y hhom).mpr hyh)
  rw [hh, map_sum, Finset.sum_eq_single r] at hzh
  · have h2 : z i = 0 ∧ ¬m.natDegree = 0 := by simpa [hzj, hmon.coeff_natDegree, r] using hzh
    exact h2.1
  · intro k hk hkr
    have : r - k ≠ 0 := by
      have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk); omega
    simp [hzj, zero_pow this]
  · intro hr; exact absurd (Finset.self_mem_range_succ r) hr

open MvPolynomial in
private theorem exists_algHom_adjoin_of_ker_le {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N : ℕ}
    (y w : Fin N → Ω) (hker : ∀ g : MvPolynomial (Fin N) K, aeval y g = 0 → aeval w g = 0) :
    ∃ ρ : Algebra.adjoin K (Set.range y) →ₐ[K] Ω,
      ∀ i, ρ ⟨y i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ = w i := by
  let φ : MvPolynomial (Fin N) K →ₐ[K] Algebra.adjoin K (Set.range y) :=
    (aeval y).codRestrict _ fun g => by
      rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨g, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨s, hs⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at hs
    obtain ⟨g, rfl⟩ := hs
    exact ⟨g, rfl⟩
  let e := Ideal.quotientKerAlgEquivOfSurjective hφ
  let lift := Ideal.Quotient.liftₐ (RingHom.ker φ) (aeval w) fun g hg => by
    apply hker
    have := congrArg Subtype.val (RingHom.mem_ker.mp hg)
    simpa [φ] using this
  refine ⟨lift.comp e.symm.toAlgHom, fun i => ?_⟩
  have hX : (⟨y i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ : Algebra.adjoin K (Set.range y)) =
      e (Ideal.Quotient.mk _ (X i)) := by
    apply Subtype.ext
    simp [e, φ]
  rw [hX]
  simp only [lift, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
    AlgEquiv.symm_apply_apply, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact aeval_X w i

open MvPolynomial in
private theorem aeval_smul_eq_pow_mul_of_isHomogeneous {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N n : ℕ}
    {φ : MvPolynomial (Fin N) K} (hφ : φ.IsHomogeneous n) (c : Ω) (x : Fin N → Ω) :
    aeval (c • x) φ = c ^ n * aeval x φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hφ (mem_support_iff.mp hm)
  simp only [aeval_monomial, Pi.smul_apply, smul_eq_mul, mul_pow, Finsupp.prod_mul]
  have : ∑ a, m a = n := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype] <;> simp
  rw [Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, this]; ring

open MvPolynomial in
private theorem aeval_inv_smul_eq_zero_of_mem_coneIdeal_zero {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N : ℕ}
    (y z : Fin N → Ω) (j : Fin N) (hy : y j = 1) (hz : z j ≠ 0)
    (hzI : ∀ g ∈ _root_.GlobalTheory.CompHt.coneIdeal K y, aeval z g = 0)
    (g : MvPolynomial (Fin N) K) (hg : aeval y g = 0) : aeval ((z j)⁻¹ • z) g = 0 := by
  set D := g.totalDegree
  set h : MvPolynomial (Fin N) K :=
    ∑ d ∈ Finset.range (D + 1), X j ^ (D - d) * homogeneousComponent d g with hh
  have hhom : h.IsHomogeneous D := by
    refine IsHomogeneous.sum _ _ _ fun d hd => ?_
    have hdD : D - d + d = D := Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd))
    simpa [hdD] using (isHomogeneous_X_pow j (D - d)).mul (homogeneousComponent_isHomogeneous d g)
  have hyh : aeval y h = 0 := by
    have : aeval y h = aeval y (∑ d ∈ Finset.range (D + 1), homogeneousComponent d g) := by
      simp [hh, map_sum, hy]
    rw [this, sum_homogeneousComponent, hg]
  have hzh : aeval z h = 0 :=
    hzI h ((_root_.GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous y hhom).mpr hyh)
  have hc : z j ^ D ≠ 0 := pow_ne_zero _ hz
  refine (mul_eq_zero.mp ?_).resolve_left hc
  rw [← sum_homogeneousComponent g, map_sum, Finset.mul_sum]
  rw [hh, map_sum] at hzh
  rw [← hzh]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdD : d ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  rw [aeval_smul_eq_pow_mul_of_isHomogeneous (homogeneousComponent_isHomogeneous d g), map_mul, map_pow,
    aeval_X, inv_pow, ← mul_assoc]
  congr 1
  rw [← Nat.sub_add_cancel hdD, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hz), mul_one,
    Nat.add_sub_cancel]

open MvPolynomial in
private theorem det_multiplication_form_eq_zero_of_sum_eq_zero {K L A : Type} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] {d N : ℕ} (b : Module.Basis (Fin d) K A) (Y : Fin N → A)
    (ρ : A →ₐ[K] L) (u : Fin N → L) (hu : ∑ i, u i * ρ (Y i) = 0) :
    (Matrix.of fun l k => ∑ i, u i *
      algebraMap K L (LinearMap.toMatrix b b (Algebra.lmul K A (Y i)) l k)).det = 0 := by
  classical
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨fun k => ρ (b k), ?_, ?_⟩
  · intro h0
    have h1 : ρ 1 = 0 := by
      rw [← b.sum_repr 1, map_sum]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [map_smul, show ρ (b l) = 0 from congrFun h0 l, smul_zero]
    exact one_ne_zero (h1 ▸ (map_one ρ).symm)
  · funext k
    have hcol : ∀ i, ∑ l, algebraMap K L (LinearMap.toMatrix b b (Algebra.lmul K A (Y i)) l k) *
        ρ (b l) = ρ (Y i) * ρ (b k) := by
      intro i
      rw [← map_mul, ← b.sum_repr (Y i * b k), map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, Algebra.smul_def, LinearMap.toMatrix_apply]
      rfl
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ i, ∑ l, ρ (b l) * (u i *
          algebraMap K L (LinearMap.toMatrix b b (Algebra.lmul K A (Y i)) l k))
        = ∑ i, u i * ∑ l, algebraMap K L (LinearMap.toMatrix b b (Algebra.lmul K A (Y i)) l k) *
          ρ (b l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
      _ = (∑ i, u i * ρ (Y i)) * ρ (b k) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcol]; ring
      _ = 0 := by rw [hu, zero_mul]

set_option autoImplicit false in
open MvPolynomial in
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N : ℕ} in

theorem _root_.GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt : ∀ (K : Type) [Field K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K)
    (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → _root_.GlobalTheory.ChowHt.IsChowFormInt (_root_.GlobalTheory.CompHt.coneIdeal K y) 0 δ f →
    δ ≤ Module.finrank K (IntermediateField.adjoin K (Set.range y)) := by
  intro K _ N δ y j f hyj hf
  classical
  obtain ⟨hhomog, -, hzero⟩ := id hf
  have hSeq : (IntermediateField.adjoin K (Set.range y)).toSubalgebra =
      Algebra.adjoin K (Set.range y) := IntermediateField.adjoin_toSubalgebra _
  haveI hfinE : FiniteDimensional K (IntermediateField.adjoin K (Set.range y)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hfin : Module.finrank K (IntermediateField.adjoin K (Set.range y)) =
      Module.finrank K (Algebra.adjoin K (Set.range y)) := by
    rw [← hSeq]; rfl
  haveI : FiniteDimensional K (Algebra.adjoin K (Set.range y)) :=
    Module.finite_of_finrank_pos (hfin ▸ Module.finrank_pos)
  rw [hfin]
  set d := Module.finrank K (Algebra.adjoin K (Set.range y))
  let b := Module.finBasis K (Algebra.adjoin K (Set.range y))
  let Y : Fin N → Algebra.adjoin K (Set.range y) :=
    fun i => ⟨y i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  let M : Fin N → Matrix (Fin d) (Fin d) K :=
    fun i => LinearMap.toMatrix b b (Algebra.lmul K _ (Y i))
  let e : Fin N → Fin (0 + 1) × Fin N := fun i => (0, i)
  have he : Function.Injective e := fun a a' h => (Prod.ext_iff.mp h).2
  set p := (Matrix.of fun l k => ∑ i, (X (e i) * C (M i l k) : MvPolynomial (Fin (0 + 1) × Fin N) K)).det
    with hp
  have hMj : M j = 1 := by
    have : Y j = 1 := Subtype.ext hyj
    simp only [M, this, map_one]
    exact LinearMap.toMatrix_one b
  have hp0 : p ≠ 0 := det_linear_form_ne_zero_of_eq_one e he M j hMj
  have hphom : p.IsHomogeneous d := isHomogeneous_det_linear_form e M
  have key : ∀ u : Fin (0 + 1) × Fin N → AlgebraicClosure K, aeval u f = 0 → aeval u p = 0 := by
    intro u hu
    obtain ⟨z, hz0, hzI, hzu⟩ := (hzero u).mp hu
    have hzj := coord_ne_zero_of_vanishes_on_coneIdeal y z j hyj hz0 hzI
    obtain ⟨ρ, hρ⟩ := exists_algHom_adjoin_of_ker_le (K := K) y ((z j)⁻¹ • z)
      (aeval_inv_smul_eq_zero_of_mem_coneIdeal_zero y z j hyj hzj hzI)
    rw [hp, aeval_det_linear_form_eq_det_map]
    refine det_multiplication_form_eq_zero_of_sum_eq_zero b Y ρ (fun i => u (e i)) ?_
    have h0 := hzu 0
    calc ∑ i, u (e i) * ρ (Y i) = (z j)⁻¹ * ∑ i, u (0, i) * z i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hρ i]; simp only [e, Pi.smul_apply, smul_eq_mul]; ring
      _ = 0 := by rw [h0, mul_zero]
  obtain ⟨q, hq⟩ := hf.dvd_of_forall_aeval_eq_zero key
  have hf0 := hf.ne_zero
  have hq0 : q ≠ 0 := by
    rintro rfl; rw [mul_zero] at hq; exact hp0 hq
  have hfdeg : f.totalDegree = δ := by
    have := (_root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.mp hhomog).isHomogeneous
    simpa using this.totalDegree hf0
  have hdeg := totalDegree_mul_of_isDomain hf0 hq0
  rw [← hq, hphom.totalDegree hp0, hfdeg] at hdeg
  omega

end GlobalTheory.CompHt.PointUp
