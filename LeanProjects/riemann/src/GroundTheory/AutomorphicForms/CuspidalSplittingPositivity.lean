import Mathlib
import GroundTheory.AutomorphicForms.CuspidalSplittingCoeff
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Topology ComplexConjugate
open scoped Pointwise

theorem quotSum_eq_zero_of_nonneg {G : Type*} [Group G] {H : Subgroup G} {Φ : G → ℝ}
    (hΦ : ∀ g, 0 ≤ Φ g) (hfin : HasFiniteSupport fun q : G ⧸ H => Φ q.out)
    (h0 : quotSum H Φ = 0) (q : G ⧸ H) : Φ q.out = 0 := by
  classical
  have hfin' : (support fun q : G ⧸ H => Φ q.out).Finite := hfin
  rw [quotSum_def, finsum_eq_sum_of_support_subset _ hfin'.coe_toFinset.symm.subset] at h0
  by_cases hq : q ∈ hfin'.toFinset
  · exact (Finset.sum_eq_zero_iff_of_nonneg fun q _ => hΦ q.out).1 h0 q hq
  · simpa using hq

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section ScalarDet

def scalarDet : GL (Fin n) F →* GL (Fin n) F :=
  (Matrix.GeneralLinearGroup.scalar (Fin n)).comp Matrix.GeneralLinearGroup.det

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coe_scalarDet (g : GL (Fin n) F) :
    ((scalarDet g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.scalar (Fin n) (g : Matrix (Fin n) (Fin n) F).det := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem scalarDet_mem_center (g : GL (Fin n) F) :
    scalarDet g ∈ Subgroup.center (GL (Fin n) F) :=
  Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 ⟨_, (coe_scalarDet g).symm⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem scalarDet_of_mem_center {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    scalarDet z = z ^ n := by
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  have hdet : (z : Matrix (Fin n) (Fin n) F).det = a ^ n := by
    rw [← ha, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  ext1
  rw [coe_scalarDet, Units.val_pow_eq_pow_val, hdet, ← ha, map_pow]

theorem continuous_scalarDet : Continuous (scalarDet : GL (Fin n) F → GL (Fin n) F) := by
  have hval : Continuous fun g : GL (Fin n) F =>
      ((scalarDet g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    simp only [coe_scalarDet, Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.matrix_det)
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  exact (hval.comp continuous_inv).congr fun g => by simp only [Function.comp_apply, map_inv]

end ScalarDet

section NormChar

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}

def normChar (ω : GL (Fin n) F → ℂ) (g : GL (Fin n) F) : ℝ :=
  ‖ω (scalarDet g)‖ ^ ((n : ℝ)⁻¹)

variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem HasCentralChar.ne_zero {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    ω z ≠ 0 := fun h0 => by
  have := hωπ.inv_mul hv hz
  rw [h0, mul_zero] at this
  exact zero_ne_one this

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_pos (g : GL (Fin n) F) : 0 < normChar ω g :=
  Real.rpow_pos_of_pos (norm_pos_iff.2 (hωπ.ne_zero hv (scalarDet_mem_center g))) _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_mul (x y : GL (Fin n) F) :
    normChar ω (x * y) = normChar ω x * normChar ω y := by
  unfold normChar
  rw [map_mul, hωπ.mul hv (scalarDet_mem_center x) (scalarDet_mem_center y), norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_one : normChar ω (1 : GL (Fin n) F) = 1 := by
  unfold normChar
  rw [map_one, hωπ.one hv, norm_one, Real.one_rpow]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_inv_mul (g : GL (Fin n) F) : normChar ω g⁻¹ * normChar ω g = 1 := by
  rw [← normChar_mul hωπ hv, inv_mul_cancel, normChar_one hωπ hv]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem map_pow_of_mem_center {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F))
    (m : ℕ) : ω (z ^ m) = ω z ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, hωπ.one hv]
  | succ m ih => rw [pow_succ, hωπ.mul hv (pow_mem hz m) hz, ih, pow_succ]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem normChar_of_mem_center {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    normChar ω z = ‖ω z‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : z = 1 := Units.ext (Subsingleton.elim _ _)
    rw [h1, normChar_one hωπ hv, hωπ.one hv, norm_one]
  · unfold normChar
    rw [scalarDet_of_mem_center hz, map_pow_of_mem_center hωπ hv hz, norm_pow,
      Real.pow_rpow_inv_natCast (norm_nonneg _) hn.ne']

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem normChar_eq_one {k : GL (Fin n) F} (hk : π (scalarDet k) v = v) : normChar ω k = 1 := by
  have h1 : ω (scalarDet k) • v = (1 : ℂ) • v := by
    rw [one_smul, ← hωπ _ (scalarDet_mem_center k), hk]
  unfold normChar
  rw [smul_left_injective ℂ hv h1, norm_one, Real.one_rpow]

end NormChar

section Twisted

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ} {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V}

variable (π ω) in

def twVec (x : V) (g : GL (Fin n) F) : V :=
  ((normChar ω g : ℂ)⁻¹) • π g x

variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_mul_center (x : V) (g : GL (Fin n) F) {z : GL (Fin n) F}
    (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    twVec π ω x (g * z) = (ω z / (‖ω z‖ : ℂ)) • twVec π ω x g := by
  unfold twVec
  have hnz : (‖ω z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.2 (hωπ.ne_zero hv hz)).ne'
  have hθ : (normChar ω g : ℂ) ≠ 0 := by exact_mod_cast (normChar_pos hωπ hv g).ne'
  rw [map_mul, Module.End.mul_apply, hωπ z hz, map_smul, smul_smul, smul_smul,
    normChar_mul hωπ hv, normChar_of_mem_center hωπ hv hz]
  congr 1
  push_cast
  field_simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_mul_of_mem {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1) (g : GL (Fin n) F) {k : GL (Fin n) F} (hk : k ∈ K) :
    twVec π ω x (g * k) = twVec π ω x g := by
  unfold twVec
  rw [map_mul, Module.End.mul_apply, hx k hk, normChar_mul hωπ hv, hK k hk, mul_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_mul (x : V) (a g : GL (Fin n) F) :
    twVec π ω x (a * g) = ((normChar ω a : ℂ)⁻¹) • π a (twVec π ω x g) := by
  unfold twVec
  rw [map_smul, smul_smul, map_mul, Module.End.mul_apply, normChar_mul hωπ hv]
  push_cast
  rw [mul_inv, mul_comm]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_one (x : V) : twVec π ω x 1 = x := by
  unfold twVec
  rw [normChar_one hωπ hv, map_one, Module.End.one_apply]
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem conj_mul_self_unit {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    conj (ω z / (‖ω z‖ : ℂ)) * (ω z / (‖ω z‖ : ℂ)) = 1 := by
  have h1 : ‖ω z / (‖ω z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.2 (hωπ.ne_zero hv hz))]
  rw [Complex.conj_mul', h1]
  norm_num

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem norm_twVec_unit {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    ‖ω z / (‖ω z‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.2 (hωπ.ne_zero hv hz))]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem normSq_twVec_rightInv {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1) :
    ∀ g, ∀ h ∈ centerSup K, ‖f (twVec π ω x (g * h))‖ ^ 2 = ‖f (twVec π ω x g)‖ ^ 2 := by
  refine rightInv_centerSup (Φ := fun g => ‖f (twVec π ω x g)‖ ^ 2) (fun g z hz => ?_)
    (fun g k hk => ?_)
  ·     rw [twVec_mul_center hωπ hv x g hz, map_smul, smul_eq_mul, norm_mul,
      norm_twVec_unit hωπ hv hz, one_mul]
  ·     rw [twVec_mul_of_mem hωπ hv hx hK g hk]

end Twisted

section Nonvanishing

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}

theorem quotSum_ofReal {G : Type*} [Group G] {H : Subgroup G} {Φ : G → ℝ}
    (hfin : HasFiniteSupport fun q : G ⧸ H => Φ q.out) :
    quotSum H (fun g => (Φ g : ℂ)) = ((quotSum H Φ : ℝ) : ℂ) := by
  rw [quotSum_def, quotSum_def]
  exact (map_finsum Complex.ofRealHom hfin).symm

variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) {v : V}
  (hv : v ≠ 0) {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F)))
  {f : Module.Dual ℂ V} (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x)

include hπ hsc hωπ hv hKo hf

omit hωπ hv in
theorem finite_support_normSq_twVec (x : V) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => ‖f (twVec π ω x q.out)‖ ^ 2 :=
  finite_support_centerSup (Φ := fun g => ‖f (twVec π ω x g)‖ ^ 2) hKo
    (isCompactModCenter_matrixCoeff hπ hsc x (mem_smoothVectors_dual_of_inv hKo hf))
    fun g h0 => by
      change f (π g x) = 0 at h0
      simp [twVec, h0]

theorem apply_eq_zero_of_quotSum_normSq {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1)
    (h0 : quotSum (centerSup K) (fun g => ‖f (twVec π ω x g)‖ ^ 2) = 0) : f x = 0 := by
  have h1 := quotSum_eq_zero_of_nonneg (fun g => by positivity)
    (finite_support_normSq_twVec hπ hsc hKo hf x) h0 (QuotientGroup.mk 1)
  rw [apply_out_mk (Φ := fun g => ‖f (twVec π ω x g)‖ ^ 2)
    (normSq_twVec_rightInv hωπ hv hx hK), twVec_one hωπ hv] at h1
  simpa using h1

end Nonvanishing

theorem exists_coeffSum_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} {ω : GL (Fin n) F → ℂ} [π.IsIrreducible]
    (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) :
    ∃ K : Subgroup (GL (Fin n) F), IsCompact (K : Set (GL (Fin n) F)) ∧
      IsOpen (K : Set (GL (Fin n) F)) ∧ ∃ f : Module.Dual ℂ V, (∀ k ∈ K, ∀ x, f (π k x) = f x) ∧
        ∃ v ∈ fixedVectors π K, ∃ w, coeffSum π π K f v w ≠ 0 := by
  classical
  obtain ⟨v, hv0⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have h1 : (stabilizerOf π v : Set (GL (Fin n) F)) ∈ 𝓝 (1 : GL (Fin n) F) :=
    (hπ v).mem_nhds (one_mem _)
  have hU : (stabilizerOf π v : Set (GL (Fin n) F)) ∩
      scalarDet ⁻¹' (stabilizerOf π v : Set (GL (Fin n) F)) ∈ 𝓝 (1 : GL (Fin n) F) :=
    Filter.inter_mem h1 (continuous_scalarDet.continuousAt.preimage_mem_nhds (by rwa [map_one]))
  obtain ⟨K', hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  let K : Subgroup (GL (Fin n) F) := K'
  have hKo : IsOpen (K : Set (GL (Fin n) F)) := K'.isOpen
  have hKc' : IsCompact (K : Set (GL (Fin n) F)) := hKc
  have hvK : v ∈ fixedVectors π K := fun k hk => (hKU hk).1
  have hθK : ∀ k ∈ K, normChar ω k = 1 := fun k hk => normChar_eq_one hωπ hv0 (hKU hk).2
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Module.Dual ℂ V, f₀ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  let f : Module.Dual ℂ V := f₀ ∘ₗ (fixedVectors π K).subtype ∘ₗ fixedProj π hπ hKc' hKo
  have hf : ∀ k ∈ K, ∀ x, f (π k x) = f x := fun k hk x => by
    simp only [f, LinearMap.comp_apply, fixedProj_apply_act hπ hKc' hKo hk]
  have hfv : f v = f₀ v := by
    simp only [f, LinearMap.comp_apply, fixedProj_apply_of_mem hπ hKc' hKo hvK,
      Submodule.subtype_apply]
  have hfs := mem_smoothVectors_dual_of_inv hKo hf

  let P : GL (Fin n) F → V := twVec π ω v
  let S : GL (Fin n) F → V := fun g => conj (f (P g)) • P g
  have hSfin : HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => S q.out :=
    finite_support_centerSup (Φ := S) hKo (isCompactModCenter_matrixCoeff hπ hsc v hfs)
      fun g h0 => by
        change f (π g v) = 0 at h0
        simp [S, P, twVec, h0]
  have hSinv : ∀ g, ∀ h ∈ centerSup K, S (g * h) = S g := by
    refine rightInv_centerSup (Φ := S) (fun g z hz => ?_) (fun g k hk => ?_)
    · simp only [S, P]
      rw [twVec_mul_center hωπ hv0 v g hz, map_smul, smul_eq_mul, map_mul, smul_smul]
      congr 1
      linear_combination conj (f (twVec π ω v g)) * conj_mul_self_unit hωπ hv0 hz
    · simp only [S, P]
      rw [twVec_mul_of_mem hωπ hv0 hvK hθK g hk]
  have hPk : ∀ k ∈ K, ∀ g, P (k * g) = π k (P g) := fun k hk g => by
    simp only [P]
    rw [twVec_mul hωπ hv0 v k g, hθK k hk, Complex.ofReal_one, inv_one, one_smul]
  let v' : V := quotSum (centerSup K) S
  have hv'K : v' ∈ fixedVectors π K := by
    intro k hk
    have hSk : ∀ g, π k (S g) = S (k * g) := fun g => by
      simp only [S]
      rw [hPk k hk, hf k hk, map_smul]
    calc π k v' = quotSum (centerSup K) fun g => π k (S g) :=
          linearMap_finsum (π k) hSfin
      _ = quotSum (centerSup K) fun g => S (k * g) := quotSum_congr hSk
      _ = v' := quotSum_mul_left hSinv k

  have hΨinv : ∀ a, ∀ g, ∀ h ∈ centerSup K,
      conj (f (P (g * h))) * f (P (a * (g * h))) = conj (f (P g)) * f (P (a * g)) := by
    intro a
    refine rightInv_centerSup (Φ := fun g => conj (f (P g)) * f (P (a * g)))
      (fun g z hz => ?_) (fun g k hk => ?_)
    · simp only [P]
      rw [← mul_assoc, twVec_mul_center hωπ hv0 v g hz, twVec_mul_center hωπ hv0 v (a * g) hz,
        f.map_smul, f.map_smul, smul_eq_mul, smul_eq_mul, map_mul]
      linear_combination conj (f (twVec π ω v g)) * f (twVec π ω v (a * g)) *
        conj_mul_self_unit hωπ hv0 hz
    · simp only [P]
      rw [← mul_assoc, twVec_mul_of_mem hωπ hv0 hvK hθK g hk,
        twVec_mul_of_mem hωπ hv0 hvK hθK (a * g) hk]
  have hΨfin : ∀ a, HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K =>
      conj (f (P q.out)) * f (P (a * q.out)) := fun a =>
    finite_support_centerSup (Φ := fun g => conj (f (P g)) * f (P (a * g))) hKo
      (isCompactModCenter_matrixCoeff hπ hsc v hfs) fun g h0 => by
        change f (π g v) = 0 at h0
        simp [P, twVec, h0]

  let k' : GL (Fin n) F → ℂ := fun x => f (twVec π ω v' x)
  have hk'eq : ∀ x, k' x = quotSum (centerSup K) fun g => conj (f (P g)) * f (P (x * g)) := by
    intro x
    let L : V →ₗ[ℂ] ℂ := ((normChar ω x : ℂ)⁻¹) • (f ∘ₗ π x)
    have hL : ∀ y, L y = f (((normChar ω x : ℂ)⁻¹) • π x y) := fun y => by
      simp [L]
    calc k' x = L v' := (hL v').symm
      _ = quotSum (centerSup K) fun g => L (S g) := linearMap_finsum L hSfin
      _ = _ := quotSum_congr fun g => by
          simp only [hL, S, P]
          rw [twVec_mul hωπ hv0 v x g]
          simp only [map_smul, smul_eq_mul]
          ring
  have hk'conj : ∀ x, conj (k' x⁻¹) = k' x := by
    intro x
    rw [hk'eq, hk'eq, ← quotSum_mul_left (Φ := fun g => conj (f (P g)) * f (P (x * g)))
      (hΨinv x) x⁻¹, quotSum_def, quotSum_def,
      map_finsum (starRingEnd ℂ) (hΨfin x⁻¹)]
    refine finsum_congr fun q => ?_
    simp only [map_mul, Complex.conj_conj, mul_inv_cancel_left]
    ring
  have hfk : ∀ g, f (π g v') = (normChar ω g : ℂ) * k' g := fun g => by
    have hθ : (normChar ω g : ℂ) ≠ 0 := by exact_mod_cast (normChar_pos hωπ hv0 g).ne'
    simp only [k', twVec, map_smul, smul_eq_mul]
    field_simp
  refine ⟨K, hKc', hKo, f, hf, v', hv'K, v', fun hzero => hf₀ ?_⟩

  have hsum : quotSum (centerSup K) (fun g => f (π g⁻¹ v') * f (π g v')) = 0 := by
    have h2 := congrArg f hzero
    rw [map_zero] at h2
    unfold coeffSum at h2
    rw [quotSum_def, linearMap_finsum f (finite_support_coeffSum hπ hsc hKo hf v')] at h2
    rw [quotSum_def]
    simpa only [map_smul, smul_eq_mul] using h2
  have hterm : ∀ g, f (π g⁻¹ v') * f (π g v') = ((‖k' g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [hfk, hfk, ← hk'conj g⁻¹, inv_inv]
    have h2 : (normChar ω g⁻¹ : ℂ) * (normChar ω g : ℂ) = 1 := by
      exact_mod_cast normChar_inv_mul hωπ hv0 g
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
    linear_combination (conj (k' g) * k' g) * h2
  have hk'0 : f v' = 0 := by
    refine apply_eq_zero_of_quotSum_normSq hπ hsc hωπ hv0 hKo hf hv'K hθK ?_
    rw [quotSum_congr hterm, quotSum_ofReal (finite_support_normSq_twVec (ω := ω) hπ hsc hKo hf v')]
      at hsum
    exact_mod_cast hsum

  have hk'1 : f v' = ((quotSum (centerSup K) fun g => ‖f (twVec π ω v g)‖ ^ 2 : ℝ) : ℂ) := by
    have h2 := hk'eq 1
    simp only [k', twVec_one hωπ hv0, one_mul] at h2
    rw [h2, ← quotSum_ofReal (finite_support_normSq_twVec (ω := ω) hπ hsc hKo hf v)]
    refine quotSum_congr fun g => ?_
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rw [← hfv]
  refine apply_eq_zero_of_quotSum_normSq hπ hsc hωπ hv0 hKo hf hvK hθK ?_
  rw [hk'1] at hk'0
  exact_mod_cast hk'0

end Parabolic

end GroundTheory.Automorphic
