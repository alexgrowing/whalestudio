import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.CoreLatticeEqOfMemCoreStabilizer
import GroundTheory.AutomorphicForms.DefiniteClassNumber.Finiteness

set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain GroundTheory.Automorphic
  GroundTheory.Global

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [Field E] [NumberField E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)

section Pairing

variable (H : Matrix ι ι E)

def pairE (x y : ι → K ⊗[K] E) : E := Algebra.TensorProduct.lid K E (hermPair K H K x y)

variable {H}

theorem baseTrace_eq_trace_lid (z : K ⊗[K] E) :
    baseTrace K E K z = Algebra.trace K E (Algebra.TensorProduct.lid K E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    rw [baseTrace_tmul, Algebra.TensorProduct.lid_tmul, LinearMap.map_smul, smul_eq_mul,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem hermTrace_eq_trace_pairE (x y : ι → K ⊗[K] E) :
    hermTrace K H K x y = Algebra.trace K E (pairE H x y) :=
  baseTrace_eq_trace_lid _

theorem pairE_smul_right (β : E) (x y : ι → K ⊗[K] E) :
    pairE H x (((1 : K) ⊗ₜ[K] β) • y) = β * pairE H x y := by
  rw [pairE, hermPair_smul_right, map_mul, Algebra.TensorProduct.lid_tmul, one_smul]
  rfl

theorem pairE_smul_left (β : E) (x y : ι → K ⊗[K] E) :
    pairE H (((1 : K) ⊗ₜ[K] β) • x) y = conj K E β * pairE H x y := by
  rw [pairE, hermPair_smul_left, map_mul, conjBase_tmul, Algebra.TensorProduct.lid_tmul, one_smul]
  rfl

theorem smul_smul_comm_vec (z : K ⊗[K] E) (c : K) (y : ι → K ⊗[K] E) :
    z • (c • y) = c • (z • y) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul_comm]

end Pairing

section Nondegenerate

variable {H : Matrix ι ι E}

theorem isUnit_det_traceGram_of_isUnit (hH : IsUnit H.det) : IsUnit (traceGram H b).det := by
  classical
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨t, ht0, ht⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  set X : ι → K ⊗[K] E := vecOfCoords b K t with hXdef
  have hX : ∀ Y : ι → K ⊗[K] E, hermTrace K H K X Y = 0 := by
    intro Y
    rw [hermTrace_eq_sum_traceGram (H := H) (b := b) K, hXdef, vecCoords_vecOfCoords,
      Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    have hc := congrFun ht c
    simp only [vecMul, dotProduct, Pi.zero_apply] at hc
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    calc ∑ a, t a * vecCoords K b Y c * traceGram H b a c
        = vecCoords K b Y c * ∑ a, t a * traceGram H b a c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
      _ = 0 := by rw [hc, mul_zero]
  have hX0 : X ≠ 0 := by
    intro h
    apply ht0
    rw [← vecCoords_vecOfCoords b K t, ← hXdef, h]
    funext a
    simp [vecCoords]
  obtain ⟨i, hi⟩ : ∃ i, X i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hX0 (funext hc)
  have hci : conjBase K E K (X i) ≠ 0 := by
    intro h
    apply hi
    rw [← conjBase_conjBase (X i), h, map_zero]
  have hunit : IsUnit (conjBase K E K (X i)) := by
    have h1 : Algebra.TensorProduct.lid K E (conjBase K E K (X i)) ≠ 0 := by
      intro h
      exact hci ((Algebra.TensorProduct.lid K E).injective (by rw [h, map_zero]))
    have := (isUnit_iff_ne_zero.2 h1).map (Algebra.TensorProduct.lid K E).symm
    rwa [AlgEquiv.symm_apply_apply] at this
  obtain ⟨u, hu⟩ := hunit
  set Hb := baseMatrix K H K
  have hHb : IsUnit Hb.det := isUnit_det_baseMatrix H K hH
  set Y : ι → K ⊗[K] E := Hb⁻¹ *ᵥ Pi.single i (↑u⁻¹ : K ⊗[K] E)
  have hpair : hermPair K H K X Y = 1 := by
    unfold hermPair
    rw [show baseMatrix K H K = Hb from rfl, mulVec_mulVec, Matrix.mul_nonsing_inv _ hHb,
      one_mulVec, dotProduct_single, ← hu, Units.mul_inv]
  have h2 := hX Y
  rw [hermTrace, hpair, show (1 : K ⊗[K] E) = algebraMap K (K ⊗[K] E) 1 from (map_one _).symm,
    baseTrace_algebraMap, mul_one] at h2
  exact two_ne_zero h2

end Nondegenerate

section Integrality

variable (H : Matrix ι ι E)

theorem exists_int_isIntegral_pairE : ∃ d : ℤ, d ≠ 0 ∧
    ∀ (g : unitaryPoints K E H (FinAdele K)) (x y : ι → K ⊗[K] E), x ∈ coreLattice b H g →
      y ∈ coreLattice b H g → IsIntegral ℤ ((d : E) * pairE H x y) := by
  obtain ⟨d₁, hd₁0, hd₁⟩ := exists_int_isIntegral_hermTrace b H
  obtain ⟨D, hD0, hD⟩ := exists_int_isIntegral_of_trace (K := E)
  refine ⟨D * d₁, mul_ne_zero hD0 hd₁0, fun g x y hx hy => ?_⟩
  have key : ∀ s, ∃ n : ℤ, Algebra.trace ℚ E (((d₁ : E) * pairE H x y) * integralBasis E s) = n := by
    intro s
    have hy' := smul_mem_coreLattice b hy (RingOfIntegers.basis E s)
    have h1 := hd₁ g x _ (coreLattice_le_adelicLattice b g hx) (coreLattice_le_adelicLattice b g hy')
    rw [hermTrace_eq_trace_pairE, pairE_smul_right] at h1
    obtain ⟨n, hn⟩ := exists_int_trace_eq h1
    refine ⟨n, ?_⟩
    rw [← hn, ← Algebra.trace_trace (S := K), integralBasis_apply, ← RingOfIntegers.coe_eq_algebraMap]
    congr 1
    rw [show (d₁ : E) = algebraMap K E (d₁ : K) by rw [map_intCast], mul_assoc, ← Algebra.smul_def,
      LinearMap.map_smul, smul_eq_mul, mul_comm (pairE H x y)]
  have := hD _ key
  rw [show ((D * d₁ : ℤ) : E) * pairE H x y = (D : E) * ((d₁ : E) * pairE H x y) by push_cast; ring]
  exact this

theorem exists_int_smul_mem_coreLattice_of_dual {H : Matrix ι ι E} (hH : IsUnit H.det) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ (g : unitaryPoints K E H (FinAdele K)) (y : ι → K ⊗[K] E),
      (∀ x ∈ coreLattice b H g, IsIntegral ℤ (pairE H y x)) → (m : K) • y ∈ coreLattice b H g := by
  obtain ⟨N, hN0, hN⟩ := exists_int_smul_mem_coreLattice b H
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem_of_forall_isIntegral b H
    (isUnit_det_traceGram_of_isUnit b hH) (N : K) (by exact_mod_cast hN0)
  refine ⟨m, hm0, fun g y hy => ?_⟩
  rw [mem_coreLattice_iff]
  intro β
  have hyβ : ∀ x ∈ adelicLattice b H g,
      IsIntegral ℤ ((N : K) * hermTrace K H K (((1 : K) ⊗ₜ[K] (β : E)) • y) x) := by
    intro x hx
    rw [← hermTrace_smul_right, hermTrace_eq_trace_pairE, pairE_smul_left]
    refine Algebra.isIntegral_trace ((map_isIntegral_int (conj K E) β.2).mul (hy _ (hN g x hx)))
  have h2 := hm g _ hyβ
  rwa [← smul_smul_comm_vec] at h2

end Integrality

section Bounds

variable {H : Matrix ι ι E}

theorem isIntegral_vecCoords_of_mem_adelicLattice_one {x : ι → K ⊗[K] E}
    (hx : x ∈ adelicLattice b H 1) (a : ι × κ) : IsIntegral ℤ (vecCoords K b x a) := by
  rw [mem_adelicLattice, inv_one, show unitaryMat (1 : unitaryPoints K E H (FinAdele K)) = 1 from rfl,
    one_mulVec, mem_stdLattice_iff] at hx
  have := hx a
  rw [vecCoords_toFinAdele] at this
  exact isIntegral_of_algebraMap_mem this

theorem exists_int_isIntegral_coords (hH : IsUnit H.det) (g : unitaryPoints K E H (FinAdele K)) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ y ∈ adelicLattice b H g, ∀ a, IsIntegral ℤ ((m : K) * vecCoords K b y a) := by
  classical
  obtain ⟨r, hr0, hr⟩ := exists_int_smul_mem_adelicLattice (b := b) g
  obtain ⟨d₁, hd₁0, hd₁⟩ := exists_int_isIntegral_hermTrace b H
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem_of_forall_isIntegral b H
    (isUnit_det_traceGram_of_isUnit b hH) ((d₁ * r : ℤ) : K) (by exact_mod_cast mul_ne_zero hd₁0 hr0)
  refine ⟨m, hm0, fun y hy a => ?_⟩
  have h1 : ∀ x ∈ adelicLattice b H 1, IsIntegral ℤ (((d₁ * r : ℤ) : K) * hermTrace K H K y x) := by
    intro x hx
    have := hd₁ g y _ hy (hr x (isIntegral_vecCoords_of_mem_adelicLattice_one b hx))
    rw [hermTrace_smul_right] at this
    rw [show ((d₁ * r : ℤ) : K) * hermTrace K H K y x = (d₁ : K) * ((r : K) * hermTrace K H K y x) by
      push_cast; ring]
    exact this
  have := isIntegral_vecCoords_of_mem_adelicLattice_one b (hm 1 y h1) a
  rwa [vecCoords_smul] at this

theorem exists_int_smul_single_mem_coreLattice (g : unitaryPoints K E H (FinAdele K)) (i : ι) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : K) • (Pi.single i (1 : K ⊗[K] E) : ι → K ⊗[K] E) ∈ coreLattice b H g := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_int_mul_isIntegral (Finset.univ.image fun k => b.repr 1 k)
  obtain ⟨r, hr0, hr⟩ := exists_int_smul_mem_adelicLattice (b := b) g
  obtain ⟨N, hN0, hN⟩ := exists_int_smul_mem_coreLattice b H
  refine ⟨N * r * c, mul_ne_zero (mul_ne_zero hN0 hr0) hc0, ?_⟩
  have hX : ∀ a, IsIntegral ℤ (vecCoords K b ((c : K) • (Pi.single i (1 : K ⊗[K] E) : ι → K ⊗[K] E)) a) := by
    rintro ⟨j, k⟩
    rw [vecCoords_smul]
    simp only [vecCoords]
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, Algebra.TensorProduct.one_def, repr_one_tmul, Algebra.algebraMap_self,
        RingHom.id_apply]
      exact hc _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    · rw [Pi.single_eq_of_ne hj, map_zero, Finsupp.zero_apply, mul_zero]
      exact isIntegral_zero
  have := hN g _ (hr _ hX)
  rwa [smul_smul, smul_smul, ← Int.cast_mul, ← Int.cast_mul] at this

end Bounds

end GroundTheory.Heights₂.Heights.FiniteCovolume
