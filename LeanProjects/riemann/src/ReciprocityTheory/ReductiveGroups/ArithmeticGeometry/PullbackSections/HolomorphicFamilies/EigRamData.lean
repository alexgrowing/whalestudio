import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.IdemDataBasis

set_option autoImplicit false

noncomputable section

open NumberField

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam

variable {E : Type} [Field E] [NumberField E]

abbrev nI (E : Type) [Field E] [NumberField E] : ℕ := Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))

def omF (i : Fin (nI E)) : 𝓞 E :=
  RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)

def omDF (i : Fin (nI E)) : E :=
  TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)

def bD (δ : 𝓞 E) (hδ : ∀ i, IsIntegral ℤ ((δ : E) * omDF (E := E) i)) (i : Fin (nI E)) : 𝓞 E := ⟨_, hδ i⟩

def cD {k : Type} [Field k] (ψ : E →+* k) (δ : 𝓞 E) (i : Fin (nI E)) : k := ψ (omF i : E) / ψ (δ : E)

theorem omF_int_basis (i : Fin (nI E)) :
    integralBasis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i) = (omF i : E) := by
  rw [NumberField.integralBasis_apply]
  rfl

theorem sum_omDF_omF : ∑ i, omDF (E := E) i * (omF i : E) = 1 := by
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.sum_dual_mul (integralBasis E)
  rw [← Equiv.sum_comp (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm] at h
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
  rw [omF_int_basis]
  rfl

theorem ev_D {k : Type} [Field k] (ψ : E →+* k) (δ : 𝓞 E) (hδ : ∀ i, IsIntegral ℤ ((δ : E) * omDF (E := E) i))
    (hψδ : ψ (δ : E) ≠ 0) : evD (ψ.comp (algebraMap (𝓞 E) E)) (bD δ hδ) (cD ψ δ) = 1 := by
  unfold evD cD bD
  have e : ∀ i, ψ (omF (E := E) i : E) / ψ (δ : E) *
      (ψ.comp (algebraMap (𝓞 E) E)) ⟨(δ : E) * omDF i, hδ i⟩ = ψ (omDF i * omF i) := by
    intro i
    show ψ (omF (E := E) i : E) / ψ (δ : E) * ψ ((δ : E) * omDF i) = _
    rw [map_mul, map_mul]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => e i, ← map_sum, sum_omDF_omF, map_one]

theorem dual_mul_expand (a : 𝓞 E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (a : E) * TB.trDual (integralBasis E) i =
      ∑ j, (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E j) i : ℤ) : ℚ) • TB.trDual (integralBasis E) j := by
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dual_expand (integralBasis E) ((a : E) * TB.trDual (integralBasis E) i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hb : ∀ l, integralBasis E l = ((RingOfIntegers.basis E l : 𝓞 E) : E) :=
    fun l => NumberField.integralBasis_apply E l
  have e1 : (a : E) * TB.trDual (integralBasis E) i * integralBasis E j =
      TB.trDual (integralBasis E) i * ((a * RingOfIntegers.basis E j : 𝓞 E) : E) := by
    rw [hb]
    push_cast
    ring
  rw [e1, ← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E j)]
  push_cast
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_zsmul, ← hb,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.trace_dual_mul]
  simp

theorem eqv_D {k : Type} [Field k] (ψ : E →+* k) (δ : 𝓞 E) (hδ : ∀ i, IsIntegral ℤ ((δ : E) * omDF (E := E) i)) :
    IsEqv (ψ.comp (algebraMap (𝓞 E) E)) (bD δ hδ) (cD ψ δ) := by
  intro a
  refine ⟨fun i j => (RingOfIntegers.basis E).repr
      (a * RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
      ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i), fun i => ?_, fun j => ?_⟩
  · apply RingOfIntegers.ext
    have h1 := dual_mul_expand (E := E) a ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)
    rw [← Equiv.sum_comp (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm] at h1
    show algebraMap (𝓞 E) E (a * bD δ hδ i) = algebraMap (𝓞 E) E (∑ j, _ • bD δ hδ j)
    rw [map_mul, map_sum]
    show (a : E) * ((δ : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)) = _
    rw [show (a : E) * ((δ : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)) =
        (δ : E) * ((a : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)) by ring, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    show (δ : E) * (_ • TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j)) =
      _ • ((δ : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
    simp only [zsmul_eq_mul, Rat.smul_def, Rat.cast_intCast]
    ring
  · simp only [cD, RingHom.comp_apply]
    have h2 : ((a * RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j) :
        𝓞 E) : E) = ∑ i : Fin (nI E), (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E
          ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
          ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i) : ℤ) : E) * (omF i : E) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E
        ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))]
      rw [← Equiv.sum_comp (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm]
      push_cast
      simp [omF, zsmul_eq_mul]
    have h3 : ψ (a : E) * ψ (omF j : E) = ∑ i : Fin (nI E), (((RingOfIntegers.basis E).repr
        (a * RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
        ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i) : ℤ) : k) * ψ (omF i : E) := by
      rw [← map_mul, show (a : E) * (omF j : E) = ((a * RingOfIntegers.basis E
        ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j) : 𝓞 E) : E) by simp [omF], h2, map_sum]
      simp [map_mul, map_intCast]
    rw [mul_div_assoc', h3, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem trace_int (x : 𝓞 E) : ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ E (x : E) := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := E) (RingOfIntegers.isIntegral_coe x))
  exact ⟨z, by simpa using hz⟩

theorem one_eq_sum_trace : (1 : E) = ∑ i, Algebra.trace ℚ E (omF i : E) • omDF (E := E) i := by
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dual_expand (integralBasis E) (1 : E)
  rw [← Equiv.sum_comp (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm] at h
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [one_mul, omF_int_basis]
  rfl

theorem comp_D {k : Type} [Field k] [CharZero k] {Ty : Type} [Fintype Ty] (ψ : Ty → E →+* k)
    (htr : ∀ x : E, ∑ t, ψ t x = algebraMap ℚ k (Algebra.trace ℚ E x)) (N : ℕ) (hN : N ≠ 0)
    (hδ : ∀ i, IsIntegral ℤ (((N : 𝓞 E) : E) * omDF (E := E) i)) {d : ℕ} (M : 𝓞 E →+* Matrix (Fin d) (Fin d) k) :
    ∑ t, actD M (bD (N : 𝓞 E) hδ) (cD (ψ t) (N : 𝓞 E)) = 1 := by
  classical
  choose z hz using fun i : Fin (nI E) => trace_int (E := E) (omF i)
  have hN' : (N : k) ≠ 0 := Nat.cast_ne_zero.2 hN

  have hsum : ∑ i, (z i : 𝓞 E) * bD (N : 𝓞 E) hδ i = (N : 𝓞 E) := by
    apply RingOfIntegers.ext
    show algebraMap (𝓞 E) E (∑ i, (z i : 𝓞 E) * bD (N : 𝓞 E) hδ i) = algebraMap (𝓞 E) E (N : 𝓞 E)
    rw [map_sum, map_natCast]
    have h1 := one_eq_sum_trace (E := E)
    have e : ∀ i, algebraMap (𝓞 E) E ((z i : 𝓞 E) * bD (N : 𝓞 E) hδ i) =
        (N : E) * (Algebra.trace ℚ E (omF i : E) • omDF (E := E) i) := by
      intro i
      rw [map_mul, map_intCast, ← hz i, Rat.smul_def, Rat.cast_intCast]
      show (z i : E) * (((N : 𝓞 E) : E) * omDF (E := E) i) = _
      push_cast
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum, ← h1, mul_one]
  have hM : ∑ i, (z i : k) • M (bD (N : 𝓞 E) hδ i) = (N : k) • (1 : Matrix (Fin d) (Fin d) k) := by
    have := congrArg M hsum
    rw [map_sum, map_natCast] at this
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one, ← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  have htr : ∀ i, ∑ t, ψ t (omF i : E) = (z i : k) := by
    intro i
    rw [htr, ← hz i]
    simp
  unfold actD cD
  rw [Finset.sum_comm]
  calc ∑ i, ∑ t, (ψ t (omF i : E) / ψ t ((N : 𝓞 E) : E)) • M (bD (N : 𝓞 E) hδ i)
      = ∑ i, ((N : k)⁻¹ * (z i : k)) • M (bD (N : 𝓞 E) hδ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp only [map_natCast, div_eq_mul_inv]
        rw [← Finset.sum_mul, htr, mul_comm]
    _ = (N : k)⁻¹ • ∑ i, (z i : k) • M (bD (N : 𝓞 E) hδ i) := by
        rw [Finset.smul_sum]
        simp [mul_smul]
    _ = 1 := by rw [hM, smul_smul, inv_mul_cancel₀ hN', one_smul]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
