import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.ESMulESOfNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.TraceFormulaOfRankDegree
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.KudlaSiegelWeil

noncomputable section

namespace PI.Dv.Tr

open PI.Dv Module

section Eps

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

open Classical in

def epsSum (P : Pair K G) : MonoidAlgebra K G :=
  ∑ h : P.H, (((P.chi h)⁻¹ : Kˣ) : K) • MonoidAlgebra.of K G (h : G)

open Classical in
lemma eps_eq (P : Pair K G) : eps P = ((Fintype.card P.H : ℕ) : K)⁻¹ • epsSum P := by
  rw [eps, epsSum, Nat.card_eq_fintype_card]
  congr 1
  symm
  refine Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _ ?_ ?_
  · intro x hx
    rw [dif_neg]
    intro hm
    exact hx ⟨⟨x, hm⟩, rfl⟩
  · intro h
    rw [dif_pos h.2]

lemma characteristic_polynomial_compatibility (P : Pair K G) (y h : P.H) :
    ((P.chi y : Kˣ) : K) * (((P.chi (y * h))⁻¹ : Kˣ) : K) = (((P.chi h)⁻¹ : Kˣ) : K) := by
  rw [map_mul, mul_inv, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]

open Classical in
lemma of_mul_epsSum (P : Pair K G) (y : P.H) :
    MonoidAlgebra.of K G (y : G) * epsSum P = ((P.chi y : Kˣ) : K) • epsSum P := by
  rw [epsSum, Finset.mul_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ (fun h => ?_)
  rw [mul_smul_comm, ← map_mul, smul_smul, Equiv.coe_mulLeft, Subgroup.coe_mul, characteristic_polynomial_compatibility]

open Classical in
lemma epsSum_sq (P : Pair K G) : epsSum P * epsSum P = ((Fintype.card P.H : ℕ) : K) • epsSum P := by
  conv_lhs => arg 1; rw [epsSum]
  rw [Finset.sum_mul]
  simp_rw [smul_mul_assoc, of_mul_epsSum, smul_smul, Units.inv_mul, one_smul]
  rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

open Classical in
lemma eps_idem (P : Pair K G) : eps P * eps P = eps P := by
  have hc : ((Fintype.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eps_eq, smul_mul_smul_comm, epsSum_sq, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]

end Eps

section Idem

lemma mul_idem {R : Type*} [Semiring R] {a b : R} (ha : a * a = a) (hb : b * b = b) (hc : b * a = a * b) :
    (a * b) * (a * b) = a * b := by
  rw [mul_assoc, ← mul_assoc b, hc, mul_assoc, hb, ← mul_assoc, ha]

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma finrank_range_idem (f : Module.End K V) (h : f * f = f) :
    ((finrank K (LinearMap.range f) : ℕ) : K) = LinearMap.trace K V f :=
  (((LinearMap.isProj_range_iff_isIdempotentElem f).mpr h).trace).symm

end Idem

section Alg

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

theorem rank_identity (T : GoodSet K G) (P0 P : Pair K G) (hM : M1 T P0)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V) :
    finrank K (LinearMap.range (ρ.asAlgebraHom (eps P * eG T))) =
      ∑ s, nS T P s * finrank K (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) := by
  choose c hc using fun s => trace_mul_eS T s ρ
  have hn : ∀ (Q : Pair K G) s, ((nS T Q s : ℕ) : K) = LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom (eps Q)) := by
    intro Q s
    rw [nS]
    exact finrank_range_idem _ (by rw [← map_mul, eps_idem])
  have hidS : ∀ (Q : Pair K G) s, (eps Q * eS T s) * (eps Q * eS T s) = eps Q * eS T s :=
    fun Q s => mul_idem (eps_idem Q) (eS_idem T s) (eS_comm T s (eps Q)).symm
  have hidG : (eps P * eG T) * (eps P * eG T) = eps P * eG T :=
    mul_idem (eps_idem P) (eG_idem T) (eG_comm T (eps P)).symm
  have hr : ∀ s, ((finrank K (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) : ℕ) : K) = c s := by
    intro s
    rw [finrank_range_idem _ (by rw [← map_mul, hidS]), hc, ← hn, hM s, Nat.cast_one, mul_one]
  apply Nat.cast_injective (R := K)
  rw [finrank_range_idem _ (by rw [← map_mul, hidG])]
  rw [eG, Finset.mul_sum, map_sum, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hc, hr, hn, mul_comm]

end Alg

section Lat

open NumberField

variable {K : Type} [Field K] [NumberField K]

lemma exists_den {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) {y : V} (hy : y ∈ Submodule.span K (L : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • y ∈ L :=
  _root_.UpperTheory.Reformulated.B.KudlaSiegelWeil.exists_den L hy

lemma span_cut {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (R : Submodule K V) :
    Submodule.span K ((L ⊓ R.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = R := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · intro y hy
    have hy' : y ∈ Submodule.span K (L : Set V) := by rw [hL]; exact Submodule.mem_top
    obtain ⟨d, hd, hm⟩ := exists_den L hy'
    have hdy : d • y ∈ R := by rw [← algebraMap_smul K d y]; exact R.smul_mem _ hy
    have hmem : d • y ∈ (L ⊓ R.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := Submodule.mem_inf.mpr ⟨hm, hdy⟩
    have hd' : algebraMap (𝓞 K) K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd
    have hyy : y = (algebraMap (𝓞 K) K d)⁻¹ • (d • y) := by
      rw [← algebraMap_smul K d y, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hyy]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

variable [StarRing K] {G : Type} [Group G] [Fintype G]

lemma rkL_cut (A : Formalism.BasicNotions.HLat K) (hA : A.Good) (ρ : Representation K G A.V) (a : MonoidAlgebra K G) :
    rkL A (cut A ρ a A.L) = finrank K (LinearMap.range (ρ.asAlgebraHom a)) := by
  unfold rkL Formalism.HN.rkK cut cutE
  rw [span_cut A.L hA.2.2]

end Lat

theorem rankPart : RankPart := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA
  have : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  rw [rkT, rkL_cut A hA.1, rank_identity T P0 P hM ρ]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rS, rkL_cut A hA.1]

end PI.Dv.Tr
