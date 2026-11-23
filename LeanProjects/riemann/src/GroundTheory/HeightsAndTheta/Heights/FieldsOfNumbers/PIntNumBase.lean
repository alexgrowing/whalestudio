import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Point

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

def blockMonomial (i : ∀ k, ι k) (m : K → ℕ) : MRing ι F :=
  ∏ k, X ⟨k, i k⟩ ^ m k

omit [∀ k, Fintype (ι k)] in

theorem blockMonomial_isMultiHomog (i : ∀ k, ι k) (m : K → ℕ) :
    IsMultiHomog (blockMonomial (F := F) i m) m := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MRing ι F) ^ m k) (fun k => m k • blockWeight ι ⟨k, i k⟩)
    (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, i k⟩).pow (m k))
  have hm : (∑ k, m k • blockWeight ι ⟨k, i k⟩) = m := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hm] at h
  exact h

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem blockMonomial_add (i : ∀ k, ι k) (m n : K → ℕ) :
    blockMonomial (F := F) i (m + n) = blockMonomial i m * blockMonomial i n := by
  simp [blockMonomial, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem blockMonomial_mk_ne_zero (P : Ideal (MRing ι F)) [P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ P) (m : K → ℕ) :
    Ideal.Quotient.mk P (blockMonomial i m) ≠ 0 := by
  unfold blockMonomial
  rw [map_prod, Finset.prod_ne_zero_iff]
  intro k _
  rw [map_pow]
  refine pow_ne_zero _ ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact hi k

end Point

theorem IntNumBase.proof (h1 : MixedDiffConst.Statement.{u}) : IntNumBase.Statement.{u} := by
  intro F _ K _ _ ι _ P hP hrel
  have := hP.isPrime

  have hev : ∀ᶠ m in Filter.atTop, hilbFn P m = intNum F P (n := 0) ![] := by
    have h0 : relDim P = ((0 : ℕ) : WithBot (WithTop ℤ)) := by rw [hrel]; rfl
    filter_upwards [(h1 F K ι P hP.multiHomog hP.relevant 0 h0).1 ![]] with m hm
    simpa [mixedDiff] using hm
  set c := intNum F P (n := 0) ![] with hc
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp hev
  choose i hi using hP.relevant
  set A := MRing ι F ⧸ P
  set L := FractionRing A
  let xm : (K → ℕ) → L := fun m => algebraMap A L (Ideal.Quotient.mk P (blockMonomial i m))
  have hxm : ∀ m, xm m ≠ 0 := fun m => by
    simp only [xm, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
    exact blockMonomial_mk_ne_zero P i hi m
  have hxm_add : ∀ m n, xm (m + n) = xm m * xm n := fun m n => by
    simp only [xm, blockMonomial_add, map_mul]

  let φ : (K → ℕ) → A →ₗ[F] L := fun m =>
    (LinearMap.mulRight F (xm m)⁻¹).comp (IsScalarTower.toAlgHom F A L).toLinearMap
  have hφ : ∀ m a, φ m a = algebraMap A L a / xm m := fun m a => by
    simp [φ, div_eq_mul_inv]
  have hφinj : ∀ m, Function.Injective (φ m) := fun m a b hab => by
    rw [hφ, hφ, div_left_inj' (hxm m)] at hab
    exact IsFractionRing.injective A L hab
  let U : (K → ℕ) → Submodule F L := fun m => (gradedPiece P m).map (φ m)
  have memU : ∀ m y, y ∈ U m ↔ ∃ f : MRing ι F, IsMultiHomog f m ∧
      y = algebraMap A L (Ideal.Quotient.mk P f) / xm m := fun m y => by
    simp only [U, gradedPiece, Submodule.mem_map, hφ]
    constructor
    · rintro ⟨a, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf, rfl⟩, rfl⟩
  have hfinU : ∀ m, FiniteDimensional F (U m) := fun m => by
    have := ((GradedFinite.proof.{u}) F K ι P m).1
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (hφinj m) _)
  have hrankU : ∀ m, Module.finrank F (U m) = Module.finrank F (gradedPiece P m) := fun m =>
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (hφinj m) _)).symm
  have hmono : ∀ m n, m ≤ n → U m ≤ U n := fun m n hmn y hy => by
    obtain ⟨f, hf, rfl⟩ := (memU m y).mp hy
    refine (memU n _).mpr ⟨f * blockMonomial i (n - m), ?_, ?_⟩
    · have := hf.mul (blockMonomial_isMultiHomog (F := F) i (n - m))
      rwa [add_tsub_cancel_of_le hmn] at this
    · have hn : xm n = xm m * xm (n - m) := by rw [← hxm_add, add_tsub_cancel_of_le hmn]
      rw [hn, map_mul, map_mul]
      exact (mul_div_mul_right _ _ (hxm (n - m))).symm
  have hmul : ∀ m n y z, y ∈ U m → z ∈ U n → y * z ∈ U (m + n) := fun m n y z hy hz => by
    obtain ⟨f, hf, rfl⟩ := (memU m y).mp hy
    obtain ⟨g, hg, rfl⟩ := (memU n z).mp hz
    refine (memU _ _).mpr ⟨f * g, hf.mul hg, ?_⟩
    rw [hxm_add, map_mul, map_mul]
    exact div_mul_div_comm _ _ _ _

  let N : K → ℕ := fun k => (M0 k).toNat
  have hrankc : ∀ n, N ≤ n → (Module.finrank F (U n) : ℤ) = c := fun n hn => by
    rw [hrankU, ← ((GradedFinite.proof.{u}) F K ι P n).2]
    refine hM0 _ fun k => ?_
    exact (Int.self_le_toNat (M0 k)).trans (by exact_mod_cast hn k)
  have hstab : ∀ m, U m ≤ U N := fun m => by
    have hN : U N = U (m ⊔ N) := by
      have := hfinU (m ⊔ N)
      refine Submodule.eq_of_le_of_finrank_eq (hmono _ _ le_sup_right) ?_
      have h1 := hrankc N le_rfl
      have h2 := hrankc (m ⊔ N) le_sup_right
      exact_mod_cast h1.trans h2.symm
    rw [hN]
    exact hmono _ _ le_sup_left

  have hone : (1 : L) ∈ U N := by
    refine hstab 0 ((memU 0 1).mpr ⟨1, isWeightedHomogeneous_one F _, ?_⟩)
    have : xm 0 = 1 := by simp [xm, blockMonomial]
    rw [this, map_one, map_one, div_one]
  let S : Subalgebra F L := (U N).toSubalgebra hone fun y z hy hz => hstab _ (hmul _ _ _ _ hy hz)
  have : FiniteDimensional F S := hfinU N
  let E : IntermediateField F L := S.toIntermediateField fun y hy =>
    S.inv_mem_of_algebraic (x := ⟨y, hy⟩) ((IsIntegral.of_finite F (⟨y, hy⟩ : S)).map S.val).isAlgebraic
  have hEq : homFracDegZero P = E := by
    apply le_antisymm
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x ⟨b, f, g, hf, hg, hgP, rfl⟩
      have hfU : algebraMap A L (Ideal.Quotient.mk P f) / xm b ∈ E :=
        hstab b ((memU b _).mpr ⟨f, hf, rfl⟩)
      have hgU : algebraMap A L (Ideal.Quotient.mk P g) / xm b ∈ E :=
        hstab b ((memU b _).mpr ⟨g, hg, rfl⟩)
      have hg0 : algebraMap A L (Ideal.Quotient.mk P g) ≠ 0 := by
        rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
        exact hgP
      have heq : algebraMap A L (Ideal.Quotient.mk P f) / algebraMap A L (Ideal.Quotient.mk P g) =
          algebraMap A L (Ideal.Quotient.mk P f) / xm b *
            (algebraMap A L (Ideal.Quotient.mk P g) / xm b)⁻¹ := by
        rw [inv_div, div_mul_div_comm, mul_comm (xm b), mul_div_mul_right _ _ (hxm b)]
      rw [SetLike.mem_coe, heq]
      exact E.mul_mem hfU (E.inv_mem hgU)
    · intro y hy
      obtain ⟨f, hf, rfl⟩ := (memU N y).mp hy
      exact IntermediateField.subset_adjoin _ _
        ⟨N, f, blockMonomial i N, hf, blockMonomial_isMultiHomog i N,
          fun h => blockMonomial_mk_ne_zero P i hi N (Ideal.Quotient.eq_zero_iff_mem.mpr h), rfl⟩
  have hES : Subalgebra.toSubmodule E.toSubalgebra = U N := rfl
  let e : E ≃ₗ[F] U N := LinearEquiv.ofEq _ _ hES
  rw [hEq]
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [e.finrank_eq]
  exact (hrankc N le_rfl).symm

end

end GroundTheory.Heights₂.Heights.FieldNumbers
