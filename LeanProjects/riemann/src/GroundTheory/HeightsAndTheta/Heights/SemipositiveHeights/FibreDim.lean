import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.PEvalKerKrullDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreMultiHomog
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FibreTranscendenceDegree

theorem isAlgebraic_of_forall_div {M : Type} [Field M] (B : Subalgebra ℤ M)
    (h : ∀ m : M, ∃ a b : M, a ∈ B ∧ b ∈ B ∧ b ≠ 0 ∧ m = a / b) : Algebra.IsAlgebraic B M := by
  refine ⟨fun m => ?_⟩
  obtain ⟨a, b, ha, hb, hb0, rfl⟩ := h m
  refine ⟨Polynomial.C (⟨b, hb⟩ : B) * Polynomial.X - Polynomial.C (⟨a, ha⟩ : B), fun h0 => hb0 ?_, ?_⟩
  · have h1 := congrArg (fun p : Polynomial B => p.coeff 1) h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, if_neg one_ne_zero,
      sub_zero, Polynomial.coeff_zero] at h1
    exact congrArg Subtype.val h1
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    show b * (a / b) - a = 0
    rw [mul_div_cancel₀ _ hb0, sub_self]

theorem trdeg_eq_of_forall_div {M : Type} [Field M] (B : Subalgebra ℤ M)
    (hZ : Function.Injective (algebraMap ℤ M))
    (h : ∀ m : M, ∃ a b : M, a ∈ B ∧ b ∈ B ∧ b ≠ 0 ∧ m = a / b) :
    Algebra.trdeg ℤ M = Algebra.trdeg ℤ B := by
  have := isAlgebraic_of_forall_div B h
  have : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective ℤ B).mpr fun a b hab =>
    hZ (by simpa using congrArg Subtype.val hab)
  have : FaithfulSMul B M := (faithfulSMul_iff_algebraMap_injective B M).mpr Subtype.val_injective
  have h0 := trdeg_add_eq ℤ B (A := M)
  rw [trdeg_eq_zero (R := B) (A := M), add_zero] at h0
  exact h0.symm

theorem trdeg_quot_ker {σ : Type} {M : Type} [CommRing M] [IsDomain M] (y : σ → M) :
    Algebra.trdeg ℤ (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M)) =
      Algebra.trdeg ℤ (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M).range := by
  have hker : RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M) =
      RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M).rangeRestrict := by
    ext p
    simp [RingHom.mem_ker, Subtype.ext_iff]
  exact ((Ideal.quotientEquivAlgOfEq ℤ hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective _))).trdeg_eq

theorem trdeg_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Ideal (MRing ι)}
    {n : ℕ} (h : IsArithVar J n) :
    ∃ t : ℕ, Algebra.trdeg ℤ (MRing ι ⧸ J) = t ∧ t + 1 = n + Fintype.card K := by
  obtain ⟨-, ⟨hprime, -, -⟩, hhor, hdim⟩ := h
  have := hprime
  have hA := IntDomainDim.proof (MRing ι ⧸ J) (CoordinateConeArithVar.algebraMap_injective J hhor)
  rw [hdim] at hA
  have hA' : ((n + Fintype.card K : ℕ) : ℕ∞) = Cardinal.toENat (Algebra.trdeg ℤ (MRing ι ⧸ J)) + 1 := by
    exact_mod_cast hA
  obtain ⟨t, ht⟩ : ∃ t : ℕ, Cardinal.toENat (Algebra.trdeg ℤ (MRing ι ⧸ J)) = t := by
    refine ENat.ne_top_iff_exists.mp (fun htop => ?_) |>.imp fun _ h => h.symm
    rw [htop] at hA'
    simp at hA'
  rw [ht] at hA'
  refine ⟨t, Cardinal.toENat_eq_natCast.mp ht, ?_⟩
  exact_mod_cast hA'.symm

theorem aeval_mem_closure {σ : Type} {L : Type} [Field L] (y : σ → L) (f : MvPolynomial σ ℤ) :
    aeval y f ∈ Subfield.closure (Set.range y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [intCast_mem]
  | add f g hf hg => simpa using add_mem hf hg
  | mul_X f i hf => simpa using mul_mem hf (Subfield.subset_closure ⟨i, rfl⟩)

end FibreTranscendenceDegree

open FibreTranscendenceDegree in

theorem FibreDim.proof : FibreDimStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r G hv hP' hP
  classical
  refine ⟨⟨RingHom.ker_isPrime _, Targets.FibreMultiHomog.proof K ι K' ι' κ v P' G hv hP'.2.1.2.1,
    fun k => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hP'.2.1.2.2 k.1
    refine ⟨i, fun h => hi ?_⟩
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at h
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h
  rw [fibreIdeal, Inter.EvalKerKrullDim.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ']
  set E := IntermediateField.adjoin G.Φ
    (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G.x' ⟨q.1.1, q.2⟩) with hEdef

  have hZ : Function.Injective (algebraMap ℤ G.Φ) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : (C a : MRing ι) ∈ imageZ v P' := by
      rw [← G.ker_x, RingHom.mem_ker, aeval_C]
      exact ha
    have h' : a ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := hmem
    rw [show (imageZ v P').comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1] at h'
    exact (Submodule.mem_bot ℤ).mp h'

  obtain ⟨t, ht, htd⟩ := trdeg_of_isArithVar hP
  have hΦ : Algebra.trdeg ℤ G.Φ = t := by
    rw [trdeg_eq_of_forall_div (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).range hZ, ← trdeg_quot_ker, G.ker_x, ht]
    intro c
    obtain ⟨f, g, hg, rfl⟩ := G.gen c
    exact ⟨_, _, ⟨f, rfl⟩, ⟨g, rfl⟩, hg, rfl⟩

  have hxE : ∀ q, G.x' q ∈ E := by
    intro q
    by_cases hq : q.1 ∈ Set.range κ
    · obtain ⟨p, rfl⟩ := hv.2.2.2 q hq
      rw [G.compat]
      exact E.algebraMap_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩
  set xE : (Σ k', ι' k') → E := fun q => ⟨G.x' q, hxE q⟩ with hxEdef
  have hval : ∀ f : MRing ι', ((aeval xE f : E) : G.Φ') = aeval G.x' f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add, IntermediateField.coe_add, hf, hg]
    | mul_X f i hf =>
      simp only [map_mul, IntermediateField.coe_mul, hf, aeval_X]
      rfl
  have hkerE : RingHom.ker (aeval xE : MRing ι' →ₐ[ℤ] E) = P' := by
    ext f
    rw [RingHom.mem_ker]
    constructor
    · intro h
      have h2 : f ∈ RingHom.ker (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ') := by
        rw [RingHom.mem_ker, ← hval f, h]
        rfl
      rwa [G.genericFibre_ker_target] at h2
    · intro h
      have h2 := h
      rw [← G.genericFibre_ker_target, RingHom.mem_ker, ← hval f] at h2
      exact Subtype.ext h2

  obtain ⟨t', ht', htd'⟩ := trdeg_of_isArithVar hP'
  have hZE : Function.Injective (algebraMap ℤ E) := by
    intro a b hab
    apply hZ
    apply (algebraMap G.Φ E).injective
    simpa using hab
  have hE : Algebra.trdeg ℤ E = t' := by
    rw [trdeg_eq_of_forall_div (aeval xE : MRing ι' →ₐ[ℤ] E).range hZE, ← trdeg_quot_ker, hkerE, ht']
    intro e

    have hle : E.toSubfield ≤ Subfield.closure (Set.range G.x') := by
      rw [hEdef, IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
      · rintro _ ⟨c, rfl⟩
        obtain ⟨f, g, -, rfl⟩ := G.gen c
        have key : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) = aeval G.x' (rename v f) := by
          intro f
          induction f using MvPolynomial.induction_on with
          | C a => simp
          | add f g hf hg => simp only [map_add, hf, hg]
          | mul_X f i hf => simp only [map_mul, hf, aeval_X, rename_X, G.compat]
        rw [map_div₀, key, key]
        exact div_mem (aeval_mem_closure _ _) (aeval_mem_closure _ _)
      · rintro _ ⟨q, rfl⟩
        exact Subfield.subset_closure ⟨_, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.mp (hle e.2)
    have hsub : Subring.closure (Set.range G.x') ≤ (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').range.toSubring := by
      rw [Subring.closure_le]
      rintro _ ⟨q, rfl⟩
      exact ⟨X q, aeval_X _ _⟩
    obtain ⟨f, rfl⟩ := hsub ha
    obtain ⟨g, rfl⟩ := hsub hb
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hab
    by_cases hg : aeval xE g = 0
    · refine ⟨0, 1, zero_mem _, one_mem _, one_ne_zero, ?_⟩
      have hg' : (aeval G.x' g : G.Φ') = 0 := by rw [← hval, hg]; rfl
      apply Subtype.ext
      rw [← hab, hg', div_zero]
      simp
    · refine ⟨aeval xE f, aeval xE g, ⟨f, rfl⟩, ⟨g, rfl⟩, hg, ?_⟩
      apply Subtype.ext
      rw [IntermediateField.coe_div, hval, hval]
      exact hab.symm

  have : FaithfulSMul ℤ G.Φ := (faithfulSMul_iff_algebraMap_injective ℤ G.Φ).mpr hZ
  have : FaithfulSMul G.Φ E := (faithfulSMul_iff_algebraMap_injective G.Φ E).mpr (algebraMap G.Φ E).injective
  have hadd := trdeg_add_eq ℤ G.Φ (A := E)
  rw [hΦ, hE] at hadd
  have hc : Fintype.card (FibreBlock κ) + Fintype.card K = Fintype.card K' := by
    simp only [← Nat.card_eq_fintype_card]
    have h1 := Set.ncard_add_ncard_compl (Set.range κ)
    rw [Set.ncard_range_of_injective hv.1, add_comm] at h1
    exact h1
  have hlt : Algebra.trdeg G.Φ E < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_add_self.trans_eq hadd) Cardinal.natCast_lt_aleph0
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hlt
  rw [hm] at hadd
  have hm' : t + m = t' := by exact_mod_cast hadd
  have hmr : m = r + Fintype.card (FibreBlock κ) := by omega
  rw [hm, hmr, Cardinal.toENat_nat]
  rfl

end GroundTheory.Heights₂.Heights.ForSecondHalf
