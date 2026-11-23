import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ChowSpec

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

def lastSubst {A : Type} [CommRing A] {N : ℕ} (D : ℕ) (t : Fin N → A) :
    Fin (D + 1) × Fin N → MvPolynomial (Fin D × Fin N) A :=
  fun v => Fin.lastCases (motive := fun _ => MvPolynomial (Fin D × Fin N) A)
    (C (t v.2)) (fun i => X (i, v.2)) v.1

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
@[simp] theorem _root_.GlobalTheory.ChowSpec.lastSubst_last {A : Type} [CommRing A] {N : ℕ} (D : ℕ)
    (t : Fin N → A) (j : Fin N) : _root_.GlobalTheory.ChowSpec.lastSubst D t (Fin.last D, j) = C (t j) := by
  simp [_root_.GlobalTheory.ChowSpec.lastSubst]

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
@[simp] theorem _root_.GlobalTheory.ChowSpec.lastSubst_castSucc {A : Type} [CommRing A] {N : ℕ} (D : ℕ)
    (t : Fin N → A) (i : Fin D) (j : Fin N) :
    _root_.GlobalTheory.ChowSpec.lastSubst D t (i.castSucc, j) = X (i, j) := by
  simp [_root_.GlobalTheory.ChowSpec.lastSubst]

def lastEquiv (K : Type) [CommRing K] (N D : ℕ) :
    MvPolynomial (Fin (D + 1) × Fin N) K ≃+* MvPolynomial (Fin D × Fin N) (MvPolynomial (Fin N) K) :=
  RingEquiv.ofRingHom
    (aeval (R := K) (lastSubst D (X : Fin N → MvPolynomial (Fin N) K))).toRingHom
    (eval₂Hom (aeval (R := K) (fun j => X (Fin.last D, j))).toRingHom
      (fun v => X (v.1.castSucc, v.2)))
    (by
      refine MvPolynomial.ringHom_ext' (MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_))
        (fun v => ?_) <;> simp)
    (by
      refine MvPolynomial.ringHom_ext (fun r => by simp) ?_
      rintro ⟨i, j⟩
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp)

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
private theorem isWeightedHomogeneous_aeval_of_forall {R S σ τ Γ Δ : Type} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid Γ] [AddCommMonoid Δ] {w : σ → Γ}
    {w' : τ → Δ} (g : Γ →+ Δ) {p : MvPolynomial σ R} {m : Γ}
    (hp : IsWeightedHomogeneous w p m) (φ : σ → MvPolynomial τ S)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ v) (g (w v))) :
    IsWeightedHomogeneous w' (aeval φ p) (g m) := by
  rw [p.as_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [mem_weightedHomogeneousSubmodule, aeval_monomial, Finsupp.prod]
  have hw : Finsupp.weight w s = m := hp (mem_support_iff.mp hs)
  have hm : g m = 0 + ∑ v ∈ s.support, s v • g (w v) := by
    rw [zero_add, ← hw, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp [map_nsmul]
  rw [hm, MvPolynomial.algebraMap_apply]
  exact (isWeightedHomogeneous_C w' _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun v _ => (hφ v).pow _)

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in

theorem _root_.GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)) (D δ : ℕ) (f : MvPolynomial (Fin (D + 1 + 1) × Fin N) K), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → _root_.GlobalTheory.ChowHt.IsChowFormInt P (D + 1) δ f → ∃ f' : MvPolynomial (Fin (D + 1) × Fin N) L, _root_.GlobalTheory.ChowHt.IsChowFormInt (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)}) D δ f' := by
  intro K L _ _ N _ _ _ _ P D δ f hP hf
  set t : Fin N → L := fun j => algebraMap (MvPolynomial (Fin N) K) L (X j) with ht
  set φ := _root_.GlobalTheory.ChowSpec.lastSubst (D + 1) t with hφ
  set f' : MvPolynomial (Fin (D + 1) × Fin N) L := aeval (R := K) φ f with hf'
  have hfhom : _root_.GlobalTheory.Chow.IsBlockHomogeneous f (fun _ => δ) :=
    _root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.1 hf.homog
  have hf'hom : _root_.GlobalTheory.Chow.IsBlockHomogeneous f' (fun _ => δ) := by
    unfold _root_.GlobalTheory.Chow.IsBlockHomogeneous at hfhom ⊢
    let g : (Fin (D + 1 + 1) → ℕ) →+ (Fin (D + 1) → ℕ) :=
      { toFun := fun a i => a i.castSucc, map_zero' := rfl, map_add' := fun _ _ => rfl }
    refine isWeightedHomogeneous_aeval_of_forall (S := L) g hfhom φ ?_
    rintro ⟨i, j⟩
    induction i using Fin.lastCases with
    | last =>
      have hg : g (_root_.GlobalTheory.Chow.blockWeight (Fin.last (D + 1), j)) = 0 := by
        funext i
        simp [g, _root_.GlobalTheory.Chow.blockWeight, Pi.single_apply, Fin.castSucc_ne_last]
      rw [hφ, _root_.GlobalTheory.ChowSpec.lastSubst_last, hg]
      exact isWeightedHomogeneous_C _ _
    | cast i =>
      have hg : g (_root_.GlobalTheory.Chow.blockWeight (i.castSucc, j)) = _root_.GlobalTheory.Chow.blockWeight (i, j) := by
        funext i'
        simp [g, _root_.GlobalTheory.Chow.blockWeight, Pi.single_apply]
      rw [hφ, _root_.GlobalTheory.ChowSpec.lastSubst_castSucc, hg]
      exact isWeightedHomogeneous_X _ _ _
  refine ⟨f', _root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.2 hf'hom, ?_, ?_⟩
  · have hkey : MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)
        (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1) f) = f' := by
      rw [hf']
      change ((MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)).comp
        (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1)).toRingHom) f = (aeval φ).toRingHom f
      congr 1
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
      · simp [_root_.GlobalTheory.ChowSpec.lastEquiv, MvPolynomial.algebraMap_apply,
          IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L]
      · rcases v with ⟨i, j⟩
        induction i using Fin.lastCases <;> simp [_root_.GlobalTheory.ChowSpec.lastEquiv, hφ, ht]
    set F := _root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1) f with hF
    have hFirr : Irreducible F :=
      (MulEquiv.irreducible_iff (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1))).2
        hf.irred
    have hF0 : F ≠ 0 := hFirr.ne_zero
    have hFprime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.1 hFirr
    have hδ : 0 < δ := by
      rcases Nat.eq_zero_or_pos δ with h | h
      · exfalso
        subst h
        have hh := hfhom.isHomogeneous
        simp only [Finset.sum_const_zero] at hh
        have hf0 := hf.ne_zero
        have hC : f = C (coeff 0 f) :=
          (totalDegree_eq_zero_iff_eq_C).1 (by simpa using hh.totalDegree hf0)
        have hc : coeff 0 f ≠ 0 := fun h0 => hf0 (by rw [hC, h0, C_0])
        apply hf.irred.not_isUnit
        rw [hC]
        exact hc.isUnit.map C
      · exact h
    have hf'0 : f' ≠ 0 := by
      rw [← hkey]
      exact fun h => hF0 ((map_eq_zero_iff _
        (MvPolynomial.map_injective _ (IsFractionRing.injective (MvPolynomial (Fin N) K) L))).1 h)
    have hnotunit : ¬ IsUnit f' := by
      intro hu
      obtain ⟨r, hr, hfr⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 hu
      have hh := hf'hom.isHomogeneous
      rw [hfr] at hh
      have h0 := hh (show coeff 0 (C r) ≠ 0 by simpa using hr.ne_zero)
      simp at h0
      omega
    have hdisj : Disjoint ((Submonoid.map (C : MvPolynomial (Fin N) K →+*
        MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
          (nonZeroDivisors (MvPolynomial (Fin N) K))) :
            Set (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K)))
        (↑(Ideal.span {F}) : Set (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))) := by
      rw [Set.disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ hmem
      obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 hmem
      apply hnotunit
      have hs0 : algebraMap (MvPolynomial (Fin N) K) L s ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      have hmapped := congrArg (MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)) hg
      rw [map_mul, hkey, map_C] at hmapped
      exact isUnit_of_mul_isUnit_right (hmapped ▸ hs0.isUnit.map C)
    have hprime := IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.map (C : MvPolynomial (Fin N) K →+*
        MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
          (nonZeroDivisors (MvPolynomial (Fin N) K)))
      (MvPolynomial (Fin (D + 1) × Fin N) L) (Ideal.span {F})
      ((Ideal.span_singleton_prime hF0).2 hFprime) hdisj
    rw [Ideal.map_span, Set.image_singleton] at hprime
    have hF' : algebraMap (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
        (MvPolynomial (Fin (D + 1) × Fin N) L) F = f' := hkey
    rw [hF'] at hprime
    exact ((Ideal.span_singleton_prime hf'0).1 hprime).irreducible
  · intro u
    set ũ : Fin (D + 1 + 1) × Fin N → AlgebraicClosure L := fun v =>
      Fin.lastCases (motive := fun _ => AlgebraicClosure L) (algebraMap L (AlgebraicClosure L) (t v.2))
        (fun i => u (i, v.2)) v.1 with hũ
    have hev : aeval u f' = aeval ũ f := by
      rw [hf']
      change ((aeval u).restrictScalars K) (aeval φ f) = aeval ũ f
      rw [← AlgHom.comp_apply, comp_aeval]
      refine congrArg (fun x => (aeval x) f) (funext fun v => ?_)
      rcases v with ⟨i, j⟩
      induction i using Fin.lastCases <;> simp [hφ, hũ]
    have hPhom : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) P := by
      intro i r hr
      convert hP r hr i using 1
      conv_lhs => rw [← sum_homogeneousComponent r]
      rw [DirectSum.decompose_sum, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum,
        Finset.sum_eq_single i]
      · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem i r)
      · intro b _ hb
        exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem b r) hb
      · intro hi
        have h0 : homogeneousComponent i r = 0 :=
          homogeneousComponent_eq_zero i r (by simp at hi; omega)
        rw [h0, DirectSum.decompose_zero]
        rfl
    have hideal : ∀ y : Fin N → AlgebraicClosure L,
        (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
          Ideal.span {(∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L)}, aeval y g = 0) ↔
        (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, ũ (Fin.last (D + 1), j) * y j = 0 := by
      intro y
      have hmap : ∀ g : MvPolynomial (Fin N) K,
          aeval y (MvPolynomial.map (algebraMap K L) g) = aeval y g := fun g => aeval_map_algebraMap L y g
      have hlin : aeval y (∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L) =
          ∑ j, ũ (Fin.last (D + 1), j) * y j := by
        simp [hũ]
      constructor
      · intro H
        refine ⟨fun g hg => ?_, ?_⟩
        · rw [← hmap]
          exact H _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))
        · rw [← hlin]
          exact H _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      · rintro ⟨H1, H2⟩ g hg
        have hle : P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
            Ideal.span {(∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L)} ≤
            RingHom.ker (aeval y : MvPolynomial (Fin N) L →ₐ[L] AlgebraicClosure L) := by
          refine sup_le (Ideal.map_le_iff_le_comap.2 fun g hg => ?_) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
          · simpa [RingHom.mem_ker, hmap] using H1 g hg
          · simpa [RingHom.mem_ker, hlin] using H2
        exact RingHom.mem_ker.1 (hle hg)
    rw [hev, hf.zero_iff_of_isAlgClosed hPhom ũ]
    constructor
    · rintro ⟨y, hy0, hyP, hyu⟩
      rw [Fin.forall_fin_succ'] at hyu
      exact ⟨y, hy0, (hideal y).2 ⟨hyP, hyu.2⟩, fun i => by simpa [hũ] using hyu.1 i⟩
    · rintro ⟨y, hy0, hyI, hyu⟩
      obtain ⟨hyP, hyh⟩ := (hideal y).1 hyI
      exact ⟨y, hy0, hyP, Fin.forall_fin_succ'.2 ⟨fun i => by simpa [hũ] using hyu i, hyh⟩⟩

end GlobalTheory.ChowSpec
