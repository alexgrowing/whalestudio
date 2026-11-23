import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusCommStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQpStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExtStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLawsStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc Polynomial
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.InvCris

section Abstract
variable {k Ω B D : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing B] [CommRing D]
  {U : IntermediateField k Ω} {ι : B →+* D} {O : Ω →+* D} {u : U →+* B} {φ : B →+* B} {σ : U →ₐ[k] U}

theorem aeval_step [Nontrivial D] (hι : Function.Injective ι) (hu : ∀ c : U, ι (u c) = O c)
    (hφ : ∀ c : U, φ (u c) = u (σ c)) {b : B} {y y' : Ω} (hy : ι b = O y) (hy' : ι (φ b) = O y')
    (q : k[X]) (hq : aeval y q = 0) : aeval y' q = 0 := by
  set v : k →+* B := u.comp (algebraMap k U) with hv
  have e1 : ι.comp v = O.comp (algebraMap k Ω) := by
    ext c
    simp [hv, hu]
  have e2 : φ.comp v = v := by
    ext c
    simp [hv, hφ]
  have key : ∀ (x : B) (z : Ω), ι x = O z → ι (q.eval₂ v x) = O (aeval z q) := by
    intro x z h
    rw [aeval_def, hom_eval₂, hom_eval₂, e1, h]
  have h0 : q.eval₂ v b = 0 := hι (by rw [key b y hy, hq, map_zero, map_zero])
  have h1 : q.eval₂ v (φ b) = 0 := by
    have := congrArg φ h0
    rwa [hom_eval₂, e2, map_zero] at this
  apply O.injective
  rw [← key _ _ hy', h1, map_zero, map_zero]

theorem periodic [Nontrivial D] [Algebra.IsAlgebraic k Ω] (hι : Function.Injective ι)
    (hu : ∀ c : U, ι (u c) = O c) (hφ : ∀ c : U, φ (u c) = u (σ c)) (S : AddSubgroup B)
    (hS : ∀ b ∈ S, φ b ∈ S) (hO : ∀ b ∈ S, ∃ y, ι b = O y) {b : B} (hb : b ∈ S) :
    ∃ N, 0 < N ∧ φ^[N] b = b := by
  have hint : ∀ y : Ω, IsIntegral k y := fun y => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hit : ∀ (i : ℕ) (x : B), x ∈ S → φ^[i] x ∈ S := by
    intro i x hx
    induction i with
    | zero => exact hx
    | succ i ih => rw [Function.iterate_succ_apply']; exact hS _ ih
  have hinj0 : ∀ x ∈ S, φ x = 0 → x = 0 := by
    intro x hx h
    obtain ⟨y, hy⟩ := hO x hx
    have := aeval_step hι hu hφ hy (y' := 0) (by rw [h, map_zero, map_zero]) _ (minpoly.aeval k y)
    rw [← coeff_zero_eq_aeval_zero', map_eq_zero, minpoly.coeff_zero_eq_zero (hint y)] at this
    exact hι (by rw [hy, this, map_zero, map_zero])
  have hinj : ∀ (i : ℕ) (x : B), x ∈ S → φ^[i] x = φ^[i] b → x = b := by
    intro i
    induction i with
    | zero => exact fun x _ h => h
    | succ i ih =>
      intro x hx h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
      refine ih x hx (sub_eq_zero.1 (hinj0 _ (S.sub_mem (hit i x hx) (hit i b hb)) ?_))
      rw [map_sub, h, sub_self]
  choose y hy using fun i : ℕ => hO _ (hit i b hb)
  have hroot : ∀ i, aeval (y i) (minpoly k (y 0)) = 0 := by
    intro i
    induction i with
    | zero => exact minpoly.aeval k _
    | succ i ih =>
      exact aeval_step hι hu hφ (hy i) (by rw [← hy (i + 1), Function.iterate_succ_apply']) _ ih
  obtain ⟨i, j, hij, h⟩ := (Polynomial.rootSet_finite (minpoly k (y 0)) Ω).exists_lt_map_eq_of_forall_mem
    (f := y) (fun i => (Polynomial.mem_rootSet_of_ne (minpoly.ne_zero (hint _))).2 (hroot i))
  refine ⟨j - i, Nat.sub_pos_of_lt hij, hinj i _ (hit _ _ hb) ?_⟩
  rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hij.le]
  exact hι (by rw [hy, hy, h])

theorem mem_range (hu : ∀ c : U, ι (u c) = O c) (hφ : ∀ c : U, φ (u c) = u (σ c))
    (fund : ∀ (b : B) (y : Ω), φ b = b → ι b = O y → ∃ c : k, u (algebraMap k U c) = b)
    {b : B} {N : ℕ} (hN : 0 < N) (hb : φ^[N] b = b) (hO : ∀ i, ∃ y, ι (φ^[i] b) = O y)
    {ζ : U} (hζ : σ^[N] ζ = ζ) (hζ' : ∀ i, 0 < i → i < N → σ^[i] ζ ≠ ζ) : ∃ c, u c = b := by
  choose y hy using hO
  have tr : ∀ n : ℕ, ∑ i ∈ Finset.range N, u ((σ^[i] ζ) ^ n) * φ^[i] b ∈ u.range := by
    intro n
    obtain ⟨c, hc⟩ := fund (∑ i ∈ Finset.range N, u ((σ^[i] ζ) ^ n) * φ^[i] b)
      (∑ i ∈ Finset.range N, (((σ^[i] ζ) ^ n : U) : Ω) * y i) (by
        rw [map_sum]
        have e : ∀ i, φ (u ((σ^[i] ζ) ^ n) * φ^[i] b) = u ((σ^[i + 1] ζ) ^ n) * φ^[i + 1] b := by
          intro i
          rw [map_mul, hφ, map_pow σ, Function.iterate_succ_apply', Function.iterate_succ_apply']
        simp only [e]
        have h1 := Finset.sum_range_succ (fun i => u ((σ^[i] ζ) ^ n) * φ^[i] b) N
        have h2 := Finset.sum_range_succ' (fun i => u ((σ^[i] ζ) ^ n) * φ^[i] b) N
        rw [h1, hζ, hb] at h2
        exact (add_right_cancel h2).symm) (by
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_mul, hu, hy])
    exact ⟨_, hc⟩
  have pol : ∀ p : U[X], ∑ i ∈ Finset.range N, u (p.eval (σ^[i] ζ)) * φ^[i] b ∈ u.range := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [eval_add, map_add, add_mul, Finset.sum_add_distrib]
      exact add_mem hp hq
    | monomial n a =>
      simp only [eval_monomial, map_mul, mul_assoc, ← Finset.mul_sum]
      exact mul_mem ⟨a, rfl⟩ (tr n)
  obtain ⟨c, hc⟩ := pol (∏ j ∈ (Finset.range N).erase 0, (X - C (σ^[j] ζ)))
  rw [Finset.sum_eq_single 0] at hc
  · have hne : (∏ j ∈ (Finset.range N).erase 0, (X - C (σ^[j] ζ))).eval (σ^[0] ζ) ≠ 0 := by
      rw [eval_prod]
      refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
      rw [Finset.mem_erase, Finset.mem_range] at hj
      simpa [sub_eq_zero] using (hζ' j (Nat.pos_of_ne_zero hj.1) hj.2).symm
    refine ⟨((∏ j ∈ (Finset.range N).erase 0, (X - C (σ^[j] ζ))).eval (σ^[0] ζ))⁻¹ * c, ?_⟩
    rw [map_mul, hc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
    rfl
  · intro i hi hi0
    rw [eval_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hi0, hi⟩) (by simp), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 hN) h

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem exists_period (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l) {N : ℕ} (hN : 0 < N) :
    ∃ ζ : ↥(MaximalUnramifiedExtension l), σ^[N] ζ = ζ ∧ ∀ i, 0 < i → i < N → σ^[i] ζ ≠ ζ := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have h1 : 1 < l ^ N := Nat.one_lt_pow hN.ne' hl
  have hm : 0 < l ^ N - 1 := by omega
  have hd : ¬ l ∣ l ^ N - 1 := by
    intro h
    have h2 : l ∣ l ^ N := dvd_pow_self l hN.ne'
    have := (Nat.dvd_sub h2 h)
    rw [Nat.sub_sub_self h1.le, Nat.dvd_one] at this
    omega
  haveI : NeZero ((l ^ N - 1 : ℕ) : Om l) := ⟨by exact_mod_cast hm.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ N - 1)
  have hzm : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, hm, hd, hz.pow_eq_one⟩
  set ζ : ↥(MaximalUnramifiedExtension l) := ⟨z, hzm⟩ with hζ
  have hp : IsPrimitiveRoot ζ (l ^ N - 1) :=
    IsPrimitiveRoot.of_map_of_injective (f := (MaximalUnramifiedExtension l).val) hz Subtype.val_injective
  have hit : ∀ i, σ^[i] ζ = ζ ^ l ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, map_pow, hσ ζ _ hm hd hp.pow_eq_one, ← pow_mul, pow_succ']
  have hz0 : ζ ≠ 0 := hp.ne_zero hm.ne'
  have hpw : ∀ i, ζ ^ l ^ i = ζ ^ (l ^ i - 1) * ζ := by
    intro i
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]
  refine ⟨ζ, by rw [hit, hpw, hp.pow_eq_one, one_mul], fun i hi hiN h => ?_⟩
  rw [hit, hpw, mul_eq_right₀ hz0] at h
  have h3 : 1 < l ^ i := Nat.one_lt_pow hi.ne' hl
  have h4 : l ^ i < l ^ N := Nat.pow_lt_pow_right hl hiN
  exact hp.pow_ne_one_of_pos_of_lt (by omega) (by omega) h

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem invariants_Bcris : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (b : Per.Bcris l),
    (∀ g ∈ GK K, Per.σB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ C.u c = b := by
  intro l _ C K b hb
  obtain ⟨hφ, -, -, hι, hσ, -⟩ := GlobalTheory.T.localPeriodRingsData_unramified_laws l C
  have hcomm := (GlobalTheory.T.periodRings_galoisAction_laws_frobenius_comm l).2.2.2.2.1
  have hfil := (GlobalTheory.T.bdR_filtration_laws l).2.2.2.2.2.2 0
  rcases subsingleton_or_nontrivial (Per.BdR l) with hs | hs
  · exact ⟨0, zero_mem _, hι (Subsingleton.elim _ _)⟩
  let O : Om l →+* Per.BdR l := (algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o
  have hu : ∀ c : ↥(MaximalUnramifiedExtension l), C.ι (C.u c) = O c := C.ι_u
  let S : AddSubgroup (Per.Bcris l) :=
    { carrier := {x | ∀ g ∈ GK K, Per.σB g x = x}
      zero_mem' := fun g _ => map_zero _
      add_mem' := fun {x y} hx hy g hg => by rw [map_add, hx g hg, hy g hg]
      neg_mem' := fun {x} hx g hg => by rw [map_neg, hx g hg] }
  have hS : ∀ x ∈ S, Per.φB l x ∈ S := fun x hx g hg => by rw [← hcomm, hx g hg]
  have hO' : ∀ x ∈ S, ∃ y ∈ K.1, C.ι x = O y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := GlobalTheory.T.bdR_galois_invariants_eq_finExt l C K (C.ι x) (fun g hg => by rw [← hσ, hx g hg])
    exact ⟨y, hy, e.symm⟩
  have hO : ∀ x ∈ S, ∃ y, C.ι x = O y := fun x hx => (hO' x hx).imp fun _ h => h.2
  have fund : ∀ (x : Per.Bcris l) (y : Om l), Per.φB l x = x → C.ι x = O y →
      ∃ c : ℚ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = x := by
    intro x y h1 h2
    refine GlobalTheory.T.bcris_frobenius_fixed_fil_zero_eq_qp l C x h1 ?_
    rw [h2]
    refine (hfil (C.o y)).2 ?_
    have hone : (1 : Per.BdRp l) ∈ Per.FilP l 0 :=
      (hfil 1).1 (by rw [map_one]; exact (GlobalTheory.T.bdR_filtration_laws l).2.1)
    simpa using Ideal.mul_mem_left _ (C.o y) hone
  have hbS : b ∈ S := hb
  obtain ⟨N, hN, hper⟩ := periodic hι hu hφ S hS hO hbS
  obtain ⟨ζ, h1, h2⟩ := exists_period C.σ C.σ_root hN
  have hit : ∀ i, (Per.φB l)^[i] b ∈ S := by
    intro i
    induction i with
    | zero => rw [Function.iterate_zero_apply]; exact hbS
    | succ i ih => rw [Function.iterate_succ_apply']; exact hS _ ih
  obtain ⟨c, hc⟩ := mem_range hu hφ fund hN hper (fun i => hO _ (hit i)) h1 h2
  obtain ⟨y, hy, e⟩ := hO' b hbS
  refine ⟨c, ?_, hc⟩
  have : (c : Om l) = y := O.injective (by rw [← hu, hc, e])
  rwa [this]

end GlobalTheory.MemLoc.InvCris
