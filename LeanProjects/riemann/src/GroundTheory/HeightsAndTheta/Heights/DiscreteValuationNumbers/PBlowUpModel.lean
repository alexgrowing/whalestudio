import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsReesAlgebraDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Graded

variable {σ : Type*} {R : Type*} [CommRing R]

theorem weight_comp_addMonoidHom_apply {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (w : σ → M)
    (f : M →+ M') (d : σ →₀ ℕ) : Finsupp.weight (fun v => f (w v)) d = f (Finsupp.weight w d) := by
  simp [Finsupp.weight_apply, Finsupp.sum, map_sum, map_nsmul]

theorem weightedHomogeneousComponent_monomial' {M : Type*} [AddCommMonoid M] [DecidableEq M]
    (w : σ → M) (n : M) (d : σ →₀ ℕ) (c : R) :
    weightedHomogeneousComponent w n (monomial d c) =
      if Finsupp.weight w d = n then monomial d c else 0 := by
  ext e
  rw [coeff_weightedHomogeneousComponent]
  by_cases hed : e = d
  · subst hed
    split_ifs <;> simp
  · classical
    split_ifs <;> simp [coeff_monomial, Ne.symm hed]

theorem coeff_aeval_C_mul_X_pow {B : Type*} [CommRing B] [Algebra R B] (a : σ → B) (ω : σ → ℕ)
    (n : ℕ) (p : MvPolynomial σ R) :
    (aeval (fun v => Polynomial.C (a v) * Polynomial.X ^ ω v) p).coeff n =
      aeval a (weightedHomogeneousComponent ω n p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have h : aeval (fun v => Polynomial.C (a v) * Polynomial.X ^ ω v) (monomial d c) =
        Polynomial.C (aeval a (monomial d c)) * Polynomial.X ^ (Finsupp.weight ω d) := by
      rw [aeval_monomial, aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.prod,
        Finsupp.sum, Polynomial.algebraMap_apply]
      simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum,
        ← Polynomial.C_pow, ← map_prod, map_mul, smul_eq_mul, mul_comm (ω _)]
      ring
    rw [h, Polynomial.coeff_C_mul_X_pow, weightedHomogeneousComponent_monomial']
    by_cases hd : Finsupp.weight ω d = n
    · rw [if_pos hd.symm, if_pos hd]
    · rw [if_neg (Ne.symm hd), if_neg hd, map_zero]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]

theorem aeval_weightedHomogeneousComponent_of_forms {K : Type*} [DecidableEq K] {ι : K → Type*}
    (ω : σ → K → ℕ) (e : σ → MRing ι R) (he : ∀ v, IsMultiHomog (e v) (ω v)) (m : K → ℕ)
    (p : MvPolynomial σ R) :
    aeval e (weightedHomogeneousComponent ω m p) =
      weightedHomogeneousComponent (blockWeight ι) m (aeval e p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hmon : IsWeightedHomogeneous (blockWeight ι) (aeval e (monomial d c))
        (Finsupp.weight ω d) := by
      rw [aeval_monomial, Finsupp.weight_apply, algebraMap_eq]
      have := (isWeightedHomogeneous_C (blockWeight ι) c).mul (IsWeightedHomogeneous.prod d.support
        (fun v => e v ^ d v) (fun v => d v • ω v) (fun v _ => (he v).pow (d v)))
      rw [zero_add] at this
      exact this
    by_cases hdm : Finsupp.weight ω d = m
    · have hmon' : IsWeightedHomogeneous (blockWeight ι) (aeval e (monomial d c)) m := hdm ▸ hmon
      rw [(isWeightedHomogeneous_monomial _ d c hdm).weightedHomogeneousComponent_same,
        hmon'.weightedHomogeneousComponent_same]
    · rw [(isWeightedHomogeneous_monomial ω d c
        (m := Finsupp.weight ω d) rfl).weightedHomogeneousComponent_ne m
        (Ne.symm hdm), hmon.weightedHomogeneousComponent_ne m (Ne.symm hdm), map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

end Graded

section BlowUp

variable {K : Type*} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

def blowUpAtOne (u : J → MRing ι R) : (Σ o, extIdx ι J o) → MRing ι R
  | ⟨none, j⟩ => u j
  | ⟨some k, i⟩ => X ⟨k, i⟩

def blowUpDegMap (N : K → ℕ) : (Option K → ℕ) →+ (K → ℕ) where
  toFun m k := m (some k) + m none * N k
  map_zero' := by
    funext k
    simp
  map_add' m m' := by
    funext k
    simp only [Pi.add_apply]
    ring

theorem isMultiHomogIdeal_blowUpOf {P : Ideal (MRing ι R)} (hP : IsMultiHomogIdeal P) (N : K → ℕ)
    (u : J → MRing ι R) (hu : ∀ j, IsMultiHomog (u j) N) : IsMultiHomogIdeal (blowUpOf P u) := by
  classical
  set w := blockWeight (extIdx ι J)
  set L := blowUpDegMap N
  set ωT : (Σ o, extIdx ι J o) → ℕ := fun v => Pi.evalAddMonoidHom (fun _ => ℕ) none (w v)
  set ωL : (Σ o, extIdx ι J o) → K → ℕ := fun v => L (w v)
  have hT : ∀ d, Finsupp.weight ωT d = Finsupp.weight w d none := fun d =>
    weight_comp_addMonoidHom_apply w (Pi.evalAddMonoidHom (fun _ => ℕ) none) d
  have hL : ∀ d, Finsupp.weight ωL d = L (Finsupp.weight w d) := fun d =>
    weight_comp_addMonoidHom_apply w L d

  have hθ : ∀ v, IsMultiHomog (blowUpAtOne u v) (ωL v) := by
    rintro ⟨o, i⟩
    cases o with
    | none =>
      have : ωL ⟨none, i⟩ = N := by
        funext k
        simp [ωL, L, w, blowUpDegMap, blockWeight]
      rw [this]
      exact hu i
    | some k =>
      have : ωL ⟨some k, i⟩ = blockWeight ι ⟨k, i⟩ := by
        funext k'
        simp [ωL, L, w, blowUpDegMap, blockWeight, Pi.single_apply]
      rw [this]
      exact isWeightedHomogeneous_X R _ _

  have hsubst : blowUpSubst P u = fun v =>
      Polynomial.C (Ideal.Quotient.mkₐ R P (blowUpAtOne u v)) * Polynomial.X ^ ωT v := by
    funext v
    obtain ⟨o, i⟩ := v
    cases o <;> simp [blowUpSubst, blowUpAtOne, ωT, w, blockWeight]
  have hcoeff : ∀ r n, (aeval (R := R) (blowUpSubst P u) r).coeff n =
      Ideal.Quotient.mk P (aeval (blowUpAtOne u) (weightedHomogeneousComponent ωT n r)) := by
    intro r n
    rw [hsubst, coeff_aeval_C_mul_X_pow, ← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply,
      comp_aeval]

  have key : ∀ D m : Option K → ℕ, D = m ↔ L D = L m ∧ D none = m none := by
    intro D m
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      funext o
      cases o with
      | none => exact h2
      | some k =>
        have := congrFun h1 k
        simp only [L, blowUpDegMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h2] at this
        omega
  have hsplit : ∀ (m : Option K → ℕ) (n : ℕ) (r : MRing (extIdx ι J) R),
      weightedHomogeneousComponent ωT n (weightedHomogeneousComponent w m r) =
        if n = m none then weightedHomogeneousComponent ωL (L m) (weightedHomogeneousComponent ωT n r)
        else 0 := by
    intro m n r
    ext d
    split_ifs with hn
    · simp only [coeff_weightedHomogeneousComponent, hT, hL, key (Finsupp.weight w d) m]
      subst hn
      by_cases h1 : Finsupp.weight w d none = m none <;> by_cases h2 : L (Finsupp.weight w d) = L m <;>
        simp [h1, h2]
    · simp only [coeff_weightedHomogeneousComponent, hT, key (Finsupp.weight w d) m, coeff_zero]
      by_cases h1 : Finsupp.weight w d none = n
      · have : ¬ Finsupp.weight w d none = m none := fun h => hn (h1.symm.trans h)
        simp [h1, hn]
      · simp [h1]
  intro p hp m
  rw [blowUpOf, RingHom.mem_ker] at hp ⊢
  refine Polynomial.ext fun n => ?_
  rw [hcoeff, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem, hsplit]
  split_ifs with hn
  · rw [aeval_weightedHomogeneousComponent_of_forms ωL _ hθ]
    apply hP
    have := hcoeff p n
    rw [hp, Polynomial.coeff_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this.symm
  · rw [map_zero]
    exact P.zero_mem

end BlowUp

theorem BlowUpModel.proof (h₁ : ReesAlgebraDim.Statement.{u}) : BlowUpModel.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P d hP N u hu hne
  have : P.IsPrime := hP.multiProj.isPrime
  set φ : MRing (extIdx ι J) O →ₐ[O] Polynomial (MRing ι O ⧸ P) := aeval (blowUpSubst P u)
  refine ⟨⟨RingHom.ker_isPrime φ, isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu, ?_⟩,
    ?_, ?_⟩
  ·
    intro o
    cases o with
    | none =>
      obtain ⟨j, hj⟩ := hne
      refine ⟨j, ?_⟩
      rw [blowUpOf, RingHom.mem_ker]
      change aeval (blowUpSubst P u) (X ⟨none, j⟩) ≠ 0
      rw [aeval_X]
      simpa [blowUpSubst, Ideal.Quotient.eq_zero_iff_mem] using hj
    | some k =>
      obtain ⟨i, hi⟩ := hP.multiProj.relevant k
      refine ⟨i, ?_⟩
      rw [blowUpOf, RingHom.mem_ker]
      change aeval (blowUpSubst P u) (X ⟨some k, i⟩) ≠ 0
      rw [aeval_X]
      simpa [blowUpSubst, Ideal.Quotient.eq_zero_iff_mem] using hi
  ·
    ext c
    rw [Ideal.mem_comap, blowUpOf, RingHom.mem_ker, Ideal.mem_bot]
    change aeval (blowUpSubst P u) (C c) = 0 ↔ c = 0
    rw [aeval_C, Polynomial.algebraMap_apply, Polynomial.C_eq_zero,
      show algebraMap O (MRing ι O ⧸ P) c = Ideal.Quotient.mk P (C c) from rfl,
      Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hP.noTorsion, Ideal.mem_bot]
  ·
    set I : Ideal (MRing ι O ⧸ P) := Ideal.span (Set.range fun j => Ideal.Quotient.mk P (u j))
    have hI : I ≠ ⊥ := by
      obtain ⟨j, hj⟩ := hne
      intro h
      apply hj
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h]
      exact Ideal.subset_span ⟨j, rfl⟩
    have hC : ∀ c : MRing ι O ⧸ P, Polynomial.C c ∈ φ.range := by
      intro c
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact ⟨liftForm (J := J) q, aeval_blowUpSubst_liftForm P u q⟩
    have hrange : φ.range.toSubring = (reesAlgebra I).toSubring := by
      ext x
      simp only [Subalgebra.mem_toSubring]
      constructor
      · rintro ⟨p, rfl⟩
        induction p using MvPolynomial.induction_on with
        | C a =>
          change aeval (blowUpSubst P u) (C a) ∈ reesAlgebra I
          rw [aeval_C, Polynomial.algebraMap_apply]
          exact (reesAlgebra I).algebraMap_mem _
        | add p q hp hq =>
          rw [map_add]
          exact add_mem hp hq
        | mul_X p v hp =>
          rw [map_mul]
          refine mul_mem hp ?_
          change aeval (blowUpSubst P u) (X v) ∈ reesAlgebra I
          rw [aeval_X]
          obtain ⟨o, i⟩ := v
          cases o with
          | none =>
            change Polynomial.C (Ideal.Quotient.mk P (u i)) * Polynomial.X ∈ reesAlgebra I
            rw [Polynomial.C_mul_X_eq_monomial]
            exact reesAlgebra.monomial_mem.mpr (by rw [pow_one]; exact Ideal.subset_span ⟨i, rfl⟩)
          | some k =>
            exact (reesAlgebra I).algebraMap_mem _
      · intro hx
        rw [← adjoin_monomial_eq_reesAlgebra] at hx
        induction hx using Algebra.adjoin_induction with
        | mem x hx =>
          obtain ⟨a, ha, rfl⟩ := hx
          induction ha using Submodule.span_induction with
          | mem a ha =>
            obtain ⟨j, rfl⟩ := ha
            refine ⟨X ⟨none, j⟩, ?_⟩
            change aeval (blowUpSubst P u) (X ⟨none, j⟩) = _
            rw [aeval_X]
            exact Polynomial.C_mul_X_eq_monomial
          | zero =>
            rw [map_zero]
            exact zero_mem _
          | add a b _ _ ha hb =>
            rw [map_add]
            exact add_mem ha hb
          | smul c a _ ha =>
            rw [LinearMap.map_smul, Polynomial.smul_eq_C_mul]
            exact mul_mem (hC c) ha
        | algebraMap a =>
          rw [Polynomial.algebraMap_eq]
          exact hC a
        | add x y _ _ hx hy => exact add_mem hx hy
        | mul x y _ _ hx hy => exact mul_mem hx hy
    have e : (MRing (extIdx ι J) O ⧸ blowUpOf P u) ≃+* reesAlgebra I :=
      (Ideal.quotientKerEquivRange φ).toRingEquiv.trans (RingEquiv.subringCongr hrange)
    rw [ringKrullDim_eq_of_ringEquiv e, h₁ (MRing ι O ⧸ P) I hI _ hP.dim, Fintype.card_option]
    rfl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
