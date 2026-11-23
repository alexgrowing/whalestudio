import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsDegreePos
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTwistSections
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertPrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertDimZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertIncrement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntersectionRecursion
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulesFromPrimes
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedFiltration
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiltrationHilbSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRankOfSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace HilbertPositive

theorem hilbertPrime : HilbertSamuel.HilbertPrime.Statement.{u} :=
  HilbertSamuel.HilbertPrime.proof HilbertSamuel.HilbertDimZero.proof
    (HilbertSamuel.HilbertIncrement.proof HilbertSamuel.IntersectionRecursion.proof)
    (HilbertSamuel.MixedNumberPolynomial.proof
      (HilbertSamuel.MultigradedHilbertPolynomial.proof HilbertSamuel.EventualPolynomial.proof))
    (HilbertSamuel.ModulesFromPrimes.proof HilbertSamuel.MultigradedFiltration.proof
      HilbertSamuel.FiltrationHilbSum.proof HilbertSamuel.DegLTGrowth.proof)

theorem mixedNumber : HilbertSamuel.MixedNumberPolynomial.Statement.{u} :=
  HilbertSamuel.MixedNumberPolynomial.proof
    (HilbertSamuel.MultigradedHilbertPolynomial.proof HilbertSamuel.EventualPolynomial.proof)

def blockEquiv (N : ℕ) : (Σ _ : Unit, Fin (N + 1)) ≃ Fin (N + 1) where
  toFun v := v.2
  invFun i := ⟨(), i⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem weight_blockWeight_one (d : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) d = fun _ => d.degree := by
  funext u
  rw [Finsupp.weight_apply, Finsupp.degree, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [NumbersDVR.blockWeight]

theorem isWeightedHomogeneous_iff (p : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) p (fun _ => n) ↔
      p.IsHomogeneous n := by
  constructor
  · intro h d hd
    have h1 : d.degree = n := congrFun ((weight_blockWeight_one d).symm.trans (h hd)) ()
    rw [← h1, Finsupp.degree_eq_weight_one]
    rfl
  · intro h d hd
    rw [weight_blockWeight_one]
    funext _
    rw [Finsupp.degree_eq_weight_one]
    exact h hd

theorem ringKrullDim_primeOfOne (y : Fin (N + 1) → Ω) :
    ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ringKrullDim (Poly k N ⧸ primeOf (S := k) y) := by
  let f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (blockEquiv N)).toRingEquiv
  have hc : primeOfOne (S := k) y = (primeOf (S := k) y).comap f.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  have h : primeOf (S := k) y = (primeOfOne (S := k) y).map f.toRingHom := by
    rw [hc, Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ f h)

theorem ne_zero_of_isSubvar {y : Fin (N + 1) → Ω} {e : ℕ} (h : IsSubvar y (primeOf (S := k) y) e) :
    y ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  intro hy
  apply hi
  rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k i), aeval_X, hy, Pi.zero_apply]

theorem finrank_piece_eq_hilbFn (y : Fin (N + 1) → Ω) (n : ℕ) :
    (Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℤ) =
      NumbersDVR.hilbFn (primeOfOne (S := k) y) (fun _ => (n : ℤ)) := by
  classical
  rw [NumbersDVR.hilbFn, if_pos (fun _ => Int.natCast_nonneg n)]
  simp only [Int.toNat_natCast]
  congr 1
  set V := weightedHomogeneousSubmodule k (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1)))
    (fun _ : Unit => n) with hV
  let f₁ : V →ₗ[k] NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y :=
    (Ideal.Quotient.mkₐ k (primeOfOne (S := k) y)).toLinearMap ∘ₗ V.subtype
  let f₂ : V →ₗ[k] Ω :=
    (aeval (fun v : Σ _ : Unit, Fin (N + 1) => y v.2)).toLinearMap ∘ₗ V.subtype
  have hhom : ∀ v ∈ V, (oneBlock (S := k) (N := N) v).IsHomogeneous n := fun v hv =>
    ((isWeightedHomogeneous_iff v n).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hv)).rename_isHomogeneous
  have heval : ∀ v, aeval y (oneBlock (S := k) (N := N) v) = aeval (fun w : Σ _ : Unit, Fin (N + 1) => y w.2) v :=
    fun v => by rw [oneBlock, aeval_rename]; rfl
  have hr₁ : LinearMap.range f₁ = NumbersDVR.gradedPiece (primeOfOne (S := k) y) (fun _ => n) := by
    rw [NumbersDVR.gradedPiece, LinearMap.range_comp, Submodule.range_subtype]
  have hr₂ : LinearMap.range f₂ = (coordGraded k y).piece (n : ℤ) := by
    apply le_antisymm
    · rintro _ ⟨⟨v, hv⟩, rfl⟩
      refine Submodule.subset_span ⟨oneBlock (S := k) (N := N) v, n, hhom v hv, rfl, ?_⟩
      exact (heval v).symm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, e, hg, he, rfl⟩
      have he' : e = n := by exact_mod_cast he
      subst he'
      refine ⟨⟨rename (blockEquiv N).symm g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        ((isWeightedHomogeneous_iff _ e).mpr (hg.rename_isHomogeneous))⟩, ?_⟩
      change aeval (fun v : Σ _ : Unit, Fin (N + 1) => y v.2) (rename (blockEquiv N).symm g) = aeval y g
      rw [aeval_rename]
      rfl
  have hker : LinearMap.ker f₁ = LinearMap.ker f₂ := by
    ext ⟨v, hv⟩
    simp only [LinearMap.mem_ker, f₁, f₂, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    change oneBlock (S := k) (N := N) v ∈ primeOf (S := k) y ↔ _
    rw [mem_primeOf_of_isHomogeneous y (hhom v hv), heval]
  have e₁ := ((f₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
    f₂.quotKerEquivRange).finrank_eq
  rw [hr₁, hr₂] at e₁
  exact e₁.symm

end HilbertPositive

open HilbertPositive in

theorem HilbertPositive.proof (hPos : ProjDegreePositive.Statement.{u})
    (hSec : TwistSections.Statement.{u, w}) : HilbertPositive.Statement.{u, w} := by
  intro k _ Ω _ _ N y e he hW
  have hy : y ≠ 0 := ne_zero_of_isSubvar hW
  have hq : NumbersDVR.IsMultiProjPrime (primeOfOne (S := k) y) := isMultiProjPrime_primeOfOne y hy
  have hdim : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim_primeOfOne]
    exact hW.dim
  refine ⟨?_, hPos k (Fin (N + 1)) _ e hq hdim, hSec k Ω N y hy⟩
  have hdim' : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ((e + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    simpa using hdim
  obtain ⟨a₀, C, hC⟩ := hilbertPrime e k Unit (fun _ => Fin (N + 1)) _ hq hdim'
  have hadd := (mixedNumber k Unit (fun _ => Fin (N + 1)) _ e hq hdim').2
  have hhom : ∀ n : ℕ, NumbersDVR.intNum k (primeOfOne (S := k) y)
      (fun _ : Fin e => fun _ : Unit => (n : ℤ)) = (n : ℤ) ^ e *
        NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) := by
    intro n
    have := HilbertSamuel.RankOfSections.const_nsmul
      (fun bs => NumbersDVR.intNum k (primeOfOne (S := k) y) bs) hadd n (fun _ : Unit => (1 : ℤ))
    have e' : (n • fun _ : Unit => (1 : ℤ)) = fun _ : Unit => (n : ℤ) := by
      funext u
      simp
    rw [e'] at this
    exact this
  refine ⟨|C| * 2 ^ (e - 1), ?_⟩
  filter_upwards [eventually_ge_atTop (max a₀ 1)] with n hn
  have h := hC (fun _ => n) (fun _ => le_of_max_le_left hn)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  rw [hhom n, ← finrank_piece_eq_hilbFn] at h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hpow : ((n : ℝ) + 1) ^ ((e : ℝ) - 1) ≤ 2 ^ (e - 1) * (n : ℝ) ^ (e - 1) := by
    rw [show (e : ℝ) - 1 = ((e - 1 : ℕ) : ℝ) by rw [Nat.cast_sub he]; simp, Real.rpow_natCast,
      ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc |(Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℝ) -
        (NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℝ) *
          (n : ℝ) ^ e / (e.factorial : ℝ)|
      = |(((Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℤ)) : ℝ) -
          (((n : ℤ) ^ e * NumbersDVR.intNum k (primeOfOne (S := k) y)
            (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℤ) : ℝ) / (e.factorial : ℝ)| := by
        push_cast
        ring_nf
    _ ≤ C * ((n : ℝ) + 1) ^ ((e : ℝ) - 1) := h
    _ ≤ |C| * ((n : ℝ) + 1) ^ ((e : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 ^ (e - 1) * (n : ℝ) ^ (e - 1)) := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    _ = |C| * 2 ^ (e - 1) * (n : ℝ) ^ (e - 1) := by ring

end

end GroundTheory.Heights₂.Heights.Kleiman
