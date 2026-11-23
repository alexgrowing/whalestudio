import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeHypersurfaceDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeProjHyperplaneDim
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre)

namespace ConeHypersurfaceDim

theorem finite_of_rel {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Fin m → MvPolynomial (Fin n) ℂ) (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (H : Fin n → Fin m → MvPolynomial (Fin n) ℂ) (hH : ∀ i j, (H i j).totalDegree ≤ r i - 1)
    (hrel : ∀ i, X i ^ r i - ∑ j, L j * H i j ∈ I) :
    RingHom.Finite ((Ideal.Quotient.mk I).comp (aeval (R := ℂ) L).toRingHom) := by
  classical
  let φ : MvPolynomial (Fin m) ℂ →+* (MvPolynomial (Fin n) ℂ ⧸ I) :=
    (Ideal.Quotient.mk I).comp (aeval L).toRingHom
  let instA : Algebra (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := φ.toAlgebra
  let instM : Module (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := instA.toModule
  have hsmul : ∀ (s : MvPolynomial (Fin m) ℂ) (p : MvPolynomial (Fin n) ℂ),
      s • Ideal.Quotient.mk I p = Ideal.Quotient.mk I (aeval L s * p) := by
    intro s p
    rw [Algebra.smul_def]
    rfl
  set M := Submodule.span (MvPolynomial (Fin m) ℂ)
    (((Fintype.piFinset fun i => Finset.range (r i)).image
      (fun α => Ideal.Quotient.mk I (monomial (Finsupp.equivFunOnFinite.symm α) 1))) :
        Set (MvPolynomial (Fin n) ℂ ⧸ I)) with hM
  have hdeg : ∀ N, ∀ β : Fin n →₀ ℕ, (β.sum fun _ e => e) = N →
      Ideal.Quotient.mk I (monomial β 1) ∈ M := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro β hβ
      have hpoly : ∀ q : MvPolynomial (Fin n) ℂ, q.totalDegree < N →
          Ideal.Quotient.mk I q ∈ M := by
        intro q hq
        rw [q.as_sum, map_sum]
        refine Submodule.sum_mem _ fun d hd => ?_
        have hd' : (d.sum fun _ e => e) < N := lt_of_le_of_lt (le_totalDegree hd) hq
        have h1 := ih _ hd' d rfl
        have : Ideal.Quotient.mk I (monomial d (coeff d q)) =
            (C (coeff d q) : MvPolynomial (Fin m) ℂ) • Ideal.Quotient.mk I (monomial d 1) := by
          rw [hsmul, aeval_C, algebraMap_eq, C_mul_monomial, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ h1
      by_cases hsmall : ∀ i, β i < r i
      · apply Submodule.subset_span
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨Finsupp.equivFunOnFinite β, ?_, ?_⟩)
        · exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (hsmall i)
        · simp
      · push Not at hsmall
        obtain ⟨i, hi⟩ := hsmall
        set β' := β - Finsupp.single i (r i) with hβ'
        have hβeq : β = β' + Finsupp.single i (r i) := by
          ext i'
          simp only [hβ', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
          by_cases h : i' = i
          · subst h; simp; omega
          · simp [Ne.symm h]
        have hmk : Ideal.Quotient.mk I (monomial β 1) =
            ∑ j, (X j : MvPolynomial (Fin m) ℂ) •
              Ideal.Quotient.mk I (monomial β' 1 * H i j) := by
          have h1 : monomial β (1 : ℂ) = monomial β' 1 * X i ^ r i := by
            rw [hβeq, X_pow_eq_monomial, monomial_mul, one_mul]
          have h2 : Ideal.Quotient.mk I (X i ^ r i) =
              Ideal.Quotient.mk I (∑ j, L j * H i j) :=
            Ideal.Quotient.eq.mpr (hrel i)
          rw [h1, map_mul, h2, ← map_mul, Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsmul, aeval_X]
          congr 1
          ring
        rw [hmk]
        refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hpoly _ ?_)
        have hβsum : (β.sum fun _ e => e) = (β'.sum fun _ e => e) + r i := by
          rw [hβeq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            Finsupp.sum_single_index rfl]
        calc (monomial β' 1 * H i j).totalDegree
            ≤ (monomial β' (1 : ℂ)).totalDegree + (H i j).totalDegree := totalDegree_mul _ _
          _ ≤ (β'.sum fun _ e => e) + (r i - 1) := by
            rw [totalDegree_monomial _ one_ne_zero]
            exact Nat.add_le_add_left (hH i j) _
          _ < N := by have := hr i; omega
  have hfin : Module.Finite (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := by
    refine ⟨⟨(Fintype.piFinset fun i => Finset.range (r i)).image
      (fun α => Ideal.Quotient.mk I (monomial (Finsupp.equivFunOnFinite.symm α) 1)), ?_⟩⟩
    rw [← hM, eq_top_iff]
    rintro x -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    have : Ideal.Quotient.mk I (monomial d (coeff d p)) =
        (C (coeff d p) : MvPolynomial (Fin m) ℂ) • Ideal.Quotient.mk I (monomial d 1) := by
      rw [hsmul, aeval_C, algebraMap_eq, C_mul_monomial, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (hdeg _ d rfl)
  exact hfin

theorem le_of_add_one_le {x : WithBot ℕ∞} {d : ℕ} (h : x + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    x ≤ ((d : ℕ) : WithBot ℕ∞) := by
  induction x with
  | bot => exact bot_le
  | coe x =>
    have h' : x + 1 ≤ ((d : ℕ∞) + 1) := by exact_mod_cast h
    have : x ≤ (d : ℕ∞) := (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'
    exact_mod_cast this

theorem proof : ConeHypersurfaceDim.Statement := by
  intro n e P Ψ c hP hΨ hc
  classical
  set J := complexFibreIdeal P ⊔ Ideal.span {conePullback Ψ c}
  have hrad : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J.radical) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
  rw [hrad]
  choose r hr H hH hrelP using fun i => ConeProjHyperplaneDim.cone_rel hP hΨ i
  have hfin := finite_of_rel J.radical (ConeProjHyperplaneDim.coneForm Ψ) r hr H hH
    (fun i => Ideal.radical_mono le_sup_left (hrelP i))
  set φ : MvPolynomial (Fin (e + 1)) ℂ →+* (MvPolynomial (Fin n) ℂ ⧸ J.radical) :=
    (Ideal.Quotient.mk J.radical).comp (aeval (ConeProjHyperplaneDim.coneForm Ψ)).toRingHom with hφ
  have hφc : φ c = 0 := by
    show Ideal.Quotient.mk J.radical (conePullback Ψ c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.le_radical (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hker : ∀ a ∈ Ideal.span {c}, φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hφc, mul_zero]
  let ψ := Ideal.Quotient.lift (Ideal.span {c}) φ hker
  have hcomp : ψ.comp (Ideal.Quotient.mk (Ideal.span {c})) = φ :=
    RingHom.ext fun a => by
      rw [RingHom.comp_apply]
      exact Ideal.Quotient.lift_mk _ _ _
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (Ideal.span {c}))
    (hcomp ▸ hfin)
  let := ψ.toAlgebra
  have : Module.Finite (MvPolynomial (Fin (e + 1)) ℂ ⧸ Ideal.span {c})
      (MvPolynomial (Fin n) ℂ ⧸ J.radical) := hψ
  have : Algebra.IsIntegral (MvPolynomial (Fin (e + 1)) ℂ ⧸ Ideal.span {c})
      (MvPolynomial (Fin n) ℂ ⧸ J.radical) := Algebra.IsIntegral.of_finite _ _
  have hS : ringKrullDim (MvPolynomial (Fin (e + 1)) ℂ) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  have hquot := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hc)
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J.radical)
      ≤ ringKrullDim (MvPolynomial (Fin (e + 1)) ℂ ⧸ Ideal.span {c}) :=
        GroundTheory.Arith.Toric.ringKrullDim_le_of_isIntegral
    _ ≤ ((e : ℕ) : WithBot ℕ∞) := le_of_add_one_le (hquot.trans_eq hS)

end ConeHypersurfaceDim

end GroundTheory.Heights₂.Heights
