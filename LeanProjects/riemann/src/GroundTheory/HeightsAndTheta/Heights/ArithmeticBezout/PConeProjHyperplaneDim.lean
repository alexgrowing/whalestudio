import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeProjHyperplaneDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSheetParam
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre mcPts psiPoly)

namespace ConeProjHyperplaneDim

def coneForm {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    MvPolynomial (Fin n) ℂ :=
  rename (fun p : Σ k : Unit, PBlk n k => p.2) (psiPoly Ψ j)

theorem coneForm_zero {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    coneForm Ψ 0 = coneFirstForm Ψ := rfl

theorem eval_coneForm {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (j : Fin (e + 1)) (z : Fin n → ℂ) :
    eval z (coneForm Ψ j) = Ψ (segre fun p : Σ k, PBlk n k => z p.2) j := by
  rw [coneForm, eval_rename]
  exact ReciprocityTheory.ChartRestriction.G.Geo.eval_psiPoly Ψ j _

theorem segre_one_block {n : ℕ} (x : Fin n → ℂ) :
    segre (fun p : Σ k, PBlk n k => x p.2) = fun f => x (f ()) := by
  funext f
  simp [segre]

theorem cone_rel {n e : ℕ} {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hP : IsArithVar P (e + 1))
    (hΨ : IsGoodProj P Ψ) (i : Fin n) :
    ∃ r : ℕ, 0 < r ∧ ∃ H : Fin (e + 1) → MvPolynomial (Fin n) ℂ,
      (∀ j, (H j).totalDegree ≤ r - 1) ∧
      X i ^ r - ∑ j, coneForm Ψ j * H j ∈ (complexFibreIdeal P).radical := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := ReciprocityTheory.ChartRestriction.G.Geo.segre_rel hP.2.1.2.1 Ψ hΨ (fun _ => i)
  refine ⟨r, hr, fun j => rename (fun f : (k : Unit) → PBlk n k => f ()) (G j),
    fun j => (totalDegree_rename_le _ _).trans (hG j), ?_⟩
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
  intro x hx
  have hae : ∀ p : MvPolynomial (Fin n) ℂ, aeval x p = eval x p := fun _ => rfl
  rw [hae]
  have hxP : ∀ q ∈ complexFibreIdeal P, eval x q = 0 := fun q hq => by
    rw [← hae]
    exact hx q hq
  simp only [map_sub, map_pow, eval_X, map_sum, map_mul, eval_coneForm, eval_rename,
    segre_one_block]
  by_cases hx0 : ∃ i0, x i0 ≠ 0
  · obtain ⟨i0, hi0⟩ := hx0
    have hzm : (fun p : Σ k, PBlk n k => x p.2) ∈ mcPts P :=
      ⟨fun _ => ⟨i0, hi0⟩, forall_eval_of_complexFibreIdeal hxP⟩
    have h := hrel _ hzm
    rw [segre_one_block] at h
    rw [sub_eq_zero]
    exact h
  · push Not at hx0
    have hx' : x = 0 := funext hx0
    subst hx'
    have h0 : (fun _ : (k : Unit) → PBlk n k => (0 : ℂ)) = 0 := rfl
    simp only [Pi.zero_apply] at *
    simp [h0, zero_pow hr.ne']

theorem krullDim_le_of_rel {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Fin m → MvPolynomial (Fin n) ℂ) (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (H : Fin n → Fin m → MvPolynomial (Fin n) ℂ) (hH : ∀ i j, (H i j).totalDegree ≤ r i - 1)
    (hrel : ∀ i, X i ^ r i - ∑ j, L j * H i j ∈ I) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ((m : ℕ) : WithBot ℕ∞) := by
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
  have : Module.Finite (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := by
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
  have : Algebra.IsIntegral (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Algebra.IsIntegral.of_finite _ _
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ringKrullDim (MvPolynomial (Fin m) ℂ) :=
        GroundTheory.Arith.Toric.ringKrullDim_le_of_isIntegral
    _ = ((m : ℕ) : WithBot ℕ∞) := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
          Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]

theorem proof : ConeProjHyperplaneDim.Statement := by
  intro n e P Ψ hP hΨ
  classical
  set J := complexFibreIdeal P ⊔ Ideal.span {coneFirstForm Ψ} with hJ
  have hrad : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J.radical) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
  rw [hrad]
  choose r hr H hH hrelP using fun i => cone_rel hP hΨ i
  have h0 : coneForm Ψ 0 ∈ J.radical := by
    rw [coneForm_zero]
    exact Ideal.le_radical (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine krullDim_le_of_rel J.radical (fun j : Fin e => coneForm Ψ j.succ) r hr
    (fun i j => H i j.succ) (fun i j => hH i j.succ) (fun i => ?_)
  have h1 : X i ^ r i - ∑ j, coneForm Ψ j * H i j ∈ J.radical :=
    Ideal.radical_mono le_sup_left (hrelP i)
  rw [Fin.sum_univ_succ] at h1
  have heq : X i ^ r i - ∑ j : Fin e, coneForm Ψ j.succ * H i j.succ =
      (X i ^ r i - (coneForm Ψ 0 * H i 0 + ∑ j : Fin e, coneForm Ψ j.succ * H i j.succ)) +
        coneForm Ψ 0 * H i 0 := by ring
  rw [heq]
  exact add_mem h1 (Ideal.mul_mem_right _ _ h0)

end ConeProjHyperplaneDim

end GroundTheory.Heights₂.Heights
