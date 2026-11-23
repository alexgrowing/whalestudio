import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsClosedPointChartField
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsClosedPointConeCoord
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIntChowFormExists
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormIrreducible
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial Vertical Vertical.NormFormIrreducible

theorem aeval_smul_of_isHomogeneous {F K : Type*} [Field F] [Field K] [Algebra F K] {n d : ℕ}
    {g : MvPolynomial (Fin n) F} (hg : g.IsHomogeneous d) (c : K) (y : Fin n → K) :
    aeval (fun j => c * y j) g = c ^ d * aeval y g := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have := hg (mem_support_iff.mp hm)
    rw [Finsupp.weight_apply, Finsupp.sum] at this
    simpa using this
  rw [aeval_monomial, aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul, Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem ChowDegreeClosedPoint.proof (hField : ClosedPointChartField.Statement)
    (hCone : ClosedPointConeCoord.Statement) : ChowDegreeClosedPoint.Statement := by
  classical
  intro F _ _ n I i hI hdim hXi
  obtain ⟨hfield, hfin⟩ := hField F n I i hI hdim hXi
  set J : Ideal (MvPolynomial (Fin n) F) := I ⊔ Ideal.span {X i - 1} with hJ
  let _ : Field (MvPolynomial (Fin n) F ⧸ J) := hfield.toField
  let L := MvPolynomial (Fin n) F ⧸ J
  have _ : FiniteDimensional F L := hfin
  have _ : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  let K := AlgebraicClosure F
  let ξ : Fin n → L := fun j => Ideal.Quotient.mk J (X j)
  have hξ : ∀ g : MvPolynomial (Fin n) F, aeval ξ g = Ideal.Quotient.mk J g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp; rfl
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | mul_X p j hp => rw [map_mul, map_mul, hp, aeval_X]
  have hξi : ξ i = 1 := by
    have : X i - 1 ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  set t : Fin n → F := Pi.single i 1 with ht_def
  have ht : ∑ j, algebraMap F L (t j) * ξ j = 1 := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [ht_def, hj])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [ht_def, hξi]
  have hgen : Algebra.adjoin F (Set.range ξ) = ⊤ := by
    have hr : Set.range ξ = Ideal.Quotient.mkₐ F J '' Set.range X := by
      rw [← Set.range_comp]; rfl
    rw [hr, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective F J

  obtain ⟨f, hf⟩ := chowFormExists F n 1 I hI hdim
  have hhom : IsMultiHomog (chowDegree I 1) f := chowFormHomog F n 1 I f hf
  have hfH : f.IsHomogeneous (chowDegree I 1) := by
    intro m hm
    have h := congrFun (hhom hm) 0
    rw [← h, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq0 : q.1 = 0 := Subsingleton.elim _ _
    simp [groupWeight, hq0]
  let ι : Fin n → Fin 1 × Fin n := fun j => (0, j)
  have hsnd : ∀ p : MvPolynomial (Fin 1 × Fin n) F, rename ι (rename Prod.snd p) = p := by
    intro p
    rw [rename_rename]
    convert rename_id_apply p
    funext q
    exact Prod.ext (Subsingleton.elim _ _) rfl
  set f₀ := rename Prod.snd f with hf₀
  set N : MvPolynomial (Fin n) F := normForm (R := F) L ξ with hN
  have hprod : N.map (algebraMap F K) = ∏ σ : L →ₐ[F] K, embForm σ ξ := normForm_map_eq_prod ξ

  have hdvd1 : f ∣ rename ι N := by
    refine (hf.2 _).1 fun u hu => ?_
    obtain ⟨y, hy0, hyI, hyu⟩ := hu
    have hyi : y i ≠ 0 := hCone F n I i hI hdim hXi K y hy0 hyI
    let ys : Fin n → K := fun j => (y i)⁻¹ * y j
    have hker : J ≤ RingHom.ker (aeval (R := F) ys).toRingHom := by
      refine sup_le (fun g hg => ?_) ((Ideal.span_le).mpr ?_)
      · rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          ← sum_homogeneousComponent g, map_sum]
        refine Finset.sum_eq_zero fun d _ => ?_
        rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d g),
          hyI _ (hI.isHomog g hg d), mul_zero]
      · rintro _ rfl
        simp [ys, hyi]
    let σ : L →ₐ[F] K := Ideal.Quotient.liftₐ J (aeval ys) fun g hg => hker hg
    have hσ : ∀ j, σ (ξ j) = ys j := fun j =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp [ys])
    rw [aeval_rename, aeval_def, ← eval_map, hprod, eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ σ) ?_
    rw [eval_embForm]
    simp only [hσ, ys, Function.comp_apply, ι]
    have := hyu 0
    calc ∑ j, u (0, j) * ((y i)⁻¹ * y j) = (y i)⁻¹ * ∑ j, u (0, j) * y j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this, mul_zero]

  have hdvd2 : ∀ σ : L →ₐ[F] K, embForm σ ξ ∣ f₀.map (algebraMap F K) := by
    intro σ
    have hprime : Prime (embForm σ ξ) := (irreducible_embForm σ ht).prime
    have hspan : (Ideal.span {embForm σ ξ}).IsPrime :=
      (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
    rw [← Ideal.mem_span_singleton, ← hspan.radical,
      ← vanishingIdeal_zeroLocus_eq_radical (K := K), mem_vanishingIdeal_iff]
    intro u hu
    have hu0 : ∑ j, u j * σ (ξ j) = 0 := by
      have := hu _ (Ideal.mem_span_singleton_self _)
      rwa [aeval_eq_eval, eval_embForm] at this
    rw [aeval_eq_eval, eval_map, ← aeval_def, hf₀, aeval_rename]
    refine (hf.2 f).2 dvd_rfl _ ⟨fun j => σ (ξ j), fun h => ?_, fun g hg => ?_, fun k => ?_⟩
    · have := congrFun h i
      simp [hξi] at this
    · rw [← comp_aeval_apply, hξ, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hg),
        map_zero]
    · rw [Subsingleton.elim k 0]
      simpa using hu0
  have hdvd3 : N.map (algebraMap F K) ∣ f₀.map (algebraMap F K) := by
    rw [hprod]; exact prod_embForm_dvd hgen ht hdvd2
  have hdvd4 : f₀ ∣ N := by
    have := map_dvd (rename Prod.snd) hdvd1
    rwa [rename_rename, show Prod.snd ∘ ι = id from rfl, rename_id_apply] at this

  have hf0 : f₀ ≠ 0 := fun h => hf.1 (by rw [← hsnd f, ← hf₀, h, map_zero])
  have hmap0 : f₀.map (algebraMap F K) ≠ 0 :=
    fun h => hf0 (map_injective _ (algebraMap F K).injective (by rw [h, map_zero]))
  obtain ⟨h, hh⟩ := hdvd4
  obtain ⟨q, hq⟩ := hdvd3
  have hq1 : q * h.map (algebraMap F K) = 1 := by
    apply mul_left_cancel₀ hmap0
    calc f₀.map (algebraMap F K) * (q * h.map (algebraMap F K))
        = (f₀.map (algebraMap F K) * h.map (algebraMap F K)) * q := by ring
      _ = N.map (algebraMap F K) * q := by rw [hh, map_mul]
      _ = f₀.map (algebraMap F K) * 1 := by rw [← hq, mul_one]
  obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp (isUnit_iff_exists_inv.mpr ⟨_, hq1⟩)
  have hlin : ∀ σ : L →ₐ[F] K, (embForm σ ξ).IsHomogeneous 1 := fun σ =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_X K j).mul (isHomogeneous_C _ (σ (ξ j)))
  have h1 : (f₀.map (algebraMap F K)).IsHomogeneous (∑ _σ : L →ₐ[F] K, 1 + 0) := by
    rw [hq, hprod, hc]
    exact (IsHomogeneous.prod _ _ _ fun σ _ => hlin σ).mul (isHomogeneous_C _ c)
  have h2 : (f₀.map (algebraMap F K)).IsHomogeneous (chowDegree I 1) :=
    hfH.rename_isHomogeneous.map _
  rw [h2.inj_right h1 hmap0]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, add_zero]
  exact AlgHom.card F L K

end ObjectsChow

end GroundTheory.Heights₂.Heights
