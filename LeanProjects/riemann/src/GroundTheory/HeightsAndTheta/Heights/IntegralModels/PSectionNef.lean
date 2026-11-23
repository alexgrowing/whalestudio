import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PColonMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open MvPolynomial NumbersDVR

noncomputable section

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type} [Field F]

theorem exists_forms_mem_of_not_le_relevant {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J)
    (hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W → ¬ J ≤ W) :
    ∃ n : ℕ, ∀ m : K → ℕ, (∀ k, n * Fintype.card (ι k) < m k) →
      ∀ x : MRing ι F, IsMultiHomog x m → x ∈ J := by
  classical

  let e : (∀ k, ι k) → (Σ k, ι k) →₀ ℕ := fun σ =>
    Finsupp.equivFunOnFinite.symm (fun v => if v.2 = σ v.1 then 1 else 0)
  have he : ∀ σ v, e σ v = if v.2 = σ v.1 then 1 else 0 := fun σ v => rfl
  have hrad : ∀ σ : (∀ k, ι k), (monomial (e σ) (1 : F)) ∈ J.radical := by
    intro σ
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro W hW
    have hWp : Ideal.IsPrime W := hW.1.1
    have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof F K ι J W hJ hW
    obtain ⟨k, hk⟩ : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ W := by
      by_contra h
      push Not at h
      exact hrel W hWp hWh h hW.1.2
    refine Ideal.mem_of_dvd _ ?_ (hk (σ k))
    rw [← pow_one (X _), X_pow_eq_monomial, monomial_dvd_monomial]
    refine ⟨Or.inr ?_, one_dvd _⟩
    rw [Finsupp.single_le_iff, he]
    simp
  have hrad' : ∀ σ : (∀ k, ι k), ∃ n : ℕ, (monomial (e σ) (1 : F)) ^ n ∈ J := fun σ => hrad σ
  choose N hN using hrad'
  refine ⟨Finset.univ.sup N, fun m hm x hx => ?_⟩
  rw [x.as_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hw := hx (mem_support_iff.mp hd)
  rw [Bridge.weight_blockWeight] at hw
  have hσ : ∀ k, ∃ i : ι k, Finset.univ.sup N ≤ d ⟨k, i⟩ := by
    intro k
    by_contra h
    push Not at h
    have h1 : ∑ i, d ⟨k, i⟩ ≤ ∑ _i : ι k, Finset.univ.sup N :=
      Finset.sum_le_sum fun i _ => (h i).le
    have h2 := congrFun hw k
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1 h2
    have h3 := hm k
    rw [h2] at h1
    rw [mul_comm] at h3
    omega
  choose σ hσ using hσ
  have hmem : monomial (e σ) (1 : F) ^ Finset.univ.sup N ∈ J :=
    Ideal.pow_mem_of_pow_mem _ (hN σ) (Finset.le_sup (Finset.mem_univ σ))
  refine Ideal.mem_of_dvd _ ?_ hmem
  rw [monomial_pow, one_pow, monomial_dvd_monomial]
  refine ⟨Or.inr ?_, one_dvd _⟩
  intro v
  rw [Finsupp.smul_apply, he, smul_eq_mul]
  split_ifs with hv
  · obtain ⟨k, i⟩ := v
    simp only at hv
    subst hv
    simpa using hσ k
  · simp

theorem hilbFn_sub_le_of_regular {P : Ideal (MRing ι F)} (hP : IsMultiProjPrime P) {b : K → ℤ}
    {f g : MRing ι F} (hs : IsRegularSection P b f g) :
    ∀ᶠ m in Filter.atTop, hilbFn P (m - b) ≤ hilbFn P m := by
  classical
  have := hP.isPrime
  obtain ⟨bf, bg, hf, hg, hb⟩ := hs.degrees
  set J : Ideal (MRing ι F) := (P ⊔ Ideal.span {g}).colon {f} with hJdef
  have hJh : IsMultiHomogIdeal J :=
    ColonMultiHomog.proof F K ι _ f bf
      (SupSpanMultiHomog.proof F K ι P g bg hP.multiHomog hg) hf
  have hPJ : P ≤ J := fun p hp => by
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul]
    exact Ideal.mem_sup_left (P.mul_mem_right f hp)
  have hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W →
      ¬ J ≤ W := by
    intro W hWp hWh hWr hJW
    obtain ⟨u, v, hu, huv⟩ := hs.regular W ⟨hWp, hWh, hWr⟩ (hPJ.trans hJW)
    apply hu
    apply hJW
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul]
    have : u * f = (u * f - v * g) + v * g := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left huv)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  obtain ⟨n, hn⟩ := exists_forms_mem_of_not_le_relevant hJh hrel
  rw [Filter.eventually_atTop]
  refine ⟨fun k => |b k| + (n * Fintype.card (ι k) : ℕ) + 1, fun m hm => ?_⟩
  have hm' : ∀ k, |b k| + (n * Fintype.card (ι k) : ℕ) + 1 ≤ m k := fun k => hm k
  have hb' : ∀ k, b k = (bf k : ℤ) - bg k := fun k => (congrFun hb k).symm
  have hm0 : ∀ k, 0 ≤ m k := fun k => by have := hm' k; have := abs_nonneg (b k); omega
  have hmb0 : ∀ k, 0 ≤ (m - b) k := fun k => by
    have := hm' k; have := le_abs_self (b k); simp only [Pi.sub_apply]; omega
  set M : K → ℕ := fun k => (m k).toNat with hM
  set M' : K → ℕ := fun k => ((m - b) k).toNat with hM'
  have hdeg : M' + bf = M + bg := by
    funext k
    have := hm0 k; have := hmb0 k; have := hb' k
    simp only [Pi.add_apply, hM, hM', Pi.sub_apply] at *
    omega
  have hbig : ∀ k, n * Fintype.card (ι k) < M' k := by
    intro k
    have := hm' k; have := le_abs_self (b k)
    simp only [hM', Pi.sub_apply]
    omega
  have hfin := (FieldNumbers.GradedFinite.proof F K ι P M).1
  have hfin' := (FieldNumbers.GradedFinite.proof F K ι P M').1
  have e1 : hilbFn P m = Module.finrank F (gradedPiece P M) := by
    unfold hilbFn; rw [if_pos hm0]
  have e2 : hilbFn P (m - b) = Module.finrank F (gradedPiece P M') := by
    unfold hilbFn; rw [if_pos hmb0]
  rw [e1, e2, Nat.cast_le]

  let φ : MRing ι F → (MRing ι F ⧸ P) →ₗ[F] (MRing ι F ⧸ P) := fun a =>
    LinearMap.mulLeft F (Ideal.Quotient.mk P a)
  have hinj : ∀ a, a ∉ P → Function.Injective (φ a) := by
    intro a ha
    exact mul_right_injective₀ (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hle : (gradedPiece P M').map (φ f) ≤ (gradedPiece P M).map (φ g) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxh : IsMultiHomog x M' := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hx
    have hxJ : x ∈ J := hn M' hbig x hxh
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_sup] at hxJ
    obtain ⟨p, hp, q, hq, hpq⟩ := hxJ
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    set y := weightedHomogeneousComponent (blockWeight ι) M a
    have hxf : IsMultiHomog (x * f) (M + bg) := by
      rw [← hdeg]; exact hxh.mul hf
    have hcomp := congrArg (weightedHomogeneousComponent (blockWeight ι) (M + bg)) hpq
    rw [map_add, ← component_mul_multiHomog a g M bg hg,
      hxf.weightedHomogeneousComponent_same] at hcomp
    have hpc : weightedHomogeneousComponent (blockWeight ι) (M + bg) p ∈ P :=
      hP.multiHomog p hp _
    refine ⟨Ideal.Quotient.mk P y, ⟨y, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      rfl⟩, ?_⟩
    simp only [φ, LinearMap.mulLeft_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.toLinearMap_apply,
      ← map_mul]
    rw [Ideal.Quotient.eq, mul_comm f x, ← hcomp]
    have : g * y - (weightedHomogeneousComponent (blockWeight ι) (M + bg) p + y * g) =
      -weightedHomogeneousComponent (blockWeight ι) (M + bg) p := by ring
    rw [this]
    exact P.neg_mem hpc
  calc Module.finrank F (gradedPiece P M')
      = Module.finrank F ((gradedPiece P M').map (φ f)) :=
        (Submodule.equivMapOfInjective _ (hinj f hs.num_not_mem) _).finrank_eq
    _ ≤ Module.finrank F ((gradedPiece P M).map (φ g)) := by
        have : FiniteDimensional F ((gradedPiece P M).map (φ g)) :=
          Module.Finite.map _ _
        exact LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
          (Submodule.inclusion_injective hle)
    _ = Module.finrank F (gradedPiece P M) :=
        ((Submodule.equivMapOfInjective _ (hinj g hs.den_not_mem) _).finrank_eq).symm

end

theorem SectionNef.proof : SectionNef.Statement := by
  intro K _ _ ι _ F _ P hP _ b f g hs
  have hev := hilbFn_sub_le_of_regular hP hs
  unfold intNum eventualValue
  split_ifs with h
  · obtain ⟨m, hm1, hm2⟩ := (h.choose_spec.and hev).exists
    rw [← hm1]
    simp only [mixedDiff, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
      Matrix.cons_val_zero, diffStep]
    linarith
  · exact le_rfl

theorem SectionNefGenerated.proof : SectionNefGenerated.Statement :=
  SectionNefGenerated.of_sectionNef SectionNef.proof

end

end GroundTheory.Heights₂.Heights.Model
