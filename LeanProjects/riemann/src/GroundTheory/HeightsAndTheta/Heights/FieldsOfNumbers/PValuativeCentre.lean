import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsValuativeCentre
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Graded

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
  {κ : Type*} [CommRing κ]

def blockSpecial (ρ : MRing ι F →+* κ) : MRing ι F →+* MvPolynomial K κ :=
  eval₂Hom (C.comp (ρ.comp C)) fun v => C (ρ (X v)) * X v.1

theorem blockSpecial_monomial (ρ : MRing ι F →+* κ) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    blockSpecial ρ (monomial d a) = C (ρ (monomial d a)) *
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) 1 := by
  have hT : (monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) (1 : κ)) =
      d.prod fun v n => (X v.1 : MvPolynomial K κ) ^ n := by
    rw [← prod_pow_blockWeight, monomial_eq, C_1, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [hT, blockSpecial, coe_eval₂Hom, eval₂_monomial, monomial_eq, map_mul, map_mul,
    map_finsuppProd, map_finsuppProd]
  simp only [RingHom.comp_apply, mul_pow, map_pow]
  rw [Finsupp.prod_mul, mul_assoc]

theorem coeff_blockSpecial (ρ : MRing ι F →+* κ) (f : MRing ι F) (e : K →₀ ℕ) :
    coeff e (blockSpecial ρ f) = ρ (weightedHomogeneousComponent (blockWeight ι) (⇑e) f) := by
  classical
  conv_lhs => rw [f.as_sum]
  rw [weightedHomogeneousComponent_apply, map_sum, coeff_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [blockSpecial_monomial, coeff_C_mul, coeff_monomial]
  have hiff : Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d) = e ↔
      Finsupp.weight (blockWeight ι) d = ⇑e := by
    rw [Equiv.symm_apply_eq]; rfl
  by_cases h : Finsupp.weight (blockWeight ι) d = ⇑e
  · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]

end Graded

theorem ValuativeCentre.proof : ValuativeCentre.Statement.{u} := by
  intro F _ K _ _ ι _ P hP
  have := hP.isPrime
  intro R hF
  set L := FractionRing (MRing ι F ⧸ P)
  let φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hφ : ∀ p, φ p = 0 ↔ p ∈ P := fun p => by
    simp only [φ, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

  have hmax : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι F) ∉ P ∧
      ∀ j, R.valuation (φ (X ⟨k, j⟩)) ≤ R.valuation (φ (X ⟨k, i⟩)) := by
    intro k
    classical
    obtain ⟨i₀, hi₀⟩ := hP.relevant k
    obtain ⟨i, hi, hmx⟩ := Finset.exists_max_image
      (Finset.univ.filter fun j => (X ⟨k, j⟩ : MRing ι F) ∉ P)
      (fun j => R.valuation (φ (X ⟨k, j⟩))) ⟨i₀, by simp [hi₀]⟩
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun j => ?_⟩
    by_cases hj : (X ⟨k, j⟩ : MRing ι F) ∈ P
    · rw [(hφ _).mpr hj, map_zero]; exact zero_le
    · exact hmx j (by simp [hj])
  choose c hcP hcmax using hmax

  have hchart : ∀ p, chartMap P c p ∈ R := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [chartMap, aeval_C]; exact hF a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [chartMap, aeval_X, ← R.valuation_le_one_iff, map_div₀]
      have h0 : R.valuation (φ (X ⟨v.1, c v.1⟩)) ≠ 0 := by
        rw [Ne, Valuation.zero_iff, hφ]; exact hcP v.1
      exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hcmax v.1 v.2)
  let χ : MRing ι F →+* R := (chartMap P c).toRingHom.codRestrict R hchart
  have hχ : ∀ p, (χ p : L) = chartMap P c p := fun p => rfl
  let ρ : MRing ι F →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp χ
  let θ : MRing ι F →+* MvPolynomial K (IsLocalRing.ResidueField R) := blockSpecial ρ
  have hdeh : ∀ f b, IsMultiHomog f b → chartMap P c f = φ f / φ (chartMonomial c b) :=
    fun f b hf => MChartDehomog.proof F K ι P c hcP f b hf
  have hmon : ∀ b, φ (chartMonomial c b) ≠ 0 := fun b => by
    simp only [chartMonomial, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (fun h => hcP k ((hφ _).mp h))

  have hy : ∀ f, f ∈ RingHom.ker θ ↔
      ∀ b : K → ℕ, ρ (weightedHomogeneousComponent (blockWeight ι) b f) = 0 := by
    intro f
    rw [RingHom.mem_ker]
    constructor
    · intro h b
      have := congrArg (coeff (Finsupp.equivFunOnFinite.symm b)) h
      rwa [coeff_blockSpecial, coeff_zero, Finsupp.coe_equivFunOnFinite_symm] at this
    · intro h
      ext e
      rw [coeff_blockSpecial, coeff_zero, h]
  have hyform : ∀ f b, IsMultiHomog f b → (f ∈ RingHom.ker θ ↔ ρ f = 0) := by
    intro f b hf
    rw [hy]
    constructor
    · intro h
      have := h b
      rwa [IsWeightedHomogeneous.weightedHomogeneousComponent_same hf] at this
    · intro h b'
      by_cases hb : b' = b
      · rw [hb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hf]; exact h
      · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hf hb, map_zero]
  refine ⟨RingHom.ker θ, ⟨RingHom.ker_isPrime θ, ?_, ?_⟩, ?_, ?_⟩
  ·
    intro f hf b
    rw [hy] at hf ⊢
    intro b'
    have hb := weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f
    by_cases hbb : b' = b
    · rw [hbb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hb]; exact hf b
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hb hbb, map_zero]
  ·
    intro k
    refine ⟨c k, fun h => ?_⟩
    have hX := isWeightedHomogeneous_X F (blockWeight ι) (⟨k, c k⟩ : Σ k, ι k)
    rw [hyform _ _ hX] at h
    have h1 : χ (X ⟨k, c k⟩) = 1 := by
      apply Subtype.ext
      rw [hχ, chartMap, aeval_X]
      exact div_self (fun h' => hcP k ((hφ _).mp h'))
    simp only [ρ, RingHom.comp_apply, h1, map_one] at h
    exact one_ne_zero h
  ·
    intro f hf
    rw [hy]
    intro b
    have hb := weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f
    have h0 : χ (weightedHomogeneousComponent (blockWeight ι) b f) = 0 := by
      apply Subtype.ext
      rw [hχ, hdeh _ _ hb, (hφ _).mpr (hP.multiHomog f hf b), zero_div]
      rfl
    simp only [ρ, RingHom.comp_apply, h0, map_zero]
  ·
    intro b f g hf hg hgy
    change φ f / φ g ∈ R ∧ (f ∈ RingHom.ker θ ↔ φ f / φ g ∈ R.nonunits)
    have hgu : IsUnit (χ g) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      exact fun h => hgy ((hyform g b hg).mpr h)
    have hg0 : (χ g : L) ≠ 0 := fun h => hgu.ne_zero (Subtype.ext h)
    have hquot : φ f / φ g = ((χ f * ↑hgu.unit⁻¹ : R) : L) := by
      have e1 : φ f / φ g = (χ f : L) / (χ g : L) := by
        rw [hχ, hχ, hdeh f b hf, hdeh g b hg, div_div_div_cancel_right₀ (hmon b)]
      have e2 : (χ g : L) * ((↑hgu.unit⁻¹ : R) : L) = 1 := by
        rw [← Subring.coe_mul, IsUnit.mul_val_inv]; rfl
      rw [e1, div_eq_iff hg0, Subring.coe_mul, mul_assoc, mul_comm _ (χ g : L), e2, mul_one]
    rw [hquot, ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_mul,
      hyform f b hf]
    refine ⟨Subtype.mem _, ?_⟩
    have hu : IsLocalRing.residue R (↑hgu.unit⁻¹ : R) ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (Units.isUnit _)
    simp only [ρ, RingHom.comp_apply, mul_eq_zero]
    exact ⟨Or.inl, fun h => h.resolve_right hu⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
