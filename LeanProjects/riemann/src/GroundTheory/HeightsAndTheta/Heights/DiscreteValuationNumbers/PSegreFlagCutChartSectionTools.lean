import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChartSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial GenericProjClosureDivisor

noncomputable section

set_option linter.unusedSectionVars false

namespace SegreFlagCutChartSection

section Component

variable {O : Type} [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ] {K : Type} [DecidableEq K] {ι : K → Type}

def coneWeight (K : Type) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1

theorem coneMap_monomial_isWeightedHomogeneous (z : (Σ k, ι k) → Φ) (d : (Σ k, ι k) →₀ ℕ) (a : O) :
    IsWeightedHomogeneous (coneWeight K) (pointConeMap O z (monomial d a))
      (Finsupp.weight (blockWeight ι) d) := by
  rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
    Finsupp.sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
  exact ((isWeightedHomogeneous_X (R := Φ) (coneWeight K) p.1).C_mul (z p)).pow (d p)

theorem coneMap_component (z : (Σ k, ι k) → Φ) (b : K → ℕ) (f : MRing ι O) :
    weightedHomogeneousComponent (coneWeight K) b (pointConeMap O z f) =
      pointConeMap O z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := coneMap_monomial_isWeightedHomogeneous (K := K) (O := O) z d a
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι O)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]

theorem isMultiHomogIdeal_pointIdeal (z : (Σ k, ι k) → Φ) : IsMultiHomogIdeal (pointIdeal O z) := by
  intro f hf b
  rw [pointIdeal, RingHom.mem_ker] at hf ⊢
  have := coneMap_component (O := O) z b f
  rw [show (pointConeMap O z) f = 0 from hf, map_zero] at this
  exact this.symm

end Component

section Subst

variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  {O : Type} [CommRing O]

theorem bind₁_isMultiHomog_of (Λ : (K₁ → ℕ) →+ (K₂ → ℕ)) (g : (Σ k, ι₁ k) → MRing ι₂ O)
    (hg : ∀ v, IsWeightedHomogeneous (blockWeight ι₂) (g v) (Λ (blockWeight ι₁ v))) {q : MRing ι₁ O}
    {d : K₁ → ℕ} (hq : IsMultiHomog q d) : IsMultiHomog (bind₁ g q) (Λ d) := by
  rw [← q.support_sum_monomial_coeff, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hmd : Finsupp.weight (blockWeight ι₁) m = d := hq (mem_support_iff.mp hm)
  rw [bind₁_monomial]
  have := (isWeightedHomogeneous_C (blockWeight ι₂) (coeff m q)).mul
    (IsWeightedHomogeneous.prod m.support (fun v => g v ^ m v) (fun v => m v • Λ (blockWeight ι₁ v))
      (fun v _ => (hg v).pow (m v)))
  rw [zero_add] at this
  have hΛ : Λ d = ∑ v ∈ m.support, m v • Λ (blockWeight ι₁ v) := by
    rw [← hmd, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [hΛ]
  exact this

theorem bind₁_scale_of (o₀ : K₁) (u : MRing ι₂ O) (h : (Σ k, ι₁ k) → MRing ι₂ O) {q : MRing ι₁ O}
    {d : K₁ → ℕ} (hq : IsMultiHomog q d) :
    bind₁ (fun v => u ^ blockWeight ι₁ v o₀ * h v) q = u ^ d o₀ * bind₁ h q := by
  conv_lhs => rw [← q.support_sum_monomial_coeff]
  conv_rhs => rw [← q.support_sum_monomial_coeff]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : Finsupp.weight (blockWeight ι₁) m = d := hq (mem_support_iff.mp hm)
  have hs : ∑ v ∈ m.support, blockWeight ι₁ v o₀ * m v = d o₀ := by
    rw [← hmd, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [mul_comm]
  rw [bind₁_monomial, bind₁_monomial]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, hs]
  ring

theorem rename_eq_bind₁ {σ τ R : Type*} [CommRing R] (f : σ → τ) (q : MvPolynomial σ R) :
    rename f q = bind₁ (fun p => X (f p)) q := by
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, rename_X, bind₁_X_right]

theorem bind₁_sub_mem_of {σ τ R : Type*} [CommRing R] (I : Ideal (MvPolynomial τ R))
    (g g' : σ → MvPolynomial τ R) (h : ∀ v, g' v - g v ∈ I) (q : MvPolynomial σ R) :
    bind₁ g' q - bind₁ g q ∈ I := by
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact I.add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul, map_mul, bind₁_X_right, bind₁_X_right,
      show bind₁ g' p * g' v - bind₁ g p * g v =
        (bind₁ g' p - bind₁ g p) * g' v + bind₁ g p * (g' v - g v) by ring]
    exact I.add_mem (I.mul_mem_right _ hp) (I.mul_mem_left _ (h v))

end Subst

section Saturate

variable {K₁ K₂ : Type} [Fintype K₁] [DecidableEq K₁] [Fintype K₂] [DecidableEq K₂] {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι₂ k)] {O : Type} [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ]

theorem saturate (j : K₁ ↪ K₂) (o₀ : K₁) (pt : (Σ k, ι₂ k) → Φ) (lam u D : MRing ι₂ O) (nD : ℕ)
    (hD : u ∣ D ^ nD) (e : K₂ → ℕ) (g : (Σ k, ι₂ (j k)) → MRing ι₂ O)
    (hg₁ : ∀ p, p.1 ≠ o₀ → g p = X (FieldNumbers.blockIncl j ι₂ p))
    (hg₂ : ∀ p, p.1 = o₀ → IsWeightedHomogeneous (blockWeight ι₂) (g p) e ∧
      u * X (FieldNumbers.blockIncl j ι₂ p) - g p ∈ Ideal.span {lam})
    (I : Ideal (MRing (fun k => ι₂ (j k)) O)) (hI : IsMultiHomogIdeal I)
    (hvan : ∀ q ∈ I, aeval (fun p => aeval pt (g p)) q = 0) :
    ∀ q ∈ I, ∃ n : ℕ, D ^ n * rename (FieldNumbers.blockIncl j ι₂) q ∈ pointIdeal O pt ⊔ Ideal.span {lam} := by
  classical
  let Λ₁ : K₁ → K₂ → ℕ := fun k => if k = o₀ then e else Pi.single (j k) 1
  let Λ : (K₁ → ℕ) →+ (K₂ → ℕ) :=
    { toFun := fun d => ∑ k, d k • Λ₁ k
      map_zero' := by simp
      map_add' := fun d d' => by simp [add_smul, Finset.sum_add_distrib] }
  have hΛ : ∀ v : Σ k, ι₂ (j k), Λ (blockWeight (fun k => ι₂ (j k)) v) = Λ₁ v.1 := by
    intro v
    simp only [Λ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, blockWeight]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hgh : ∀ v, IsWeightedHomogeneous (blockWeight ι₂) (g v) (Λ (blockWeight _ v)) := by
    intro v
    rw [hΛ]
    by_cases hv : v.1 = o₀
    · simp only [Λ₁, if_pos hv]
      exact (hg₂ v hv).1
    · simp only [Λ₁, if_neg hv]
      rw [hg₁ v hv]
      exact isWeightedHomogeneous_X O (blockWeight ι₂) (FieldNumbers.blockIncl j ι₂ v)
  have hform : ∀ (d : K₁ → ℕ) (q : MRing (fun k => ι₂ (j k)) O), IsMultiHomog q d → q ∈ I →
      u ^ d o₀ * rename (FieldNumbers.blockIncl j ι₂) q ∈ pointIdeal O pt ⊔ Ideal.span {lam} := by
    intro d q hqd hqI
    have h1 : bind₁ g q ∈ pointIdeal O pt := by
      refine mem_of_homog (bind₁_isMultiHomog_of Λ g hgh hqd) ?_
      rw [aeval_bind₁]
      exact hvan q hqI
    have h2 : u ^ d o₀ * rename (FieldNumbers.blockIncl j ι₂) q - bind₁ g q ∈ Ideal.span {lam} := by
      have hr : rename (FieldNumbers.blockIncl j ι₂) q =
          bind₁ (fun p => X (FieldNumbers.blockIncl j ι₂ p)) q := rename_eq_bind₁ _ q
      rw [hr, ← bind₁_scale_of o₀ u _ hqd]
      refine bind₁_sub_mem_of _ g _ (fun v => ?_) q
      by_cases hv : v.1 = o₀
      · have : blockWeight (fun k => ι₂ (j k)) v o₀ = 1 := by simp [blockWeight, hv]
        rw [this, pow_one]
        exact (hg₂ v hv).2
      · have : blockWeight (fun k => ι₂ (j k)) v o₀ = 0 := by
          simp [blockWeight, Ne.symm hv]
        rw [this, pow_zero, one_mul, hg₁ v hv, sub_self]
        exact zero_mem _
    have h3 := Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
    rwa [add_sub_cancel] at h3
  intro q hq
  have hsat : ∀ d, ∃ n : ℕ, D ^ n * rename (FieldNumbers.blockIncl j ι₂)
      (weightedHomogeneousComponent (blockWeight (fun k => ι₂ (j k))) d q) ∈
      pointIdeal O pt ⊔ Ideal.span {lam} := by
    intro d
    have hqd := hform d _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (hI q hq d)
    obtain ⟨r, hr⟩ := hD
    refine ⟨nD * d o₀, ?_⟩
    rw [pow_mul, hr, mul_pow, mul_comm (u ^ d o₀) (r ^ d o₀), mul_assoc]
    exact Ideal.mul_mem_left _ _ hqd
  choose nn hnn using hsat
  obtain ⟨S, hS⟩ : ∃ S : Finset (K₁ → ℕ),
      q = ∑ d ∈ S, weightedHomogeneousComponent (blockWeight (fun k => ι₂ (j k))) d q := by
    have hfin := weightedHomogeneousComponent_finsupp (w := blockWeight (fun k => ι₂ (j k))) q
    refine ⟨hfin.toFinset, ?_⟩
    conv_lhs => rw [← sum_weightedHomogeneousComponent (blockWeight (fun k => ι₂ (j k))) q]
    exact finsum_eq_sum _ hfin
  refine ⟨∑ d ∈ S, nn d, ?_⟩
  rw [hS, map_sum, Finset.mul_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  rw [← Nat.sub_add_cancel (Finset.single_le_sum (f := nn) (fun _ _ => Nat.zero_le _) hd), pow_add,
    mul_assoc]
  exact Ideal.mul_mem_left _ _ (hnn d)

end Saturate

end SegreFlagCutChartSection

end

end GroundTheory.Heights₂.Heights.NumbersDVR
