import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsUnitIffCharpolyCoeffZeroNe
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimaryStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobiusStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement

open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {F : Type} [Field F] [Finite F]

def tor (F : Type) [Field F] [Finite F] (n : ℕ) : Set (AlgebraicClosure F) :=
  {α | α ^ (Nat.card F ^ n - 1) = 1}

theorem N_pos {n : ℕ} (hn : 0 < n) : 0 < Nat.card F ^ n - 1 := by
  have := Nat.one_lt_pow hn.ne' (Finite.one_lt_card (α := F))
  omega

theorem tor_finite {n : ℕ} (hn : 0 < n) : (tor F n).Finite := by
  refine (Polynomial.nthRoots (Nat.card F ^ n - 1) (1 : AlgebraicClosure F)).finite_toSet.subset ?_
  intro α hα
  exact (Polynomial.mem_nthRoots (N_pos hn)).2 hα

def hT (n : ℕ) (ψ : F → ℂ) (β : AlgebraicClosure F) : ℂ :=
  ψ (-((minpoly F β) ^ (n / (minpoly F β).natDegree)).nextCoeff)

def aC (n : ℕ) (θ : AlgebraicClosure F →* ℂ) (h : AlgebraicClosure F → ℂ) (l : ℕ) : ℂ :=
  ((Nat.card F ^ n - 1 : ℕ) : ℂ)⁻¹ * ∑ᶠ β ∈ tor F n, h β * star (θ β ^ l)

theorem theta_pow_N {n : ℕ} (θ : AlgebraicClosure F →* ℂ) {β : AlgebraicClosure F} (hβ : β ∈ tor F n) :
    θ β ^ (Nat.card F ^ n - 1) = 1 := by
  rw [← map_pow, show β ^ (Nat.card F ^ n - 1) = 1 from hβ, map_one]

theorem star_eq_inv_of_pow {c : ℂ} {N : ℕ} (hN : 0 < N) (hc : c ^ N = 1) : star c = c⁻¹ := by
  have h1 : ‖c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hc hN.ne'
  have h0 : c ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hc; exact zero_ne_one hc
  refine eq_inv_of_mul_eq_one_left ?_
  have : star c * c = ((Complex.normSq c : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  rw [this, Complex.normSq_eq_norm_sq, h1]; simp

open scoped Classical in

theorem sum_pow_star {n : ℕ} (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    {β β' : AlgebraicClosure F} (hβ : β ∈ tor F n) (hβ' : β' ∈ tor F n) :
    ∑ l ∈ Finset.range (Nat.card F ^ n - 1), θ β ^ l * star (θ β' ^ l) =
      if β = β' then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by
  have hN := N_pos (F := F) hn
  have e1 := theta_pow_N θ hβ
  have e2 := theta_pow_N θ hβ'
  have h0 : θ β' ≠ 0 := by
    intro h; rw [h, zero_pow hN.ne'] at e2; exact zero_ne_one e2
  have hs : star (θ β') = (θ β')⁻¹ := star_eq_inv_of_pow hN e2
  have hw : ∀ l, θ β ^ l * star (θ β' ^ l) = (θ β * (θ β')⁻¹) ^ l := by
    intro l; rw [star_pow, hs, mul_pow, inv_pow]
  simp_rw [hw]
  have hwN : (θ β * (θ β')⁻¹) ^ (Nat.card F ^ n - 1) = 1 := by
    rw [mul_pow, inv_pow, e1, e2, inv_one, one_mul]
  split_ifs with hb
  · subst hb
    rw [mul_inv_cancel₀ h0]; simp
  · have hne : θ β * (θ β')⁻¹ ≠ 1 := by
      intro h
      have h' : θ β = θ β' := by
        rw [mul_inv_eq_one₀ h0] at h; exact h
      have n0 : ∀ {x : AlgebraicClosure F}, x ∈ tor F n → x ≠ 0 := by
        intro x hx h; rw [h] at hx
        have : (0 : AlgebraicClosure F) ^ (Nat.card F ^ n - 1) = 1 := hx
        rw [zero_pow hN.ne'] at this; exact zero_ne_one this
      exact hb (hθ _ _ (n0 hβ) (n0 hβ') h')
    rw [geom_sum_eq hne, hwN, sub_self, zero_div]

theorem sum_aC {n : ℕ} (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (h : AlgebraicClosure F → ℂ)
    {β : AlgebraicClosure F} (hβ : β ∈ tor F n) :
    ∑ l ∈ Finset.range (Nat.card F ^ n - 1), aC n θ h l * θ β ^ l = h β := by
  classical
  have hT := tor_finite (F := F) hn
  have hN : ((Nat.card F ^ n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (N_pos hn).ne'
  unfold aC
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ hT, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ β' ∈ hT.toFinset, ∑ l ∈ Finset.range (Nat.card F ^ n - 1),
      ((Nat.card F ^ n - 1 : ℕ) : ℂ)⁻¹ * (h β' * star (θ β' ^ l)) * θ β ^ l =
      ((Nat.card F ^ n - 1 : ℕ) : ℂ)⁻¹ * h β' * (if β = β' then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0) := by
    intro β' hb'
    rw [← sum_pow_star hn θ hθ hβ ((Set.Finite.mem_toFinset hT).1 hb'), Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl e]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq hT.toFinset β, if_pos ((Set.Finite.mem_toFinset hT).2 hβ)]
  field_simp

theorem minpoly_pow_card (β : AlgebraicClosure F) (i : ℕ) :
    minpoly F (β ^ Nat.card F ^ i) = minpoly F β := by
  obtain ⟨f, hf⟩ := exists_algHom_pow_card_pow (F := F) i
  rw [← hf]
  exact minpoly.algHom_eq f f.toRingHom.injective β

theorem hT_pow_card (n : ℕ) (ψ : F → ℂ) (β : AlgebraicClosure F) (i : ℕ) :
    hT n ψ (β ^ Nat.card F ^ i) = hT n ψ β := by
  unfold hT; rw [minpoly_pow_card]

theorem pow_mem_tor {n : ℕ} {β : AlgebraicClosure F} (hβ : β ∈ tor F n) (m : ℕ) : β ^ m ∈ tor F n := by
  show (β ^ m) ^ (Nat.card F ^ n - 1) = 1
  rw [← pow_mul, mul_comm, pow_mul, show β ^ (Nat.card F ^ n - 1) = 1 from hβ, one_pow]

theorem expand_primary {n : ℕ} (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (ψ : F → ℂ)
    (P f : F[X]) (m : ℕ) (hf : f.Monic) (hirr : Irreducible f) (hm : 0 < m) (hP : P = f ^ m)
    (hdeg : P.natDegree = n) (h0 : P.coeff 0 ≠ 0) :
    (n : ℂ) * ψ (-P.nextCoeff) =
      ∑ l ∈ Finset.range (Nat.card F ^ n - 1), aC n θ (hT n ψ) l * rootSum θ l P := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure F) f
    (degree_pos_of_irreducible hirr).ne'
  have hmin : f = minpoly F α := minpoly.eq_of_irreducible_of_monic hirr hα hf
  have hd : f.natDegree * m = n := by rw [← hdeg, hP, hf.natDegree_pow, mul_comm]
  have hdpos : 0 < f.natDegree := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)
  have hmq : n / f.natDegree = m := by rw [← hd, Nat.mul_div_cancel_left _ hdpos]
  have hf0 : f.coeff 0 ≠ 0 := by
    intro hc; apply h0
    rw [hP, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, hc, zero_pow hm.ne']
  have hα0 : α ≠ 0 := by
    rintro rfl; apply hf0; rwa [aeval_def, eval₂_at_zero, map_eq_zero_iff _ (algebraMap F _).injective] at hα
  have hαt : α ∈ tor F n := by
    have h1 : α ^ Nat.card F ^ n = α :=
      (minpoly_natDegree_dvd_iff_pow α n).1 (by rw [← hmin, ← hd]; exact Dvd.intro m rfl)
    show α ^ (Nat.card F ^ n - 1) = 1
    have h2 : α ^ (Nat.card F ^ n - 1) * α = α * 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow n (Nat.card F) Nat.card_pos), h1, mul_one]
    exact mul_left_cancel₀ hα0 (by rw [mul_comm] at h2; exact h2)
  have hPα : P = minpoly F α ^ (n / (minpoly F α).natDegree) := by rw [← hmin, hmq, hP]
  have hr := (GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum F θ n hn α hαt).2.2
  have hnc : ψ (-P.nextCoeff) = hT n ψ α := by unfold hT; rw [← hPα]
  rw [hnc, hPα]
  simp_rw [hr, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ i ∈ Finset.range n, ∑ l ∈ Finset.range (Nat.card F ^ n - 1),
      aC n θ (hT n ψ) l * θ (α ^ Nat.card F ^ i) ^ l = hT n ψ α := by
    intro i _
    rw [sum_aC hn θ hθ _ (pow_mem_tor hαt _), hT_pow_card]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end DiscreteGroups.sglob.DzType.Kon
