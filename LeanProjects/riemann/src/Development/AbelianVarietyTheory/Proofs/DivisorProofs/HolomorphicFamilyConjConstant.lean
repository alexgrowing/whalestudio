import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

namespace HolConj

variable {J : Type} [Fintype J] [DecidableEq J] {d : J → ℕ}

def unit (j : J) (p q : Fin (d j)) : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ :=
  Pi.single j (Matrix.single p q 1)

lemma pi_single_mul_ne {R : J → Type} [∀ i, MulZeroClass (R i)] {i j : J} (h : i ≠ j)
    (x : R i) (y : R j) : (Pi.single i x : Π k, R k) * Pi.single j y = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [Pi.single_apply, Ne.symm h]
  · simp [Pi.single_apply, hk]

lemma unit_mul_ne_factor {j j' : J} (h : j ≠ j') (p q : Fin (d j)) (p' q' : Fin (d j')) :
    unit (d := d) j p q * unit j' p' q' = 0 :=
  pi_single_mul_ne h _ _

lemma unit_mul_same (j : J) (p q r : Fin (d j)) :
    unit (d := d) j p q * unit j q r = unit j p r := by
  simp only [unit, ← Pi.single_mul, Matrix.single_mul_single_same, _root_.mul_one]

lemma unit_mul_ne (j : J) (p q p' r : Fin (d j)) (h : q ≠ p') :
    unit (d := d) j p q * unit j p' r = 0 := by
  simp only [unit, ← Pi.single_mul, Matrix.single_mul_single_of_ne _ _ _ _ h, Pi.single_zero]

lemma pi_single_sum {R : J → Type} [∀ i, AddCommMonoid (R i)] {X : Type} (s : Finset X)
    (j : J) (f : X → R j) :
    (Pi.single j (∑ x ∈ s, f x) : Π k, R k) = ∑ x ∈ s, Pi.single j (f x) :=
  map_sum (AddMonoidHom.single R j) f s

lemma sum_unit_diag : ∑ j, ∑ k, unit (d := d) j k k = 1 := by
  simp only [unit]
  have : ∀ j, ∑ k, (Pi.single j (Matrix.single k k (1:ℂ)) : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
      = Pi.single j 1 := by
    intro j
    rw [← Matrix.sum_single_one, pi_single_sum]
  simp only [this]
  exact Finset.univ_sum_single (fun j => (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ))

lemma eq_sum_unit (t : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    t = ∑ j, ∑ p, ∑ q, t j p q • unit j p q := by
  conv_lhs => rw [← Finset.univ_sum_single t]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Matrix.matrix_eq_sum_single (t j)]
  simp only [unit, pi_single_sum, ← Pi.single_smul, Matrix.smul_single, smul_eq_mul, _root_.mul_one]

end HolConj

end GlobalTheory

namespace GlobalTheory

namespace HolConj

variable {J : Type} [Fintype J] [DecidableEq J] {d : J → ℕ} [∀ j, NeZero (d j)]
variable {A : Type} [Ring A] [Algebra ℂ A]

def conjMat (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A) : A :=
  ∑ j, ∑ k, f (unit j k 0) * g (unit j 0 k)

lemma conjMat_self (f : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A) :
    conjMat f f = 1 := by
  simp only [conjMat, ← map_mul, unit_mul_same, ← map_sum, sum_unit_diag, map_one]

lemma conjMat_unit (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A)
    (j' : J) (p q : Fin (d j')) :
    f (unit j' p q) * conjMat f g = conjMat f g * g (unit j' p q) := by
  have hL : f (unit j' p q) * conjMat f g = f (unit j' p 0) * g (unit j' 0 q) := by
    simp only [conjMat, Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_eq_single j']
    · rw [Finset.sum_eq_single q]
      · rw [unit_mul_same]
      · intro k _ hk
        rw [unit_mul_ne _ _ _ _ _ (Ne.symm hk), map_zero, zero_mul]
      · simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [unit_mul_ne_factor (Ne.symm hj), map_zero, zero_mul]
    · simp
  have hR : conjMat f g * g (unit j' p q) = f (unit j' p 0) * g (unit j' 0 q) := by
    simp only [conjMat, Finset.sum_mul, _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_eq_single j']
    · rw [Finset.sum_eq_single p]
      · rw [unit_mul_same]
      · intro k _ hk
        rw [unit_mul_ne _ _ _ _ _ hk, map_zero, mul_zero]
      · simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [unit_mul_ne_factor hj, map_zero, mul_zero]
    · simp
  rw [hL, hR]

lemma conjMat_intertwines (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A)
    (t : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    f t * conjMat f g = conjMat f g * g t := by
  rw [eq_sum_unit t]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    conjMat_unit]

end HolConj

theorem holFamily_conj_const : ∀ (S : Type) [Ring S] [Algebra ℂ S] [FiniteDimensional ℂ S] [IsSemisimpleRing S] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (S →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ)), IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ a, F b a * h b = h b * F b₀ a := by
  intro S _ _ _ _ g m B b₀ F hB hb₀ hF
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ S
  let f : (Fin m → ℂ) →
      ((Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) :=
    fun b => (F b).comp e.symm.toAlgHom
  let h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => HolConj.conjMat (f b) (f b₀)
  have hdiff : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B := by
    intro i j
    simp only [h, f, HolConj.conjMat, Matrix.sum_apply, Matrix.mul_apply, AlgHom.comp_apply]
    refine DifferentiableOn.fun_sum fun _ _ => DifferentiableOn.fun_sum fun _ _ =>
      DifferentiableOn.fun_sum fun _ _ => (hF _ _ _).mul_const _
  have hc : ContinuousOn h B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hdiff i j).continuousOn
  have hdet : ContinuousOn (fun b => (h b).det) B :=
    (continuous_id.matrix_det).comp_continuousOn hc
  have h₀ : h b₀ = 1 := HolConj.conjMat_self _
  refine ⟨B ∩ (fun b => (h b).det) ⁻¹' {0}ᶜ, h,
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, by simp [h₀]⟩,
    Set.inter_subset_left, h₀, fun i j => (hdiff i j).mono Set.inter_subset_left, ?_⟩
  rintro b ⟨-, hb⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hb), fun a => ?_⟩
  have := HolConj.conjMat_intertwines (f b) (f b₀) (e a)
  simpa [f] using this

end GlobalTheory
