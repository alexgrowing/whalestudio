import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

namespace ConeMatch

variable {V : Type} [AddCommGroup V] [Module ℝ V]

theorem coef_eq {n : ℕ} {P : Fin n → V} (hP : LinearIndependent ℝ P) {a b : Fin n → ℝ}
    (h : ∑ i, a i • P i = ∑ i, b i • P i) : a = b := by
  have := Fintype.linearIndependent_iff.1 hP (a - b) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext i; exact sub_eq_zero.1 (this i)

theorem exists_pos_of_sum_eq_one {n : ℕ} (f : Fin n → ℝ) (h : ∑ i, f i = 1) : ∃ i, 0 < f i := by
  by_contra hc
  push_neg at hc
  have : ∑ i, f i ≤ 0 := Finset.sum_nonpos fun i _ => hc i
  linarith

theorem match_vec {k m : ℕ} (P : Fin k → V) (Q : Fin m → V) (hP : LinearIndependent ℝ P)
    (hQ : LinearIndependent ℝ Q) (t : Fin k → ℝ) (c : Fin m → ℝ) (ht : ∀ i, 0 < t i) (hc : ∀ j, 0 ≤ c j)
    (hsum : ∑ i, t i • P i = ∑ j, c j • Q j)
    (hPQ : ∀ i, ∃ a : Fin m → ℝ, (∀ j, 0 ≤ a j) ∧ P i = ∑ j, a j • Q j)
    (hQP : ∀ j, 0 < c j → ∃ b : Fin k → ℝ, (∀ l, 0 ≤ b l) ∧ Q j = ∑ l, b l • P l) :
    (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ P i = d • Q j) ∧
    (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ P i = d • Q j ∧ c j = t i * d) := by
  choose D hD0 hD using hPQ
  have hQP' : ∀ j, ∃ b : Fin k → ℝ, (∀ l, 0 ≤ b l) ∧ (0 < c j → Q j = ∑ l, b l • P l) := fun j => by
    by_cases h : 0 < c j
    · obtain ⟨b, hb, e⟩ := hQP j h
      exact ⟨b, hb, fun _ => e⟩
    · exact ⟨0, fun _ => le_rfl, fun h' => absurd h' h⟩
  choose E hE0 hE using hQP'

  have hcD : ∀ j, c j = ∑ i, t i * D i j := by
    have h1 : ∑ j, c j • Q j = ∑ j, (∑ i, t i * D i j) • Q j := by
      rw [← hsum]
      simp only [hD, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact congrFun (coef_eq hQ h1)
  have hDz : ∀ i j, ¬ 0 < c j → D i j = 0 := fun i j h => by
    have h0 : c j = 0 := le_antisymm (not_lt.1 h) (hc j)
    rw [hcD j] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (ht i).le (hD0 i j)).1 h0 i
      (Finset.mem_univ _)
    exact (mul_eq_zero.1 this).resolve_left (ht i).ne'
  have hDQ : ∀ i j, D i j • Q j = D i j • ∑ l, E j l • P l := fun i j => by
    by_cases h : 0 < c j
    · rw [← hE j h]
    · simp [hDz i j h]
  have hDE : ∀ i l, ∑ j, D i j * E j l = if i = l then 1 else 0 := by
    intro i l
    have h1 : ∑ l, (if i = l then (1 : ℝ) else 0) • P l = ∑ l, (∑ j, D i j * E j l) • P l := by
      rw [show ∑ l, (if i = l then (1 : ℝ) else 0) • P l = P i by simp [ite_smul]]
      conv_lhs => rw [hD i]
      simp only [hDQ, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact (congrFun (coef_eq hP h1) l).symm
  have hED : ∀ j, 0 < c j → ∀ j', ∑ l, E j l * D l j' = if j = j' then 1 else 0 := by
    intro j hj j'
    have h1 : ∑ j', (if j = j' then (1 : ℝ) else 0) • Q j' = ∑ j', (∑ l, E j l * D l j') • Q j' := by
      rw [show ∑ j', (if j = j' then (1 : ℝ) else 0) • Q j' = Q j by simp [ite_smul]]
      conv_lhs => rw [hE j hj]
      simp only [hD, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact (congrFun (coef_eq hQ h1) j').symm
  have single : ∀ i j, 0 < D i j * E j i → 0 < c j ∧ 0 < D i j ∧ P i = D i j • Q j := by
    intro i j hpos
    have hcj : 0 < c j := by
      by_contra h
      rw [hDz i j h, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hEne : E j i ≠ 0 := fun h => by rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
    have hDpos : 0 < D i j := lt_of_le_of_ne (hD0 i j) fun h => by rw [← h, zero_mul] at hpos; exact lt_irrefl _ hpos
    have hoff : ∀ j', j' ≠ j → D i j' = 0 := fun j' hj' => by
      have hle : E j i * D i j' ≤ ∑ l, E j l * D l j' :=
        Finset.single_le_sum (f := fun l => E j l * D l j') (fun l _ => mul_nonneg (hE0 j l) (hD0 l j'))
          (Finset.mem_univ i)
      rw [hED j hcj j', if_neg (Ne.symm hj')] at hle
      have h0 : E j i * D i j' = 0 := le_antisymm hle (mul_nonneg (hE0 j i) (hD0 i j'))
      exact (mul_eq_zero.1 h0).resolve_left hEne
    refine ⟨hcj, hDpos, ?_⟩
    rw [hD i, Finset.sum_eq_single j (fun j' _ hj' => by rw [hoff j' hj', zero_smul])
      (fun h => absurd (Finset.mem_univ j) h)]
  refine ⟨fun i => ?_, fun j hj => ?_⟩
  · obtain ⟨j, hj⟩ := exists_pos_of_sum_eq_one _ ((hDE i i).trans (if_pos rfl))
    obtain ⟨hcj, hd, e⟩ := single i j hj
    exact ⟨j, hcj, D i j, hd, e⟩
  · obtain ⟨l, hl⟩ := exists_pos_of_sum_eq_one _ ((hED j hj j).trans (if_pos rfl))
    have hl' : 0 < D l j * E j l := by rw [mul_comm]; exact hl
    obtain ⟨-, hd, e⟩ := single l j hl'
    have hEne : E j l ≠ 0 := fun h => by rw [h, zero_mul] at hl; exact lt_irrefl _ hl
    have hoff : ∀ i, i ≠ l → D i j = 0 := fun i hi => by
      have hle : D i j * E j l ≤ ∑ j'', D i j'' * E j'' l :=
        Finset.single_le_sum (f := fun j'' => D i j'' * E j'' l) (fun j'' _ => mul_nonneg (hD0 i j'') (hE0 j'' l))
          (Finset.mem_univ j)
      rw [hDE i l, if_neg hi] at hle
      have h0 : D i j * E j l = 0 := le_antisymm hle (mul_nonneg (hD0 i j) (hE0 j l))
      exact (mul_eq_zero.1 h0).resolve_right hEne
    refine ⟨l, D l j, hd, e, ?_⟩
    rw [hcD j, Finset.sum_eq_single l (fun i _ hi => by rw [hoff i hi, mul_zero])
      (fun h => absurd (Finset.mem_univ l) h)]

end ConeMatch

section Forms

variable {X : Type} [AddCommGroup X]

theorem linearIndependent_toReal {n : ℕ} {p : Fin n → LinearMap.BilinForm ℤ X} (hp : LinearIndependent ℤ p) :
    LinearIndependent ℝ fun i => toReal (p i) := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  have hind : ∀ (d : Fin 0 → ℤ) (c : Fin n → ℤ), ∑ j, c j • p j = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) →
      c = 0 := fun d c h => by
    funext i
    exact Fintype.linearIndependent_iff.1 hp c (by simpa using h) i
  have := eq_zero_of_toReal_rel (u := p) (v := (Fin.elim0 : Fin 0 → LinearMap.BilinForm ℤ X)) hind
    (r := g) (s := 0) (by simpa using hg)
  exact fun i => congrFun this i

theorem cone_match_rays {X : Type} [AddCommGroup X] {k m : ℕ} (p : Fin k → LinearMap.BilinForm ℤ X)
    (δ : Fin m → LinearMap.BilinForm ℤ X) :
    LinearIndependent ℤ p → LinearIndependent ℤ δ →
    ∀ (t : Fin k → ℝ) (c : Fin m → ℝ), (∀ i, 0 < t i) → (∀ j, 0 ≤ c j) →
      ∑ i, t i • toReal (p i) = ∑ j, c j • toReal (δ j) →
      (∀ i, InRCone δ (p i)) → (∀ j, 0 < c j → InRCone p (δ j)) →
      (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
      (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) :=
  fun hp hδ t c ht hc hsum hpδ hδp =>
    ConeMatch.match_vec (fun i => toReal (p i)) (fun j => toReal (δ j)) (linearIndependent_toReal hp)
      (linearIndependent_toReal hδ) t c ht hc hsum hpδ hδp

end Forms

end GlobalTheory.PolFan
