import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.IsotropicPartner

open scoped ComplexOrder

def hf {n : ℕ} (d : Fin n → ℂ) (x y : Fin n → ℂ) : ℂ := ∑ i, star (x i) * d i * y i

lemma hf_symm {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, star (d i) = d i) (x y : Fin n → ℂ) :
    hf d y x = star (hf d x y) := by
  simp only [hf, star_sum, star_mul', star_star, hd]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma hf_sub {n : ℕ} (d : Fin n → ℂ) (x y u w : Fin n → ℂ) (a b : ℂ) :
    hf d x (fun i => y i - a * u i - b * w i) = hf d x y - a * hf d x u - b * hf d x w := by
  simp only [hf, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_adapted_basis (n : ℕ) (ε : Fin n → Bool) (e : Fin n → ℂ) (he : e ≠ 0)
    (hiso : star e ⬝ᵥ (Jm ε *ᵥ e) = 0) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P ∧ p ≠ q ∧
      P *ᵥ Pi.single p 1 = e ∧ P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ e) ∧
      ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
        (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0 := by
  set d : Fin n → ℂ := fun a => if ε a then 1 else -1 with hd_def
  have hJ : Jm ε = diagonal d := rfl
  have hd : ∀ i, star (d i) = d i := by intro i; simp only [d]; split_ifs <;> simp
  have hd2 : ∀ i, d i * d i = 1 := by intro i; simp only [d]; split_ifs <;> norm_num
  set s : ℂ := ∑ i, star (e i) * e i with hs_def
  have hs : s ≠ 0 := by
    have := (dotProduct_star_self_eq_zero (v := e)).not.mpr he
    exact fun h0 => this h0
  set c : ℂ := s⁻¹ with hc_def
  set e' : Fin n → ℂ := fun i => c * (d i * e i) with he'_def
  have hee : hf d e e = 0 := by
    simpa [hJ, hf, dotProduct, mulVec_diagonal, mul_assoc] using hiso
  have hee' : hf d e e' = 1 := by
    have : hf d e e' = c * s := by
      simp only [hf, e', s, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by linear_combination (c * star (e i) * e i) * hd2 i
    rw [this, hc_def, inv_mul_cancel₀ hs]
  have he'e' : hf d e' e' = 0 := by
    have : hf d e' e' = star c * c * hf d e e := by
      simp only [hf, e', Finset.mul_sum, star_mul', hd]
      exact Finset.sum_congr rfl fun i _ => by
        linear_combination (star c * c * star (e i) * d i * e i) * hd2 i
    rw [this, hee, mul_zero]
  have he'e : hf d e' e = 1 := by rw [hf_symm d hd, hee', star_one]
  obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
    by_contra h; push_neg at h; exact he (funext h)
  set f : Fin n → ℂ := fun i => e' i - (e' p / e p) * e i with hf_def
  obtain ⟨q, hq⟩ : ∃ q, f q ≠ 0 := by
    by_contra h; push_neg at h
    have : hf d e e' = (e' p / e p) * hf d e e := by
      simp only [hf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := h i; simp only [f] at this
      linear_combination (star (e i) * d i) * this
    rw [hee', hee, mul_zero] at this; exact one_ne_zero this
  have hpq : p ≠ q := by
    rintro rfl; apply hq; simp only [f]; field_simp; ring
  let pr : (Fin n → ℂ) → (Fin n → ℂ) := fun y i => y i - hf d e' y * e i - hf d e y * e' i
  have hpre : ∀ y, hf d e (pr y) = 0 := by
    intro y; simp only [pr]; rw [hf_sub, hee, hee']; ring
  have hpre' : ∀ y, hf d e' (pr y) = 0 := by
    intro y; simp only [pr]; rw [hf_sub, he'e, he'e']; ring
  have hpre_l : ∀ y, hf d (pr y) e = 0 := by intro y; rw [hf_symm d hd, hpre, star_zero]
  have hpre'_l : ∀ y, hf d (pr y) e' = 0 := by intro y; rw [hf_symm d hd, hpre', star_zero]
  let col : Fin n → Fin n → ℂ := fun j => if j = p then e else if j = q then e' else pr (Pi.single j 1)
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => col j i
  have hPcol : ∀ j, P *ᵥ Pi.single j 1 = col j := by
    intro j; ext i; simp [P, mulVec_single_one]
  have hgram : ∀ a b, (Pᴴ * Jm ε * P) a b = hf d (col a) (col b) := by
    intro a b
    rw [hJ, Matrix.mul_apply]; simp only [Matrix.mul_diagonal]
    simp [hf, P, Matrix.conjTranspose_apply]
  have hcolp : col p = e := by simp [col]
  have hcolq : col q = e' := by simp [col, hpq.symm]
  have hcolr : ∀ r, r ≠ p → r ≠ q → col r = pr (Pi.single r 1) := by
    intro r h1 h2; simp [col, h1, h2]
  have hGram : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      hf d (col a) (col b) = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0 := by
    intro a b hab
    rcases eq_or_ne a p with rfl | hap
    · rcases eq_or_ne b a with rfl | hba
      · simp [hcolp, hee, hpq]
      rcases eq_or_ne b q with rfl | hbq
      · simp [hcolp, hcolq, hee']
      · simp [hcolp, hcolr b hba hbq, hpre, hba, hbq]
    rcases eq_or_ne a q with rfl | haq
    · rcases eq_or_ne b p with rfl | hbp
      · simp [hcolp, hcolq, he'e]
      rcases eq_or_ne b a with rfl | hbq
      · simp [hcolq, he'e', hap]
      · simp [hcolq, hcolr b hbp hbq, hpre', hbp, hbq]
    · rcases hab with h | h | rfl | rfl
      · exact absurd h hap
      · exact absurd h haq
      · simp [hcolp, hcolr a hap haq, hpre_l, hap, haq]
      · simp [hcolq, hcolr a hap haq, hpre'_l, hap, haq]
  have key : ∀ x v, hf d x (P *ᵥ v) = ∑ j, v j * hf d x (col j) := by
    intro x v
    simp only [hf, mulVec, dotProduct, P, of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hecol : ∀ j, hf d e (col j) = if j = q then 1 else 0 := by
    intro j
    rcases eq_or_ne j p with rfl | hjp
    · simp [hcolp, hee, hpq]
    rcases eq_or_ne j q with rfl | hjq
    · simp [hcolq, hee']
    · simp [hcolr j hjp hjq, hpre, hjq]
  have he'col : ∀ j, hf d e' (col j) = if j = p then 1 else 0 := by
    intro j
    rcases eq_or_ne j p with rfl | hjp
    · simp [hcolp, he'e]
    rcases eq_or_ne j q with rfl | hjq
    · simp [hcolq, he'e', hjp]
    · simp [hcolr j hjp hjq, hpre', hjp]
  have hsingle : ∀ x j, hf d x (Pi.single j 1) = star (x j) * d j := by
    intro x j; simp [hf, Pi.single_apply]
  have h0 : ∀ x, hf d x 0 = 0 := by intro x; simp [hf]
  have hker : ∀ v, P *ᵥ v = 0 → v = 0 := by
    intro v hv
    have hvq : v q = 0 := by
      have := key e v
      rw [hv, h0] at this
      simp only [hecol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    have hvp : v p = 0 := by
      have := key e' v
      rw [hv, h0] at this
      simp only [he'col, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    have hPv : P *ᵥ v = pr v := by
      ext i
      have hterm : ∀ j, col j i * v j = pr (Pi.single j 1) i * v j := by
        intro j
        rcases eq_or_ne j p with rfl | hjp
        · simp [hvp]
        rcases eq_or_ne j q with rfl | hjq
        · simp [hvq]
        rw [hcolr j hjp hjq]
      simp only [mulVec, dotProduct, P, of_apply]
      rw [Finset.sum_congr rfl fun j _ => hterm j]
      simp only [pr, hsingle]
      have h1 : ∑ j, (Pi.single j (1:ℂ) : Fin n → ℂ) i * v j = v i := by simp [Pi.single_apply]
      simp only [sub_mul, Finset.sum_sub_distrib, h1]
      rw [sub_sub, sub_sub]
      congr 1
      simp only [hf, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hPv] at hv
    have hvi : ∀ i, v i = hf d e' v * e i + hf d e v * e' i := by
      intro i; have := congrFun hv i; simp only [pr, Pi.zero_apply] at this
      linear_combination this
    have hp0 : hf d e' v * e p + hf d e v * e' p = 0 := by rw [← hvi p, hvp]
    have hq0 : hf d e' v * e q + hf d e v * e' q = 0 := by rw [← hvi q, hvq]
    have hβ : hf d e v = 0 := by
      have : hf d e v * f q = 0 := by
        simp only [f]; field_simp; linear_combination e p * hq0 - e q * hp0
      exact (mul_eq_zero.mp this).resolve_right hq
    have hα : hf d e' v = 0 := by
      rw [hβ, zero_mul, add_zero] at hp0; exact (mul_eq_zero.mp hp0).resolve_right hp
    ext i; rw [hvi, hα, hβ]; simp
  have hunit : IsUnit P := by
    refine (Matrix.mulVec_injective_iff_isUnit).mp fun v w h => ?_
    have := hker (v - w) (by rw [Matrix.mulVec_sub, h, sub_self])
    exact sub_eq_zero.mp this
  refine ⟨P, p, q, c, hunit, hpq, by rw [hPcol, hcolp], ?_, fun a b hab => by rw [hgram]; exact hGram a b hab⟩
  rw [hPcol, hcolq]; ext i; simp [e', hJ, mulVec_diagonal]

end GlobalTheory.IsotropicPartner
