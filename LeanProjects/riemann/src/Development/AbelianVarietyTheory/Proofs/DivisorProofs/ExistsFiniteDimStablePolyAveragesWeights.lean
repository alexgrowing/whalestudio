import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin

noncomputable section

open MeasureTheory MvPolynomial
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1
open ReciprocityTheory.ChartRestriction.DS (IsURepOn UJset)

namespace GlobalTheory.PsCo.PolyAvg

variable {n : ℕ}

theorem totalDegree_bind_le {α β : Type} (g : α → MvPolynomial β ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial α ℂ) : (bind₁ g Q).totalDegree ≤ Q.totalDegree := by
  classical
  conv_lhs => rw [Q.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (hg i))).trans ?_
  simp [Finsupp.sum]

theorem exists_translate (a : Mat n) (P : Poly n) :
    ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧ ∀ g, ev (a * g) P = ev g Q := by
  let f : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Poly n := Sum.elim
    (fun x => ∑ c, C (a x.1 c) * X (Sum.inl (c, x.2))) (fun x => ∑ c, C (star (a x.1 c)) * X (Sum.inr (c, x.2)))
  refine ⟨bind₁ f P, totalDegree_bind_le f ?_ P, fun g => ?_⟩
  · rintro (x | x) <;>
    · refine totalDegree_finsetSum_le fun l _ => (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_C]
  · have h : ev (a * g) = (ev g).comp (bind₁ f : Poly n →ₐ[ℂ] Poly n).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) ?_
      · simp [ev]
      · rintro (x | x) <;> simp [ev, f, Matrix.mul_apply]
    rw [h]; rfl

def varWt : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Fin n → ℝ :=
  Sum.elim (fun x => -Pi.single x.1 1) (fun x => Pi.single x.1 1)

def monWt (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) : Fin n → ℝ := fun a => ∑ i, (s i : ℝ) * varWt i a

theorem ev_diag_monomial (θ : Fin n → ℝ) (g : Mat n) (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) :
    ev (Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) * g) (monomial s 1) =
      Complex.exp (((∑ a, monWt s a * θ a : ℝ) : ℂ) * Complex.I) * ev g (monomial s 1) := by
  have h1 : (∑ a, monWt s a * θ a : ℝ) = ∑ i, (s i : ℝ) * ∑ a, varWt i a * θ a := by
    simp only [monWt, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [h1]
  simp only [ev, eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Complex.ofReal_sum, Finset.sum_mul,
    Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc, Complex.exp_nat_mul, ← mul_pow]
  congr 1
  rcases i with x | x
  · simp [varWt, Pi.single_apply, ite_mul]
  · simp [varWt, Pi.single_apply, ite_mul, ← Complex.exp_conj]

theorem continuous_toMK (ε : Fin n → Bool) : Continuous fun k : KG ε => toMK k :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val

theorem continuous_ev (P : Poly n) : Continuous fun g : Mat n => ev g P := by
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi ?_)
  rintro (x | x)
  · simp only [Sum.elim_inl]; fun_prop
  · simp only [Sum.elim_inr]; fun_prop

theorem toMK_mem (ε : Fin n → Bool) (k : KG ε) : toMK k ∈ UJset ε := (k : Formalism.REAL.UJ ε).2

theorem toMK_mul (ε : Fin n → Bool) (a b : KG ε) : toMK (a * b) = toMK a * toMK b := rfl

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Mat n → (H →L[ℂ] H)}

omit [CompleteSpace H] in
theorem integrable_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (P : Poly n) :
    Integrable (fun k : KG ε => ev (toMK k) P • σ (toMK k) u) (muK ε) := by
  have h : Continuous fun k : KG ε => ev (toMK k) P • σ (toMK k) u :=
    ((continuous_ev P).comp (continuous_toMK ε)).smul
      ((hσ.2.2 u).comp_continuous (continuous_toMK ε) (toMK_mem ε))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def avg (hσ : IsURepOn (UJset ε) σ) (u : H) : Poly n →ₗ[ℂ] H where
  toFun P := ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε)
  map_add' P Q := by
    rw [← integral_add (integrable_avg hσ u P) (integrable_avg hσ u Q)]
    simp only [map_add, add_smul]
  map_smul' c P := by
    rw [RingHom.id_apply, ← integral_smul]
    simp [ev, smul_eq_C_mul, mul_smul]

theorem apply_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (P : Poly n) (g : KG ε) :
    σ (toMK g) (avg hσ u P) = ∫ k : KG ε, ev (toMK g⁻¹ * toMK k) P • σ (toMK k) u ∂(muK ε) := by
  change σ (toMK g) (∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε)) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hσ u P),
    ← integral_mul_left_eq_self (fun k : KG ε => ev (toMK g⁻¹ * toMK k) P • σ (toMK k) u) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only
  rw [← toMK_mul, inv_mul_cancel_left, toMK_mul, hσ.1.2 _ (toMK_mem ε g) _ (toMK_mem ε k), map_smul]
  rfl

theorem isWtOn_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ (monWt s) (avg hσ u (monomial s 1)) := by
  intro θ hθ
  rw [← Formalism.REAL.range_toMK] at hθ
  obtain ⟨g, hg⟩ := hθ
  simp only at hg
  have hinv : toMK g⁻¹ = Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) := by
    have h1 : toMK g * Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) = 1 := by
      rw [hg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have h2 : toMK g⁻¹ * toMK g = 1 := by rw [← toMK_mul, inv_mul_cancel]; rfl
    rw [← Matrix.mul_one (toMK g⁻¹), ← h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [← hg, apply_avg, hinv]
  simp only [ev_diag_monomial, mul_smul]
  rw [integral_smul]
  rfl

theorem polyAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧ (∀ P : GlobalTheory.PsCo.Pc1.Poly n, P.totalDegree ≤ d → ∫ k : Formalism.REAL.KG ε, GlobalTheory.PsCo.Pc1.ev (Formalism.REAL.toMK k) P • σ (Formalism.REAL.toMK k) u ∂(Formalism.REAL.muK ε) ∈ S) ∧ ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A := by
  intro n ε d
  refine ⟨monWt '' {s | s.degree ≤ d}, (Finsupp.finite_of_degree_le d).image _, ?_⟩
  intro H _ _ _ σ hσ u
  refine ⟨(restrictTotalDegree _ ℂ d).map (avg hσ u), inferInstance, ?_, ?_, ?_⟩
  · rintro g hg v ⟨P, hP, rfl⟩
    rw [← Formalism.REAL.range_toMK] at hg
    obtain ⟨g, rfl⟩ := hg
    obtain ⟨Q, hQ, hQ'⟩ := exists_translate (toMK g⁻¹) P
    refine ⟨Q, (mem_restrictTotalDegree _ _ _).2 (hQ.trans ((mem_restrictTotalDegree _ _ _).1 hP)), ?_⟩
    simp only
    rw [apply_avg]
    simp only [hQ']
    rfl
  · intro P hP
    exact ⟨P, (mem_restrictTotalDegree _ _ _).2 hP, rfl⟩
  · rintro μ v ⟨P, hP, rfl⟩ hv hw
    by_contra hμ
    apply hv
    have hP' : P.totalDegree ≤ d := (mem_restrictTotalDegree _ _ _).1 hP
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    have e : avg hσ u P = ∑ s ∈ P.support, coeff s P • avg hσ u (monomial s 1) := by
      conv_lhs => rw [P.as_sum, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
    generalize avg hσ u P = v at e hw
    have : inner ℂ v (∑ s ∈ P.support, coeff s P • avg hσ u (monomial s 1)) = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [inner_smul_right, ReciprocityTheory.ChartRestriction.DS.kfin_wt_orth hσ hw (isWtOn_avg hσ u s), mul_zero]
      rintro rfl
      exact hμ ⟨s, (le_totalDegree hs).trans hP', rfl⟩
    rwa [← e] at this

end GlobalTheory.PsCo.PolyAvg

end
