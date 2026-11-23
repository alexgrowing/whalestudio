import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EigenNorm

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_add_left (z z' w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z + z') w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z' w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_add_right (z w w' : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (w + w') = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w' := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_smul_left (r : ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (r • z) w = r * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, smul_eq_mul]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_smul_right (r : ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (r • w) = starRingEnd ℂ r * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rfl

theorem hermForm_sum_left {κ : Type*} (s : Finset κ) (z : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i ∈ s, z i) w = ∑ i ∈ s, hermForm Hm (z i) w := by
  simp [hermForm, sum_dotProduct]

theorem hermForm_sum_right {κ : Type*} (s : Finset κ) (z : Fin g → ℂ) (w : κ → Fin g → ℂ) :
    hermForm Hm z (∑ i ∈ s, w i) = ∑ i ∈ s, hermForm Hm z (w i) := by
  simp [hermForm, star_sum, Matrix.mulVec_sum, dotProduct_sum]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_conj (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm w z = starRingEnd ℂ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w) := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun hH i) j
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h]
  simp [Pi.star_apply, Complex.star_def]
  ring

theorem eq_zero_of_sum_embedding_mul {E : Type} [Field E] [NumberField E] (f : (E →+* ℂ) → ℂ)
    (hf : ∀ s : 𝓞 E, ∑ τ : E →+* ℂ, τ (s : E) * f τ = 0) (τ : E →+* ℂ) : f τ = 0 := by
  have hinj : Function.Injective
      (fun τ : E →+* ℂ => ((τ.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ) : 𝓞 E →* ℂ)) := by
    intro τ₁ τ₂ h12
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun s => ?_
    exact DFunLike.congr_fun h12 s
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ hinj
  refine Fintype.linearIndependent_iff.1 hli f ?_ τ
  funext s
  simpa [mul_comm] using hf s

theorem conj_eq_neg_of_sq {ρ : ℂ} {d : ℕ} (hd : d ≠ 0) (h : ρ ^ 2 = -(d : ℂ)) : starRingEnd ℂ ρ = -ρ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two] at h1 h2
  have h3 : ρ.re * ρ.im = 0 := by linarith [mul_comm ρ.re ρ.im]
  have h4 : ρ.re = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · rw [h] at h1; nlinarith [mul_self_nonneg ρ.re]
  apply Complex.ext <;> simp [h4]

theorem hermForm_eigen :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian →
  ∀ (L : Type) [AddCommGroup L] [Module (𝓞 E) L] (h : L → L → E) (ρ : ℂ) (c : ℝ) (x : (E →+* ℂ) → L →+ (Fin g → ℂ)),
  ρ ^ 2 = -(H.d : ℂ) → (∀ a b e, h (a + b) e = h a e + h b e) → (∀ (s : 𝓞 E) a e, h (s • a) e = s * h a e) →
  (∀ a b, h b a = IsCMField.complexConj E (h a b)) →
  (∀ τ (s : 𝓞 E) a, x τ (s • a) = τ (s : E) • x τ a) → (∀ τ, τ (H.rt : E) ≠ ρ → x τ = 0) →
  (∀ a, hermForm Hm (∑ τ, x τ a) (∑ τ, x τ a) = c * ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ), τ (h a a)) →
  ∀ τ τ' a b, τ (H.rt : E) = ρ → hermForm Hm (x τ a) (x τ' b) = open Classical in if τ' = τ then c * τ (h a b) else 0 := by
  intro E _ _ _ H g Hm hH L _ _ h ρ c x hρ hadd hsmul hsymm hx hx0 hq τ τ' a b hτ
  classical
  have hd : H.d ≠ 0 := H.d_prime.ne_zero
  have hρc := conj_eq_neg_of_sq hd hρ
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    apply hd
    have : (H.d : ℂ) = 0 := by simpa using hρ.symm
    exact_mod_cast this
  have hconj : ∀ (σ : E →+* ℂ) a b, σ (h b a) = starRingEnd ℂ (σ (h a b)) := fun σ a b => by
    rw [hsymm a b, IsCMField.complexEmbedding_complexConj]
  have haddr : ∀ (σ : E →+* ℂ) e a b, σ (h e (a + b)) = σ (h e a) + σ (h e b) := fun σ e a b => by
    rw [hconj σ (a + b) e, hconj σ a e, hconj σ b e, hadd, map_add, map_add]
  have hsmulr : ∀ (σ : E →+* ℂ) (s : 𝓞 E) e a, σ (h e (s • a)) = starRingEnd ℂ (σ s) * σ (h e a) :=
    fun σ s e a => by rw [hconj σ (s • a) e, hconj σ a e, hsmul, map_mul, map_mul]
  set Ψ := Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ) with hΨ
  let D : L → L → ℂ := fun a b =>
    hermForm Hm (∑ τ, x τ a) (∑ τ, x τ b) - c * ∑ τ ∈ Ψ, τ (h a b)
  have hD0 : ∀ a, D a a = 0 := fun a => sub_eq_zero.2 (hq a)
  have hDc : ∀ a b, D b a = starRingEnd ℂ (D a b) := fun a b => by
    simp only [D, map_sub, map_mul, map_sum, Complex.conj_ofReal, ← hconj]
    rw [hermForm_conj Hm hH]
  have hDl : ∀ a b e, D (a + b) e = D a e + D b e := fun a b e => by
    simp only [D, map_add, hadd, Finset.sum_add_distrib, hermForm_add_left]; ring
  have hDr : ∀ e a b, D e (a + b) = D e a + D e b := fun e a b => by
    simp only [D, map_add, haddr, Finset.sum_add_distrib, hermForm_add_right]; ring
  have hDpol : ∀ a b, D a b + starRingEnd ℂ (D a b) = 0 := fun a b => by
    have := hD0 (a + b)
    rw [hDl, hDr, hDr, hD0, hD0, hDc a b] at this
    linear_combination this
  have hDrt : ∀ a b, D (H.rt • a) b = ρ * D a b := fun a b => by
    have h1 : ∑ τ, x τ (H.rt • a) = ρ • ∑ τ, x τ a := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases hσ : σ (H.rt : E) = ρ
      · rw [hx, hσ]
      · simp [hx0 σ hσ]
    have h2 : ∑ τ ∈ Ψ, τ (h (H.rt • a) b) = ρ * ∑ τ ∈ Ψ, τ (h a b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ hσ => ?_
      rw [hsmul, map_mul, (Finset.mem_filter.1 hσ).2]
    simp only [D]
    rw [h1, h2, hermForm_smul_left]; ring
  have hD : ∀ a b, D a b = 0 := fun a b => by
    have h1 := hDpol a b
    have h2 := hDpol (H.rt • a) b
    rw [hDrt, map_mul, hρc] at h2
    have h3 : ρ * (2 * D a b) = 0 := by linear_combination h2 + ρ * h1
    simpa [hρ0] using h3
  have hstep : ∀ b, hermForm Hm (x τ a) (∑ σ, x σ b) = c * τ (h a b) := fun b => by
    have := eq_zero_of_sum_embedding_mul
      (fun σ : E →+* ℂ => hermForm Hm (x σ a) (∑ σ, x σ b) -
        if σ (H.rt : E) = ρ then (c : ℂ) * σ (h a b) else 0) (fun s => ?_) τ
    · simpa [hτ, sub_eq_zero] using this
    have h1 := hD (s • a) b
    simp only [D, hΨ] at h1
    rw [hermForm_sum_left, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib] at h1
    refine Eq.trans (Finset.sum_congr rfl fun σ _ => ?_) h1
    rw [hx, hermForm_smul_left, hsmul, map_mul]
    split_ifs <;> ring
  have := eq_zero_of_sum_embedding_mul
    (fun σ : E →+* ℂ => starRingEnd ℂ (hermForm Hm (x τ a) (x σ b) -
      if σ = τ then (c : ℂ) * τ (h a b) else 0)) (fun s => ?_) τ'
  · rw [map_eq_zero, sub_eq_zero] at this
    convert this
  have h1 := hstep (s • b)
  rw [hermForm_sum_right, hsmulr] at h1
  simp only [hx, hermForm_smul_right] at h1
  have h2 : ∑ σ : E →+* ℂ, starRingEnd ℂ (σ (s : E)) * (hermForm Hm (x τ a) (x σ b) -
      if σ = τ then (c : ℂ) * τ (h a b) else 0) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, h1, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have h3 := congrArg (starRingEnd ℂ) h2
  simpa only [map_sum, map_mul, Complex.conj_conj, map_zero] using h3

end GlobalTheory.EigenNorm
