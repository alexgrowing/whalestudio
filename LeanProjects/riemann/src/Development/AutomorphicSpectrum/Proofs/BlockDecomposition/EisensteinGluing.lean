import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GaloisBoundFirst

open Filter Topology Set
open PositivityTheory.Rg.SwEis

namespace GlobalTheory.CompanionTheory.PolyDenominator

theorem exists_pow_mul (B : ℂ → ℂ) (hB : Differentiable ℂ B) (hz : ∃ z, B z ≠ 0) (a : ℂ) :
    ∃ (k : ℕ) (v : ℂ → ℂ), Differentiable ℂ v ∧ v a ≠ 0 ∧ ∀ z, B z = (z - a) ^ k * v z :=
  _root_.UpperTheory.Reformulated.B.GaloisBoundFirst.main B hB hz a

theorem finite_zeros (B : ℂ → ℂ) (hB : Differentiable ℂ B) (hz : ∃ z, B z ≠ 0) {Q : Set ℂ} (hQ : IsCompact Q) :
    {z | z ∈ Q ∧ B z = 0}.Finite := by
  obtain ⟨z₀, hz₀⟩ := hz
  have han : AnalyticOnNhd ℂ B univ := fun x _ => hB.analyticAt x
  by_contra hinf
  have hinf' : ({z | z ∈ Q ∧ B z = 0} : Set ℂ).Infinite := hinf
  obtain ⟨x, hxQ, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact hQ (fun z hz => hz.1)
  have hfreq : ∃ᶠ z in 𝓝[≠] x, B z = 0 :=
    (accPt_iff_frequently_nhdsNE.1 hacc).mono fun z hz => hz.2
  exact hz₀ (han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ x) hfreq (mem_univ z₀))

theorem factor_of_finset {Q : Set ℂ} (F : Finset ℂ) :
    ∀ B : ℂ → ℂ, Differentiable ℂ B → (∃ z, B z ≠ 0) → (∀ z ∈ Q, B z = 0 → z ∈ F) →
      ∃ (d : Polynomial ℂ) (u : ℂ → ℂ), d ≠ 0 ∧ Differentiable ℂ u ∧
        (∀ z, B z = d.eval z * u z) ∧ ∀ z ∈ Q, u z ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro B hB _ hF
    refine ⟨1, B, one_ne_zero, hB, fun z => by simp, fun z hz h0 => ?_⟩
    simpa using hF z hz h0
  | insert a F _ ih =>
    intro B hB hz hF
    obtain ⟨k, v, hv, hva, hBv⟩ := exists_pow_mul B hB hz a
    obtain ⟨d, u, hd, hu, hvu, huQ⟩ := ih v hv ⟨a, hva⟩ (by
      intro z hzQ h0
      have hza : z ≠ a := fun h => hva (h ▸ h0)
      have hBz : B z = 0 := by rw [hBv, h0, mul_zero]
      exact (Finset.mem_insert.1 (hF z hzQ hBz)).resolve_left hza)
    refine ⟨(Polynomial.X - Polynomial.C a) ^ k * d, u,
      mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)) hd, hu, fun z => ?_, huQ⟩
    rw [hBv, hvu]
    simp [mul_assoc]

theorem exists_poly_factor (A : ℂ → ℂ) (hA : Differentiable ℂ A) (hz : ∃ z, A z ≠ 0) {Q : Set ℂ} (hQ : IsCompact Q) :
    ∃ (d : Polynomial ℂ) (u : ℂ → ℂ), d ≠ 0 ∧ Differentiable ℂ u ∧
      (∀ z, A z = d.eval z * u z) ∧ ∀ z ∈ Q, u z ≠ 0 :=
  factor_of_finset (finite_zeros A hA hz hQ).toFinset A hA hz fun z hzQ h0 => by simpa using And.intro hzQ h0

theorem glue : Glue := by
  classical
  intro X I _ T e H A R hA hAne hHd hHc hHe hed hec heT s₀
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min s₀.re R - 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = s₀.im := ⟨_, rfl⟩
  have hQ : IsCompact (Icc a (R + 1) ×ℂ Icc (c - 1) (c + 1)) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨d, u, hd, hu, hAu, huQ⟩ := exists_poly_factor A hA hAne hQ
  let P : Set ℂ := {z | R < z.re}
  let W : Set ℂ := {z | a < z.re ∧ z.re < R + 1 ∧ c - 1 < z.im ∧ z.im < c + 1}
  let U : Set ℂ := P ∪ {z | a < z.re ∧ c - 1 < z.im ∧ z.im < c + 1}
  have hPo : IsOpen P := isOpen_lt continuous_const Complex.continuous_re
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hUo : IsOpen U := hPo.union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))
  have hWQ : ∀ z ∈ W, u z ≠ 0 := fun z hz => huQ z (Complex.mem_reProdIm.2
    ⟨⟨hz.1.le, hz.2.1.le⟩, ⟨hz.2.2.1.le, hz.2.2.2.le⟩⟩)
  have hUPW : ∀ z ∈ U, z ∈ P ∨ z ∈ W := by
    rintro z (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · by_cases h : R < z.re
      · exact Or.inl h
      · exact Or.inr ⟨h1, by linarith [not_lt.1 h], h2, h3⟩
  let E : ℂ → X → ℂ := fun z x => if R < z.re then d.eval z * e z x else H z x / u z
  have hEP : ∀ z, R < z.re → ∀ x, E z x = d.eval z * e z x := fun z h x => by simp [E, h]
  have hEW : ∀ z ∈ W, ∀ x, E z x = H z x / u z := by
    intro z hz x
    by_cases h : R < z.re
    · have h0 := hWQ z hz
      rw [hEP z h, hHe z h, hAu z]
      field_simp
    · simp [E, h]
  have hHT : ∀ i x z, H z (T i x) = H z x := by
    intro i x z
    have h1 : AnalyticOnNhd ℂ (H · (T i x)) univ := fun w _ => (hHd (T i x)).analyticAt w
    have h2 : AnalyticOnNhd ℂ (H · x) univ := fun w _ => (hHd x).analyticAt w
    have hmem : ((R + 1 : ℝ) : ℂ) ∈ P := by simp [P]
    have h3 : (H · (T i x)) =ᶠ[𝓝 ((R + 1 : ℝ) : ℂ)] (H · x) := by
      filter_upwards [hPo.mem_nhds hmem] with w hw
      rw [hHe w hw, hHe w hw, heT]
    exact congrFun (h1.eq_of_eventuallyEq h2 h3) z
  refine ⟨U, d, E, hUo, ⟨⟨R, subset_union_left⟩, ?_⟩, ?_, hd, ?_, ?_, ?_, fun z hz x => hEP z hz x⟩
  · rintro s (h | ⟨h1, h2, h3⟩) t ht
    · left
      simp only [P, mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
      exact lt_add_of_lt_of_nonneg h ht
    · right
      simp only [mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
      exact ⟨lt_add_of_lt_of_nonneg h1 ht, h2, h3⟩
  · by_cases h : R < s₀.re
    · exact Or.inl h
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · have := min_le_left s₀.re R
        rw [ha]; linarith
      · rw [hc]; linarith
      · rw [hc]; linarith
  · intro x z hz
    rcases hUPW z hz with h | h
    · have h1 : DifferentiableAt ℂ (fun w => d.eval w * e w x) z :=
        (d.differentiable z).mul ((hed x z h).differentiableAt (hPo.mem_nhds h))
      refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hPo.mem_nhds h] with w hw using hEP w hw x
    · have h1 : DifferentiableAt ℂ (fun w => H w x / u w) z := (hHd x z).div (hu z) (hWQ z h)
      refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hWo.mem_nhds h] with w hw using hEW w hw x
  · have hc1 : ContinuousOn (fun y : ℂ × X => d.eval y.1 * e y.1 y.2) (P ×ˢ univ) :=
      (d.continuous.comp continuous_fst).continuousOn.mul hec
    have hc2 : ContinuousOn (fun y : ℂ × X => H y.1 y.2 / u y.1) (W ×ˢ univ) :=
      hHc.continuousOn.div (hu.continuous.comp continuous_fst).continuousOn fun y hy => hWQ y.1 hy.1
    rintro ⟨z, x⟩ ⟨hz, -⟩
    rcases hUPW z hz with h | h
    · have ho : IsOpen (P ×ˢ (univ : Set X)) := hPo.prod isOpen_univ
      have hmem : (z, x) ∈ P ×ˢ (univ : Set X) := ⟨h, mem_univ x⟩
      have : ContinuousOn (fun y : ℂ × X => E y.1 y.2) (P ×ˢ univ) :=
        hc1.congr fun y hy => hEP y.1 hy.1 y.2
      exact (this.continuousAt (ho.mem_nhds hmem)).continuousWithinAt
    · have ho : IsOpen (W ×ˢ (univ : Set X)) := hWo.prod isOpen_univ
      have hmem : (z, x) ∈ W ×ˢ (univ : Set X) := ⟨h, mem_univ x⟩
      have : ContinuousOn (fun y : ℂ × X => E y.1 y.2) (W ×ˢ univ) :=
        hc2.congr fun y hy => hEW y.1 hy.1 y.2
      exact (this.continuousAt (ho.mem_nhds hmem)).continuousWithinAt
  · intro z hz i x
    rcases hUPW z hz with h | h
    · rw [hEP z h, hEP z h, heT]
    · rw [hEW z h, hEW z h, hHT]

end GlobalTheory.CompanionTheory.PolyDenominator
