import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjMulEq
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.UnitNormLocal

open IsLocalRing

theorem exists_conj_mul_eq_of_residue_one {R : Type} [CommRing R] [HenselianLocalRing R]
    (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (x₀ : R) (hx : IsUnit (σ x₀ - x₀)) (a : R)
    (ha : a ∈ maximalIdeal R) (hfix : σ a = a) :
    ∃ s : R, σ s * s = 1 + a := by
  have hmax : ∀ y ∈ maximalIdeal R, σ y ∈ maximalIdeal R := by
    intro y hy
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    exact fun h => hy (by simpa [hσ] using h.map σ)
  have hres : ∀ y, y - 1 ∈ maximalIdeal R → IsUnit y := by
    intro y hy
    by_contra h
    have h1 : y ∈ maximalIdeal R := (mem_maximalIdeal _).2 h
    have h2 : (1 : R) ∈ maximalIdeal R := by simpa using sub_mem h1 hy
    exact (Ideal.ne_top_iff_one _).1 (maximalIdeal.isMaximal R).ne_top h2
  obtain ⟨d, hd⟩ := hx
  set di : R := ((d⁻¹ : Rˣ) : R) with hdi
  have hddi : (σ x₀ - x₀) * di = 1 := by rw [← hd, hdi]; exact d.mul_inv
  set e : R := -x₀ * di with he
  set f : R := σ e with hf
  have hσdi : σ di = -di := by
    have h1 : σ ((σ x₀ - x₀) * di) = 1 := by rw [hddi, map_one]
    rw [map_mul, map_sub, hσ] at h1
    linear_combination (-di) * h1 + (-σ di) * hddi
  have hef : e + f = 1 := by
    rw [hf, he, map_mul, map_neg, hσdi]
    linear_combination hddi
  have hfe : σ f = e := by rw [hf, hσ]
  set n : R := e * f with hn
  have hσn : σ n = n := by rw [hn, map_mul, hfe, ← hf]; ring
  let P : R[X] := X ^ 2 - X - C (n * a)
  have hP : P.Monic := by simp only [P]; monicity!
  have hP1 : P.eval 1 ∈ maximalIdeal R := by
    have : P.eval 1 = -(n * a) := by simp [P]
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ ha)
  have hP2 : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (P.derivative.eval 1)) := by
    have : P.derivative.eval 1 = 1 := by
      simp [P, derivative_X_pow]
    rw [this, map_one]; exact isUnit_one
  obtain ⟨u, hu, hu1⟩ := HenselianRing.is_henselian (I := maximalIdeal R) P hP 1 hP1 (by exact hP2)
  have hroot : u ^ 2 - u = n * a := by
    have : P.eval u = 0 := hu
    simp only [P, eval_sub, eval_pow, eval_X, eval_C] at this
    linear_combination this
  have hroot' : (σ u) ^ 2 - σ u = n * a := by
    have := congrArg σ hroot
    simpa only [map_sub, map_pow, map_mul, hσn, hfix] using this
  have hv1 : σ u - 1 ∈ maximalIdeal R := by simpa using hmax _ hu1
  have hw : IsUnit (u + σ u - 1) := hres _ (by
    have := add_mem hu1 hv1
    convert this using 1
    ring)
  have huu : σ u = u := by
    have h0 : (u - σ u) * (u + σ u - 1) = 0 := by linear_combination hroot - hroot'
    have := hw.mul_left_eq_zero.1 h0
    exact (sub_eq_zero.1 this).symm
  obtain ⟨U, hU⟩ := hres u hu1
  set ui : R := ((U⁻¹ : Rˣ) : R) with hui
  have huui : u * ui = 1 := by rw [← hU, hui]; exact U.mul_inv
  have hσui : σ ui = ui := by
    have h1 : σ (u * ui) = 1 := by rw [huui, map_one]
    rw [map_mul, huu] at h1
    linear_combination ui * h1 - σ ui * huui
  have h2 : a * ui + n * (a * ui) ^ 2 = a := by
    linear_combination (-a * ui ^ 2) * hroot + (a * (ui * u + 1) - a * ui) * huui
  refine ⟨1 + e * (a * ui), ?_⟩
  have hσt : σ (a * ui) = a * ui := by rw [map_mul, hfix, hσui]
  rw [map_add, map_one, map_mul σ e, hσt, ← hf]
  linear_combination (a * ui) * hef + h2 - (a * ui) ^ 2 * hn

theorem exists_isUnit_conj_mul_eq {R : Type} [CommRing R] [HenselianLocalRing R]
    [Finite (ResidueField R)] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (x₀ : R)
    (hx : IsUnit (σ x₀ - x₀)) (c : R) (hc : IsUnit c) (hfix : σ c = c) :
    ∃ s : R, IsUnit s ∧ σ s * s = c := by
  haveI : IsLocalHom σ := ⟨fun a h => by simpa [hσ] using h.map σ⟩
  let τ : ResidueField R →+* ResidueField R := ResidueField.map σ
  have hτ : ∀ y, τ (residue R y) = residue R (σ y) := fun y => ResidueField.map_residue σ y
  have hτ2 : ∀ x, τ (τ x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    rw [hτ, hτ, hσ]
  have hne : ∃ x, τ x ≠ x := by
    refine ⟨residue R x₀, fun h => ?_⟩
    rw [hτ] at h
    have h0 : residue R (σ x₀ - x₀) = 0 := by rw [map_sub, h, sub_self]
    exact (residue_ne_zero_iff_isUnit _).2 hx h0
  obtain ⟨sb, hsb⟩ := GlobalTheory.CompanionTheory.FFNorm.exists_conj_mul_eq (ResidueField R) τ hτ2 hne (residue R c)
    (by rw [hτ, hfix])
  obtain ⟨s₀, rfl⟩ := residue_surjective sb
  rw [hτ, ← map_mul] at hsb
  have hs₀ : IsUnit s₀ := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h0
    rw [map_mul, h0, mul_zero] at hsb
    exact (residue_ne_zero_iff_isUnit _).2 hc hsb.symm
  obtain ⟨D, hD⟩ := (hs₀.map σ).mul hs₀
  set Di : R := ((D⁻¹ : Rˣ) : R) with hDi
  have hDDi : σ s₀ * s₀ * Di = 1 := by rw [← hD, hDi]; exact D.mul_inv
  have hσD : σ (σ s₀ * s₀) = σ s₀ * s₀ := by rw [map_mul, hσ, mul_comm]
  have hσDi : σ Di = Di := by
    have h1 : σ (σ s₀ * s₀ * Di) = 1 := by rw [hDDi, map_one]
    rw [map_mul, hσD] at h1
    linear_combination Di * h1 - σ Di * hDDi
  have ha : c * Di - 1 ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, ← hsb, ← map_mul, hDDi, map_one, sub_self]
  obtain ⟨s₁, hs₁⟩ := exists_conj_mul_eq_of_residue_one σ hσ x₀ hx _ ha
    (by rw [map_sub, map_mul, hfix, hσDi, map_one])
  have hmul : σ (s₀ * s₁) * (s₀ * s₁) = c := by
    rw [map_mul]
    linear_combination (σ s₀ * s₀) * hs₁ + c * hDDi
  refine ⟨s₀ * s₁, ?_, hmul⟩
  exact isUnit_of_mul_isUnit_right (hmul ▸ hc)

theorem exists_unit_norm_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ c : w.adicCompletion E, cj w c = c → Valued.v c = 1 → ∃ s : w.adicCompletion E, Valued.v s = 1 ∧ cj w s * s = c := by
  intro E _ _ _ hU w hw c hcj hcv
  obtain ⟨-, hinv, hval, hns, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨-, ⟨ϖ, q, hI, -⟩, -, -⟩ := hns hw
  obtain ⟨-, -, -, -, ⟨x₀, hx₀, hx⟩, hq, hcard⟩ := hI
  haveI := Formalism.BasicNotions.Examples₂.adicInt_henselian (K := E) w
  have hfin : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) := by
    refine Nat.finite_of_card_ne_zero ?_
    have h := hcard
    have h2 : q ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
    rw [← h] at h2
    exact h2
  have hmem : ∀ x : w.adicCompletionIntegers E, cj w x ∈ w.adicCompletionIntegers E := by
    intro x
    have hx2 := x.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx2 ⊢
    rwa [hval]
  let σ : w.adicCompletionIntegers E →+* w.adicCompletionIntegers E :=
    ((cj w).comp (w.adicCompletionIntegers E).subtype).codRestrict _ hmem
  have hσc : ∀ x, ((σ x : w.adicCompletionIntegers E) : w.adicCompletion E) = cj w x := fun _ => rfl
  have hunit : ∀ x : w.adicCompletionIntegers E, IsUnit x ↔ Valued.v (x : w.adicCompletion E) = 1 :=
    fun x => (Formalism.BasicNotions.Examples₂.adicInt_integers w).isUnit_iff_valuation_eq_one
  have hσ : ∀ x, σ (σ x) = x := fun x => Subtype.ext (hinv _)
  let y₀ : w.adicCompletionIntegers E := ⟨x₀, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx₀⟩
  have hy : IsUnit (σ y₀ - y₀) := (hunit _).2 hx
  let c₀ : w.adicCompletionIntegers E := ⟨c, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hcv.le⟩
  have hc₀ : IsUnit c₀ := (hunit _).2 hcv
  obtain ⟨s, hs, hsc⟩ := exists_isUnit_conj_mul_eq σ hσ y₀ hy c₀ hc₀ (Subtype.ext hcj)
  exact ⟨s, (hunit s).1 hs, congrArg Subtype.val hsc⟩

end GlobalTheory.CompanionTheory.UnitNormLocal
