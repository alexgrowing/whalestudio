import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule

set_option autoImplicit false

noncomputable section

open scoped NNReal NumberField Classical
open GlobalTheory.HTLat GlobalTheory.EigenSplit

namespace GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison

section Valuations

variable {C : Type} [Field C]

def absDifferent (v : Valuation C ℝ≥0) {E : Type} [Field E] [NumberField E] (τ : E →+* C) : ℝ≥0 :=
  sSup {r | ∃ x ∈ differentIdeal ℤ (𝓞 E), v (τ x) = r}

def valDifferent_vp (p : ℕ) (v : Valuation C ℝ≥0) {E : Type} [Field E] [NumberField E]
    (τ : E →+* C) : ℝ :=
  Real.log (absDifferent v τ) / Real.log (v (p : C))

def IsPowMul_vp (p : ℕ) (v : Valuation C ℝ≥0) {O : Type} [CommRing O] [Algebra O C] {U : Type}
    [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] (t : ℝ)
    (La La' : Submodule O U) : Prop :=
  ∃ u : C, (v u : ℝ) = (v (p : C) : ℝ) ^ t ∧ La' = scaleLat u La

set_option autoImplicit false in
open scoped NNReal NumberField Classical in
variable {C : Type} [Field C] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.exists_generator_different {v : Valuation C ℝ≥0} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
    (τ : E →+* C) :
    ∃ δ : O, (differentIdeal ℤ (𝓞 E)).map (_root_.GlobalTheory.HTLat.embO hv τ) =
        Ideal.span {δ} ∧
      v (algebraMap O C δ) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ ≠ 0 ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ ≤ 1 := by
  set f := _root_.GlobalTheory.HTLat.embO hv τ with hf
  have hemb : ∀ x : 𝓞 E, algebraMap O C (f x) = τ x :=
    _root_.GlobalTheory.HTLat.algebraMap_embO hv τ
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (differentIdeal ℤ (𝓞 E))
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hne
    rw [← hS]
    simp
  obtain ⟨g, hgS, hmax⟩ := Finset.exists_max_image S (fun g => v (τ g)) hSne
  have hgI : g ∈ differentIdeal ℤ (𝓞 E) := hS ▸ Submodule.subset_span hgS
  have hdvd : ∀ x ∈ differentIdeal ℤ (𝓞 E), f g ∣ f x := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      apply hv.dvd_of_le
      rw [hemb, hemb]
      exact hmax y hy
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add]
      exact dvd_add ha hb
    | smul a b _ hb =>
      rw [smul_eq_mul, map_mul]
      exact dvd_mul_of_dvd_right hb _
  have hgreat : IsGreatest {r | ∃ x ∈ differentIdeal ℤ (𝓞 E), v (τ x) = r} (v (τ g)) := by
    refine ⟨⟨g, hgI, rfl⟩, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    rw [← hemb, ← hemb]
    exact hv.le_of_dvd (hdvd x hx)
  have habs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ = v (τ g) := hgreat.csSup_eq
  refine ⟨f g, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact hdvd x hx
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem f hgI
  · rw [habs, hemb]
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hx0' : v (τ x) ≠ 0 := by
      rw [Ne, map_eq_zero, map_eq_zero]
      exact_mod_cast hx0
    rw [habs]
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hx0') (hgreat.2 ⟨x, hx, rfl⟩))
  · rw [habs, ← hemb]
    exact hv.map_le_one _

example (p : ℕ) (v : Valuation C ℝ≥0) {O : Type} [CommRing O] [Algebra O C] {U : Type}
    [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] (La : Submodule O U) :
    IsPowMul_vp p v 1 La (scaleLat (p : C) La) := ⟨p, (Real.rpow_one _).symm, rfl⟩

end Valuations

section AtAPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] C] [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C] [IsAlgClosed C]
  [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E))

abbrev Flags (Ψ : Finset (E →+* C)) (N j : ℕ) : Type :=
  ∀ τ : Ψ, P.Frame (embO P.integers τ.1) N j

abbrev wHT (τ : E →+* C) : Submodule O P.V :=
  P.wHT (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) τ

abbrev omHT (τ : E →+* C) : Submodule O P.OmC :=
  P.omHT (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) τ

abbrev wRec (τ : E →+* C) : Submodule O P.V := P.wRec (embO P.integers τ)

abbrev omRec (τ : E →+* C) : Submodule O P.OmC :=
  P.omRec (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) τ

variable {P} {Ψ : Finset (E →+* C)} {N j : ℕ}

def phiDiff_vp (F : Flags P Ψ N j) (lam : Ψ → Fin N → ℝ) : ℝ :=
  Point.phiHT_vp (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) Ψ F lam -
    Point.phiRec_vp (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) Ψ F lam

def GradedComparison (F : Flags P Ψ N j) : Prop :=
  ∃ a : Ψ → Fin N → ℝ,
    (∀ τ i, 0 ≤ a τ i ∧ a τ i ≤ 1 / ((p : ℝ) - 1)) ∧
    (∀ (τ : Ψ) (i : Fin N), (i : ℕ) < j →
      IsPowMul_vp p v (-a τ i - valDifferent_vp p v τ.1)
        (grAt C (wRec P τ.1) (F τ).f i) (grAt C (wHT P τ.1) (F τ).f i)) ∧
    (∀ (τ : Ψ) (i : Fin N), j ≤ (i : ℕ) →
      IsPowMul_vp p v (a τ i)
        (grAt C (omRec P τ.1) (P.alC ∘ (F τ).f) i) (grAt C (omHT P τ.1) (P.alC ∘ (F τ).f) i)) ∧
    (∀ lam : Ψ → Fin N → ℝ, phiDiff_vp F lam = -Real.log p * ∑ τ : Ψ,
      ((∑ i : Fin N with i.val < j, lam τ i * (valDifferent_vp p v τ.1 + a τ i)) -
        ∑ i : Fin N with j ≤ i.val, lam τ i * a τ i)) ∧
    ∀ lam : Ψ → Fin N → ℝ, |phiDiff_vp F lam| ≤ Real.log p * ∑ τ : Ψ,
      (1 / ((p : ℝ) - 1) * ∑ i, |lam τ i| +
        valDifferent_vp p v τ.1 * |∑ i : Fin N with i.val < j, lam τ i|)

end AtAPoint

def PointwiseGeneral : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O]
    [Algebra O C] [Algebra ℤ_[p] C] [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C] [IsAlgClosed C]
    [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E))
    (Ψ : Finset (E →+* C)) (N j : ℕ) (F : Flags P Ψ N j), GradedComparison F

section PadicComplex

@[reducible] def algInt (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] 𝓞_ℂ_[p] := (padicIntHom p).toAlgebra

@[reducible] def algField (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] ℂ_[p] :=
  ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (padicIntHom p)).toAlgebra

attribute [local instance] algInt algField

theorem tower (p : ℕ) [Fact p.Prime] :
    @IsScalarTower ℤ_[p] 𝓞_ℂ_[p] ℂ_[p] (algInt p).toSMul Algebra.toSMul (algField p).toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem fact_not_isUnit (p : ℕ) [Fact p.Prime] : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) :=
  ⟨PadicComplexHost.not_isUnit_p p⟩

attribute [local instance] tower fact_not_isUnit PadicComplexHost.isAdicComplete

abbrev PointCp (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] : Type 1 :=
  Point p (Valued.v : Valuation ℂ_[p] ℝ≥0) 𝓞_ℂ_[p] (𝓞 E)

def Pointwise : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : PointCp p E)
    (Ψ : Finset (E →+* ℂ_[p])) (N j : ℕ) (F : Flags P Ψ N j), GradedComparison F

def ramifiedOrLevel (E : Type) [Field E] [NumberField E] (level : ℕ) : Finset ℕ :=
  (2 * (NumberField.discr E).natAbs * level).primeFactors

def badPrimes (E : Type) [Field E] [NumberField E] (level : ℕ) (B : ℝ) : Finset ℕ :=
  (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime ∪ ramifiedOrLevel E level

instance factPrime {E : Type} [Field E] [NumberField E] {level : ℕ} {B : ℝ}
    (p : badPrimes E level B) : Fact (p : ℕ).Prime :=
  ⟨(Finset.mem_union.1 p.2).elim (fun h => (Finset.mem_filter.1 h).2) Nat.prime_of_mem_primeFactors⟩

def SumOverBadPrimes : Prop :=
  ∃ K : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] [StarRing (𝓞 E)]
    (level : ℕ) (B : ℝ), 1 ≤ level → 2 ≤ B → ((ramifiedOrLevel E level).card : ℝ) ≤ B →
    ∀ (I : Type) [Fintype I] (N j : ℕ) (lam : I → Fin N → ℝ)
      (P : ∀ p : badPrimes E level B, PointCp p E)
      (Ψ : ∀ p : badPrimes E level B, Finset (E →+* ℂ_[p])) (e : ∀ p, Ψ p ≃ I)
      (F : ∀ p, Flags (P p) (Ψ p) N j),
      let lhs := ∑ p : badPrimes E level B, |phiDiff_vp (F p) fun τ => lam (e p τ)|
      let size := ∑ τ, ∑ i, |lam τ i|
      let first := (3 * Real.log B + 1) * size +
        Real.log (NumberField.rootDiscr E) * ∑ τ, |∑ i : Fin N with i.val < j, lam τ i|
      let second := (3 * Real.log B + 1 + Real.log (NumberField.rootDiscr E)) * size
      lhs ≤ first ∧ first ≤ K * Real.log (B * NumberField.rootDiscr E) * size ∧ first ≤ second ∧
        (3 ≤ B → second ≤ 4 * Real.log (B * NumberField.rootDiscr E) * size)

end PadicComplex

def Statement : Prop := Pointwise ∧ SumOverBadPrimes

end GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison
