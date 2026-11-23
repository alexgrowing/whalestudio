import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.InertUQ

open IsDedekindDomain.HeightOneSpectrum

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem mem_max_iff (x : w.adicCompletionIntegers E) :
    x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) ↔ Valued.v (x : w.adicCompletion E) < 1 := by
  have hI := Valuation.valuationSubring.integers (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx : Valued.v (x : w.adicCompletion E) ≤ 1 := x.2
  constructor
  · intro hn
    refine lt_of_le_of_ne hx fun h => hn ?_
    exact (hI.isUnit_iff_valuation_eq_one (x := x)).2 h
  · intro hlt hu
    exact (ne_of_lt hlt) ((hI.isUnit_iff_valuation_eq_one (x := x)).1 hu)

private lemma withZero_lt_one_iff_le_exp_neg_one (g : WithZero (Multiplicative ℤ)) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · rw [← WithZero.exp_log hg, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

private lemma mem_span_pow_iff_valuation_le_exp_neg_one_pow (p : w.adicCompletionIntegers E)
    (hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (a : w.adicCompletionIntegers E) :
    a ∈ Ideal.span {p ^ n} ↔ Valued.v (a : w.adicCompletion E) ≤ WithZero.exp (-1 : ℤ) ^ n := by
  have hp0 : (p : w.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, rfl⟩
    have hb : Valued.v (b : w.adicCompletion E) ≤ 1 := b.2
    push_cast
    rw [map_mul, map_pow, hp]
    exact mul_le_of_le_one_right' hb
  · intro ha
    have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-1 : ℤ) ^ n :=
      zero_lt_iff.2 (pow_ne_zero _ WithZero.exp_ne_zero)
    have hb : Valued.v ((a : w.adicCompletion E) / (p : w.adicCompletion E) ^ n) ≤ 1 := by
      rw [map_div₀, map_pow, hp]
      exact (div_le_one₀ hpos).2 ha
    refine ⟨⟨_, hb⟩, ?_⟩
    apply Subtype.ext
    push_cast
    field_simp

private lemma maximalIdeal_eq_span_of_valuation_eq_exp_neg_one (p : w.adicCompletionIntegers E)
    (hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) = Ideal.span {p} := by
  ext a
  have h := mem_span_pow_iff_valuation_le_exp_neg_one_pow w p hp 1 a
  rw [pow_one, pow_one] at h
  rw [h, mem_max_iff, withZero_lt_one_iff_le_exp_neg_one]

theorem valuation_max_eq (ϖ : w.adicCompletion E) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (x : w.adicCompletion E) :
    (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation (w.adicCompletion E) x
      = Valued.v x := by
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ]
    exact ((withZero_lt_one_iff_le_exp_neg_one _).2 le_rfl).le
  let p : w.adicCompletionIntegers E := ⟨ϖ, hϖ1⟩
  have hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hp0 : p ≠ 0 := fun h => hϖ0 (congrArg Subtype.val h)
  have hVp : (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) ϖ = WithZero.exp (-1 : ℤ) := by
    have h1 := (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation_of_algebraMap
      (K := w.adicCompletion E) p
    rw [(IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).intValuation_singleton hp0
      (maximalIdeal_eq_span_of_valuation_eq_exp_neg_one w p hp)] at h1
    exact h1
  have hVu : ∀ a : w.adicCompletionIntegers E, Valued.v (a : w.adicCompletion E) = 1 →
      (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
        (w.adicCompletion E) a = 1 := by
    intro a ha
    have h1 := (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation_of_algebraMap
      (K := w.adicCompletion E) a
    refine h1.trans (HeightOneSpectrum.intValuation_eq_one_iff.2 fun hmem => ?_)
    have := (mem_max_iff w a).1 hmem
    rw [ha] at this
    exact lt_irrefl _ this
  by_cases hx : x = 0
  · simp [hx]
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v x = WithZero.exp k := ⟨_, (WithZero.exp_log hvx).symm⟩
  have hy : Valued.v (x * ϖ ^ k) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, hk, ← WithZero.exp_zsmul, ← WithZero.exp_add, WithZero.exp_eq_one]
    simp
  have hV : (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) (x * ϖ ^ k) = 1 := hVu ⟨x * ϖ ^ k, hy.le⟩ hy
  have hxe : x = (x * ϖ ^ k) * ϖ ^ (-k) := by
    rw [mul_assoc, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, mul_one]
  have e1 : (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) x = (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) (x * ϖ ^ k) * (IsDiscreteValuationRing.maximalIdeal
        (w.adicCompletionIntegers E)).valuation (w.adicCompletion E) ϖ ^ (-k) := by
    rw [← map_zpow₀, ← Valuation.map_mul, ← hxe]
  have e2 : Valued.v x = Valued.v (x * ϖ ^ k) * Valued.v ϖ ^ (-k) := by
    rw [← map_zpow₀, ← Valuation.map_mul, ← hxe]
  rw [e1, e2, hV, hVp, hy, hϖ]

private lemma isAdicComplete_maximalIdeal_adicCompletionIntegers (ϖ : w.adicCompletion E) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    IsAdicComplete (IsLocalRing.maximalIdeal (w.adicCompletionIntegers E))
      (w.adicCompletionIntegers E) := by
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ]
    exact ((withZero_lt_one_iff_le_exp_neg_one _).2 le_rfl).le
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  let p : w.adicCompletionIntegers E := ⟨ϖ, hϖ1⟩
  have hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := hϖ
  have hpow : ∀ (n : ℕ) (a : w.adicCompletionIntegers E),
      a ∈ (IsLocalRing.maximalIdeal (w.adicCompletionIntegers E)) ^ n ↔
        Valued.v (a : w.adicCompletion E) ≤ Valued.v ϖ ^ n := by
    intro n a
    rw [maximalIdeal_eq_span_of_valuation_eq_exp_neg_one w p hp, Ideal.span_singleton_pow, hϖ]
    exact mem_span_pow_iff_valuation_le_exp_neg_one_pow w p hp n a
  have hadic : IsAdic (IsLocalRing.maximalIdeal (w.adicCompletionIntegers E)) := by
    rw [isAdic_iff]
    constructor
    · intro n
      have hset : ((IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) ^ n : Ideal (w.adicCompletionIntegers E)) :
          Set (w.adicCompletionIntegers E)) =
          Subtype.val ⁻¹' {y : w.adicCompletion E |
            (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict y ≤
              (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict (ϖ ^ n)} := by
        ext a
        simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_ofPred_eq]
        rw [Valuation.restrict_le_iff, map_pow]
        exact hpow n a
      rw [hset]
      refine (Valued.isOpen_closedBall _ ?_).preimage continuous_subtype_val
      intro h0
      have h1 : Valued.v (ϖ ^ n) = 0 := by
        rw [← Valuation.embedding_restrict, h0, map_zero]
      exact pow_ne_zero n hϖ0 ((Valuation.zero_iff _).1 h1)
    · intro s hs
      obtain ⟨u, hu, hus⟩ := mem_nhds_subtype _ _ _ |>.1 hs
      rw [ZeroMemClass.coe_zero, Valued.mem_nhds_zero] at hu
      obtain ⟨γ, hγ⟩ := hu
      obtain ⟨n, hn⟩ := Valued.exists_pow_lt_of_le_exp_neg_one (R := w.adicCompletion E) hϖ.le
        (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
          (f := (.ofClass (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))))) γ)
      refine ⟨n, fun a ha => hus (hγ ?_)⟩
      show (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict
        (a : w.adicCompletion E) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding]
      exact lt_of_le_of_lt ((hpow n a).1 ha) (by simpa using hn)
  have hcl : IsClosed ((w.adicCompletionIntegers E : Set (w.adicCompletion E))) :=
    Valued.isClosed_valuationSubring _
  have : CompleteSpace (w.adicCompletionIntegers E) := hcl.completeSpace_coe
  exact hadic.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

private lemma neg_log_valuation_eq_ordL (x : w.adicCompletion E) : -WithZero.log (Valued.v x) = ordL x := by
  unfold ordL
  split_ifs with h
  · rw [h, WithZero.log_zero, neg_zero]
  · congr 1
    conv_lhs => rw [← WithZero.coe_unzero h]
    rfl

theorem exists_uq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∃ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) ∧ (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) ∧ (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) ∧ qV E w = K.q ^ 2 := by
  intro E _ _ _ hU w hw
  obtain ⟨-, hcc, hiso, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨-, ⟨ϖ, q, hUI, hq⟩, -, -⟩ := hns hw
  obtain ⟨-, -, -, hϖ, ⟨x₀, hx₀, hx₀'⟩, hq2, hcard⟩ := hUI
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hc : Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) = q ^ 2 := hcard
  have := isAdicComplete_maximalIdeal_adicCompletionIntegers w ϖ hϖ'
  have : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hc]
    exact pow_ne_zero 2 (by omega)
  have : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  let σ : w.adicCompletion E ≃+* w.adicCompletion E :=
    RingEquiv.ofRingHom (cj w) (cj w) (RingHom.ext hcc) (RingHom.ext hcc)
  have hx₀A : Valued.v x₀ ≤ 1 := hx₀
  have hσx₀ : Valued.v (σ x₀) ≤ 1 := by
    show Valued.v (cj w x₀) ≤ 1
    rw [hiso]
    exact hx₀A
  have hint : ∀ x : w.adicCompletionIntegers E, ∃ y : w.adicCompletionIntegers E,
      σ (algebraMap _ (w.adicCompletion E) x) = algebraMap _ (w.adicCompletion E) y := by
    intro x
    have hx : Valued.v (σ x) ≤ 1 := by
      show Valued.v (cj w x) ≤ 1
      rw [hiso]
      exact x.2
    exact ⟨⟨σ x, hx⟩, rfl⟩
  have hres : ∃ x y : w.adicCompletionIntegers E,
      σ (algebraMap _ (w.adicCompletion E) x) = algebraMap _ (w.adicCompletion E) y ∧
        x - y ∉ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) := by
    refine ⟨⟨x₀, hx₀A⟩, ⟨σ x₀, hσx₀⟩, rfl, fun hm => ?_⟩
    have h1 := (mem_max_iff w _).1 hm
    have h2 : Valued.v (x₀ - σ x₀) = 1 := by
      rw [Valuation.map_sub_swap]
      exact hx₀'
    push_cast at h1
    rw [h2] at h1
    exact lt_irrefl _ h1
  let K : GlobalTheory.UnitLemma.UQ :=
    { O := w.adicCompletionIntegers E
      E := w.adicCompletion E
      c := σ
      c_c := hcc
      c_int := hint
      c_res := hres
      q := q
      card_res := hc }
  refine ⟨K, RingEquiv.refl _, fun x => rfl, ?_, ?_, hq⟩
  · intro x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro h
      exact ⟨⟨x, h⟩, rfl⟩
  · intro x
    show -WithZero.log ((IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) x) = ordL x
    rw [valuation_max_eq w ϖ hϖ' x]
    exact neg_log_valuation_eq_ordL w x

end GlobalTheory.InertUQ
