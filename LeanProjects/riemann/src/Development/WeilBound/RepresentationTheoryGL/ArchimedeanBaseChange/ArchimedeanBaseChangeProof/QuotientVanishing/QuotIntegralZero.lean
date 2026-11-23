import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.D4

open PositivityTheory.Rg.BcB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

structure IsTest2J (φ : GA E a × GA E b → ℂ) (r : ℝ) : Prop extends IsTest2 φ r where
  level : ∃ (U₁ : Subgroup (GL (Fin a) (Af E))) (U₂ : Subgroup (GL (Fin b) (Af E))), IsOpen (U₁ : Set (GL (Fin a) (Af E))) ∧
    IsOpen (U₂ : Set (GL (Fin b) (Af E))) ∧ ∀ u₁ ∈ U₁, ∀ u₂ ∈ U₂, ∀ g,
      φ (finGL E a u₁ * g.1, finGL E b u₂ * g.2) = φ g ∧ φ (g.1 * finGL E a u₁, g.2 * finGL E b u₂) = φ g

def cutTerm2 [MeasurableSpace (GA E a)] [MeasurableSpace (GA E b)] (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (τ : ℝ)
    (φ : GA E a × GA E b → ℂ) (d₁ : GL (Fin a) E) (d₂ : GL (Fin b) E) : ℂ :=
  quotIntegral (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂)) Measure.count fun x =>
    chiT τ x.1 * chiT τ x.2 * φ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂))

def Unfold2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) [MeasurableSpace (GA E a)]
  [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)] (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure]
  (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure] (F₁ : Set (GA E a)) (F₂ : Set (GA E b)) (τ r : ℝ) (φ : GA E a × GA E b → ℂ),
    IsFundamentalDomain (ratGL E a).range F₁ μ₁ → IsFundamentalDomain (ratGL E b).range F₂ μ₂ → IsTest2J φ r →
    (Function.support fun c : TwClass E a × TwClass E b => cutTerm2 μ₁ μ₂ τ φ (Quot.out c.1) (Quot.out c.2)).Finite ∧
      cutTr2 μ₁ μ₂ F₁ F₂ τ φ = ∑ᶠ c : TwClass E a × TwClass E b, cutTerm2 μ₁ μ₂ τ φ (Quot.out c.1) (Quot.out c.2)

def SliceTerm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) [MeasurableSpace (GA E a)]
  [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)] (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure]
  (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure] (τ r : ℝ) (φ : GA E a × GA E b → ℂ) (d₁ : GL (Fin a) E) (d₂ : GL (Fin b) E),
    IsTest2J φ r →
    cutTerm2 μ₁ μ₂ τ φ d₁ d₂ = quotIntegral μ₂ (ratCent d₂) Measure.count (fun y =>
        chiT τ y * cutTerm μ₁ τ (fun g => φ (g, twConj (thetaA E b) y (ratGL E b d₂))) d₁) ∧
      cutTerm2 μ₁ μ₂ τ φ d₁ d₂ = quotIntegral μ₁ (ratCent d₁) Measure.count (fun x =>
        chiT τ x * cutTerm μ₂ τ (fun g => φ (twConj (thetaA E a) x (ratGL E a d₁), g)) d₂)

def ClassVanish2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (a b : ℕ),
  ∃ C : ℝ, ∀ [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)]
    (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure] (τ r : ℝ) (φ : GA E a × GA E b → ℂ)
    (d₁ : GL (Fin a) E) (d₂ : GL (Fin b) E), IsTest2J φ r → C * (1 + r) ≤ τ → IsRegD d₁ → IsRegD d₂ →
    ¬ (IsRegEll d₁ ∧ IsRegEll d₂) → cutTerm2 μ₁ μ₂ τ φ d₁ d₂ = 0

def EllFormula2J : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (a b : ℕ),
  ∃ C : ℝ, 0 ≤ C ∧ ∀ [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)]
    (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure] (F₁ : Set (GA E a))
    (F₂ : Set (GA E b)) (τ r : ℝ) (φ : GA E a × GA E b → ℂ), IsFundamentalDomain (ratGL E a).range F₁ μ₁ →
    IsFundamentalDomain (ratGL E b).range F₂ μ₂ → IsTest2J φ r → 0 ≤ r → C * (1 + r) ≤ τ →
    cutTr2 μ₁ μ₂ F₁ F₂ τ φ = ellSum2 μ₁ μ₂ φ

theorem quotIntegral_zero {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (μH : Measure H) :
    quotIntegral μ H μH (fun _ => (0 : ℂ)) = 0 := by
  unfold quotIntegral; split_ifs <;> simp

theorem classVanish2_of (hS : SliceTerm) (hV : ClassVanish) (hZ : SizeBasic) : ClassVanish2 := by
  intro E _ _ _ _ a b
  obtain ⟨C₁, h₁⟩ := hV E a
  obtain ⟨C₂, h₂⟩ := hV E b
  refine ⟨max 0 (max C₁ C₂), fun μ₁ _ μ₂ _ τ r φ d₁ d₂ hφ hτ hd₁ hd₂ hne => ?_⟩
  by_cases hr : 0 ≤ 1 + r
  · have l₁ : C₁ * (1 + r) ≤ τ :=
      le_trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hr) hτ
    have l₂ : C₂ * (1 + r) ≤ τ :=
      le_trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hr) hτ
    by_cases he₁ : IsRegEll d₁
    · have he₂ : ¬ IsRegEll d₂ := fun h => hne ⟨he₁, h⟩
      rw [(hS E a b μ₁ μ₂ τ r φ d₁ d₂ hφ).2]
      have : ∀ x : GA E a, chiT τ x *
          cutTerm μ₂ τ (fun g => φ (twConj (thetaA E a) x (ratGL E a d₁), g)) d₂ = 0 := fun x => by
        rw [h₂ μ₂ τ r _ d₂ (hφ.test₂ _).1 (fun g hg => (hφ.size _ hg).2) (hφ.test₂ _).2.2 l₂ hd₂ he₂, mul_zero]
      simp only [this]
      exact quotIntegral_zero _ _ _
    · rw [(hS E a b μ₁ μ₂ τ r φ d₁ d₂ hφ).1]
      have : ∀ y : GA E b, chiT τ y *
          cutTerm μ₁ τ (fun g => φ (g, twConj (thetaA E b) y (ratGL E b d₂))) d₁ = 0 := fun y => by
        rw [h₁ μ₁ τ r _ d₁ (hφ.test₁ _).1 (fun g hg => (hφ.size _ hg).1) (hφ.test₁ _).2.2 l₁ hd₁ he₁, mul_zero]
      simp only [this]
      exact quotIntegral_zero _ _ _
  · have h0 : ∀ g, φ g = 0 := fun g => by
      by_contra h
      have := (hφ.size g h).1
      have := (hZ E a).2.1 g.1
      linarith
    have : (fun x : GA E a × GA E b => chiT τ x.1 * chiT τ x.2 *
        φ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂))) = fun _ => 0 := by
      funext x; rw [h0, mul_zero]
    rw [cutTerm2, this]
    exact quotIntegral_zero _ _ _

theorem ellFormula2_of (hU : Unfold2) (hE : EllTerm) (hV : ClassVanish2) (hS : SizeBasic) : EllFormula2J := by
  classical
  intro E _ _ _ _ a b
  obtain ⟨C₁, h₁⟩ := hE E a
  obtain ⟨C₂, h₂⟩ := hE E b
  obtain ⟨C₃, h₃⟩ := hV E a b
  refine ⟨max 0 (max C₁ (max C₂ C₃)), le_max_left _ _, fun μ₁ _ μ₂ _ F₁ F₂ τ r φ hF₁ hF₂ hφ hr0 hτ => ?_⟩
  have l₁ : C₁ ≤ max 0 (max C₁ (max C₂ C₃)) := (le_max_left _ _).trans (le_max_right _ _)
  have l₂ : C₂ ≤ max 0 (max C₁ (max C₂ C₃)) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have l₃ : C₃ ≤ max 0 (max C₁ (max C₂ C₃)) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h1r : (0 : ℝ) ≤ 1 + r := by linarith
  rw [(hU E a b μ₁ μ₂ F₁ F₂ τ r φ hF₁ hF₂ hφ).2, ellSum2]
  refine finsum_congr fun c => ?_
  by_cases he : IsRegEll (Quot.out c.1) ∧ IsRegEll (Quot.out c.2)
  · rw [finsum_eq_if, if_pos he, cutTerm2, orbTerm2]
    congr 1
    funext x
    by_cases h0 : φ (twConj (thetaA E a) x.1 (ratGL E a (Quot.out c.1)), twConj (thetaA E b) x.2 (ratGL E b (Quot.out c.2))) = 0
    · simp [h0]
    · have hs := hφ.size _ h0
      have hx₁ : x.1 ∈ cutSet E a τ := by
        refine h₁ τ x.1 _ he.1 (le_trans ?_ hτ)
        have a0 := (hS E a).2.1 (twConj (thetaA E a) x.1 (ratGL E a (Quot.out c.1)))
        exact mul_le_mul l₁ (by linarith [hs.1]) (by linarith) (le_max_left _ _)
      have hx₂ : x.2 ∈ cutSet E b τ := by
        refine h₂ τ x.2 _ he.2 (le_trans ?_ hτ)
        have a0 := (hS E b).2.1 (twConj (thetaA E b) x.2 (ratGL E b (Quot.out c.2)))
        exact mul_le_mul l₂ (by linarith [hs.2]) (by linarith) (le_max_left _ _)
      simp [chiT, hx₁, hx₂]
  · rw [finsum_eq_if, if_neg he]
    by_cases hd : IsRegD (Quot.out c.1) ∧ IsRegD (Quot.out c.2)
    · exact h₃ μ₁ μ₂ τ r φ _ _ hφ (le_trans (mul_le_mul_of_nonneg_right l₃ h1r) hτ) hd.1 hd.2 he
    · have : ∀ x : GA E a × GA E b, φ (twConj (thetaA E a) x.1 (ratGL E a (Quot.out c.1)),
          twConj (thetaA E b) x.2 (ratGL E b (Quot.out c.2))) = 0 := fun x => by
        by_contra h
        apply hd
        exact ⟨(hφ.test₁ _).2.1 _ x.1 h, (hφ.test₂ _).2.1 _ x.2 h⟩
      simp [cutTerm2, this, quotIntegral]

end PositivityTheory.Rg.BcB.D4

end
