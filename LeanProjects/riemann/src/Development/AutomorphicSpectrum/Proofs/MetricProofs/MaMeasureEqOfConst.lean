import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FixedMemberBase
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem maMeasure_eq_of_const {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X) (c : Fin e → ℝ)
    (h : ∀ i x y, (Ψ i).φ x y = (Φ i).φ x y + c i) : maMeasure A Ψ = maMeasure A Φ := by
  have hH : ∀ (F : (Fin e → ℂ) → ℝ) (a : ℝ) (y : Fin e → ℂ),
      hessC (fun z => F z + a) y = hessC F y := by
    intro F a y
    have h1 : fderiv ℝ (fun z => F z + a) = fderiv ℝ F := funext fun z => fderiv_add_const a
    unfold hessC
    rw [h1]
  have hD : ∀ j, locDens A Ψ j = locDens A Φ j := by
    intro j
    funext y
    unfold locDens maDens
    have hk : (fun k => hessC (fun y' => (Ψ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) =
        fun k => hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
      funext k
      simp only [h k]
      exact hH _ _ y
    rw [hk]
  unfold maMeasure
  simp only [hD]

theorem exists_pos_le_all {e : ℕ} (f : Fin e → ℝ) (hf : ∀ i, 0 < f i) (a : ℝ) (ha : 0 < a) :
    ∃ b : ℝ, 0 < b ∧ b ≤ a ∧ ∀ i, b ≤ f i := by
  have hne : (insert a (Finset.univ.image f)).Nonempty := Finset.insert_nonempty _ _
  refine ⟨_, (Finset.lt_min'_iff _ hne).2 fun x hx => ?_,
    Finset.min'_le _ _ (Finset.mem_insert_self _ _),
    fun i => Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ i)))⟩
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact ha
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hf i

theorem tail_uniform : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → ∃ K t₁ : ℝ, 0 < t₁ ∧ (0 < t₀ → t₁ ≤ t₀) ∧ ∀ τ : Fin e → ℝ, (∀ i, 0 < τ i ∧ τ i ≤ t₁) → (∀ i, IsPotential A (th i + LocPot.ofFun (phT i (τ i)) + Θ) ∧ IsPsh A (th i + LocPot.ofFun (phT i (τ i)) + Θ)) ∧ ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  intro hTB e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR
  choose t₂ ht₂ ht₂₀ hfix using fun i =>
    fixedMember_base A Θ L s (th i) (ph i) (phT i) C₅ C t₀ hΘ hpos hnorm (hW i) (hR i)
  obtain ⟨a, ha, hε⟩ := epsT_small C
  obtain ⟨t₁, ht₁, ht₁a, ht₁0, ht₁2⟩ : ∃ t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ a ∧ (0 < t₀ → t₁ ≤ t₀) ∧
      ∀ i, t₁ ≤ t₂ i := by
    obtain ⟨b, hb, hba, hbf⟩ := exists_pos_le_all t₂ ht₂ a ha
    by_cases h0 : 0 < t₀
    · exact ⟨min b t₀, lt_min hb h0, (min_le_left _ _).trans hba, fun _ => min_le_right _ _,
        fun i => (min_le_left _ _).trans (hbf i)⟩
    · exact ⟨b, hb, hba, fun h => absurd h h0, hbf⟩
  have hB := fun i => hfix i t₁ ht₁ (ht₁2 i)
  obtain ⟨Ct, hCt⟩ := hTB A (fun i => th i + LocPot.ofFun (phT i t₁) + Θ) L s m W
    (fun i => (hB i).1) (fun i => (hB i).2.2.1) hL hS hSNC hnorm
  have hC₁ : 0 ≤ |C₅| + |C| + 1 := by positivity
  refine ⟨Ct * (|C₅| + |C| + 1 + 3), t₁, ht₁, ht₁0, fun τ hτ => ⟨fun i => ?_, fun R hRe => ?_⟩⟩
  · have hτ0 : τ i ≤ t₀ := ((hτ i).2.trans (ht₁2 i)).trans (ht₂₀ i)
    obtain ⟨hsm, -, -, -, hpsh, -, -, -⟩ := (hR i).2.2 (τ i) (hτ i).1 hτ0
    have hth := (hW i).1
    have hεi := (abs_le.1 (hε (τ i) (hτ i).1 ((hτ i).2.trans ht₁a)).1).2
    refine ⟨isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ hsm)) hΘ,
      isPsh_of_le A Θ (th i) (phT i (τ i)) hΘ hpos hth hsm (epsT C (τ i)) 1 0 (by linarith) hpsh _
        (fun x z hz => ⟨hz.1.1, hz.2⟩) (fun x z => ?_)⟩
    show (th i).φ x z + phT i (τ i) z + Θ.φ x z = _
    ring
  · have hL' := fun i => (hB i).2.2.2 (τ i) (hτ i).1 (hτ i).2
    have hm : maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) =
        maMeasure A (fun i => (th i + LocPot.ofFun (phT i t₁) + Θ) +
          LocPot.ofFun (fun y => phT i (τ i) y - phT i t₁ y - C * epsT C t₁)) :=
      maMeasure_eq_of_const A _ _ (fun _ => C * epsT C t₁) fun i x y => by
        show (th i).φ x y + phT i (τ i) y + Θ.φ x y =
          (th i).φ x y + phT i t₁ y + Θ.φ x y +
            (phT i (τ i) y - phT i t₁ y - C * epsT C t₁) + C * epsT C t₁
        ring
    rw [hm]
    exact hCt (|C₅| + |C| + 1) (fun i y => phT i (τ i) y - phT i t₁ y - C * epsT C t₁) hC₁
      (fun i => (hL' i).1) (fun i => (hL' i).2.1)
      (fun i y hy => ⟨(hL' i).2.2.2 y hy, (hL' i).2.2.1 y⟩) R hRe

end GlobalTheory.CompanionTheory.Ar.Giv
